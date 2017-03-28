#include "crab_llvm/Analysis/AssumptionAnalysis.hpp"

#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include <crab/common/types.hpp>
#include <crab/common/debug.hpp>
#include <crab/common/stats.hpp>

#include <crab/cfg/cfg.hpp> 
#include <crab/iterators/killgen_fixpoint_iterator.hpp> 
#include <crab/domains/separate_domains.hpp>
#include <crab/analysis/graphs/cdg.hpp>

#include "crab_llvm/CfgBuilder.hh"
#include "crab_llvm/MemAnalysis.hh"
#include "crab_llvm/Support/NameValues.hh"

#include <boost/unordered_map.hpp>
#include <boost/range/iterator_range.hpp>
#include <boost/bimap.hpp>


/**
 *  Dataflow analysis that infers which unjustified assumptions must
 *  hold to prove an assertion.
 * 
 *  First, for each block b it computes facts <i,V> meaning that there
 *  exists a path emanating from b that will reach assertion with id=i
 *  and its evaluation depends on the set of variables V.
 * 
 *  Second, using this set of facts computed we map each assertion to
 *  the set of assumptions (i.e., conditions over other statements)
 *  that must hold in order to prove the assertion.
 *
 *  Notes:
 *  - Consider only integer instructions ignoring the heap.
 *  - The assumptions that consider are only whether add/mul/sub
 *    operations can overflow.
 **/

namespace crab_llvm {

     using namespace crab::iterators;
     using namespace crab::domains;
     using namespace crab::cfg;

     // A wrapper to an assert statement 
     template<typename CFG>
     struct assert_wrapper: public ikos::writeable {

       typedef typename statement_visitor<typename CFG::varname_t>::z_assert_t assert_t;
       typedef typename CFG::basic_block_label_t basic_block_label_t;
       typedef assert_wrapper<CFG> this_type;
       
       // unique identifier for the assert statement needed for being
       // used as key
       index_t id;
       // basic block where the assert statement is located
       basic_block_label_t bbl;
       // the assert statement
       assert_t* a;

       ///////
       /// pointers to some global datastructures
       typedef boost::unordered_map<assert_t*, this_type > assert_map_t;	        
       typedef boost::unordered_map <basic_block_label_t,
				     std::vector<basic_block_label_t> > cdg_t;
       assert_map_t* assert_map_ptr;              
       const cdg_t* cdg_ptr;
       ////////

       assert_wrapper (index_t _id, basic_block_label_t _bbl, assert_t* _a,
		       assert_map_t *am, const cdg_t *cdg)
	 : id (_id), bbl (_bbl), a(_a), assert_map_ptr(am), cdg_ptr (cdg) {}

       index_t index() const { return id;}
       bool operator==(this_type o) const { return id == o.id;}
       bool operator< (this_type o) const { return id < o.id; }       
       void write (crab::crab_os& o) { o << id; }
     };

     // Define the operations of the dataflow analysis
     template<class CFG>
     class assumption_analysis_ops:
       public killgen_operations_api<CFG,
		 separate_killgen_domain<assert_wrapper<CFG>,
					 flat_killgen_domain<typename CFG::varname_t> > > {
       
       typedef assert_wrapper<CFG> assert_wrapper_t;
       typedef flat_killgen_domain<typename CFG::varname_t> var_dom_t;      
       typedef separate_killgen_domain<assert_wrapper_t, var_dom_t> separate_killgen_domain_t;
       typedef killgen_operations_api<CFG, separate_killgen_domain_t> killgen_operations_api_t;
       
      public:

       typedef typename CFG::basic_block_label_t basic_block_label_t;
       typedef typename CFG::basic_block_t basic_block_t;
       typedef typename CFG::varname_t V;
       typedef ikos::z_number N;

       // map each stmt assertion to a unique identifier
       typedef typename assert_wrapper_t::assert_t assert_t; 
       typedef boost::unordered_map<assert_t*, assert_wrapper_t > assert_map_t;	 
       
       // control-dependency graph       
       // map a CFG block to the set of blocks which control-dependent on it.
       typedef boost::unordered_map <basic_block_label_t,
				     std::vector<basic_block_label_t> > cdg_t;
       
       // set of uses and definitions of an instruction
       typedef crab::cfg::Live<V> live_t;

       
       class transfer_function: public statement_visitor<V> {
	 
         typedef typename statement_visitor<V>::z_bin_op_t  bin_op_t;
         typedef typename statement_visitor<V>::z_assign_t  assign_t;
         typedef typename statement_visitor<V>::z_assume_t  assume_t;
         typedef typename statement_visitor<V>::z_select_t  select_t;
         typedef typename statement_visitor<V>::z_assert_t  assert_t;
         typedef typename statement_visitor<V>::havoc_t     havoc_t;
         typedef typename statement_visitor<V>::unreach_t   unreach_t;
	 
	 // Apply function F to each pair's value of the separate domain_t.
       	 template<typename F>
       	 struct apply_separate:
	   public std::unary_function<separate_killgen_domain_t, separate_killgen_domain_t>{
	   typedef apply_separate<F> this_type;
	   typedef std::binary_function<assert_wrapper_t, var_dom_t,
					std::pair<var_dom_t, bool> > function_type;
	   static_assert (std::is_base_of<function_type, F>::value,
			  "Function must be subclass of type F");

       	   F f; 

	 public:
	   
       	   apply_separate (F _f): f (_f) {}
	   apply_separate (const this_type& o): f (o.f) {}
	   
       	   separate_killgen_domain_t operator()(separate_killgen_domain_t inv)
       	   { // XXX: separate_killgen_domain_t cannot be modified in-place
	     typedef std::pair<typename separate_killgen_domain_t::key_type,
			       typename separate_killgen_domain_t::value_type> value_type;     

	     if (inv.is_bottom ()) return inv;
	     
       	     std::vector<value_type> kvs;
       	     kvs.reserve (std::distance (inv.begin(), inv.end ()));
       	     for (auto const &kv: inv)
       	       kvs.push_back (value_type(kv.first, kv.second));

       	     for (auto &kv: kvs) {
       	       auto p = f(kv.first, kv.second);
       	       if (p.second) inv.set (kv.first, p.first);
       	     }
       	     return inv;
       	   }
	   
       	 };

	 // Function to add data-dependencies
       	 class add_data_deps:
       	   public std::binary_function<assert_wrapper_t, var_dom_t, std::pair<var_dom_t,bool> >
       	 {
	   var_dom_t uses;
	   var_dom_t defs;

	 public:
	   
       	   add_data_deps (const live_t& l)
	     : uses(var_dom_t::bottom()), defs (var_dom_t::bottom()) {
	     for (auto v: boost::make_iterator_range(l.uses_begin(), l.uses_end()))
	       uses += v;
	     for (auto v: boost::make_iterator_range(l.defs_begin(), l.defs_end()))
	       defs += v;
	   }

	   add_data_deps (const add_data_deps &o): uses (o.uses), defs (o.defs) {}
	   
       	   std::pair<var_dom_t,bool> operator()(assert_wrapper_t /*w*/,var_dom_t d) {
       	     bool change = false;
	     
	     if (defs.is_bottom() && !uses.is_bottom() &&
		 !(uses & d).is_bottom ()) {
	       d += uses;
	       change = true;
	     }	       

       	     if (!(d & defs).is_bottom()) {
       	       d -= defs;
	       d += uses;
       	       change = true;
       	     }
	     
       	     return std::make_pair(d, change);
       	   }
       	 };

	 // Function to add control-dependencies
       	 class add_control_deps:
       	   public std::binary_function<assert_wrapper_t, var_dom_t, std::pair<var_dom_t,bool> >
       	 {
	   var_dom_t uses;
	   const std::vector<basic_block_label_t> &cdeps;
	   
	 public:
	   
       	   add_control_deps (const live_t& l, const std::vector<basic_block_label_t>& deps)
	     : uses(var_dom_t::bottom()), cdeps (deps) {
	     for (auto v: boost::make_iterator_range(l.uses_begin(), l.uses_end()))
	       uses += v;
	   }

	   add_control_deps (const add_data_deps &o): uses (o.uses), cdeps (o.cdeps) {}
	   
       	   std::pair<var_dom_t,bool> operator()(assert_wrapper_t w, var_dom_t d) {
       	     bool change = false;

	     if (std::find (cdeps.begin (), cdeps.end (), w.bbl) != cdeps.end ()) {
	       d += uses;
	       change = true;
	     }	       

       	     return std::make_pair(d, change);
       	   }
       	 };

	 // Function to remove data-dependencies
       	 class remove_deps:
       	   public std::binary_function<assert_wrapper_t, var_dom_t, std::pair<var_dom_t,bool> > {
	   
	   var_dom_t vars; 
	   
	 public:
	   
       	   remove_deps (V v): vars(var_dom_t::bottom()) { vars += v; }
	   
	   remove_deps (const std::vector<V> &vs)
	     : vars(var_dom_t::bottom()) { for (auto v: vs) {vars += v; } }

	   remove_deps (const remove_deps& o): vars (o.vars) {}
	   
       	   std::pair<var_dom_t,bool> operator()(assert_wrapper_t /*w*/, var_dom_t d) {
       	     bool change = false;
       	     if (!(d & vars).is_bottom()) {
       	       d -= vars;
       	       change = true;
       	     }
       	     return std::make_pair(d, change);
       	   }
       	 };

	 typedef apply_separate<add_data_deps> apply_add_data_t;
	 typedef apply_separate<add_control_deps> apply_add_control_t;	 
	 typedef apply_separate<remove_deps> apply_remove_t;
	 
	 // dataflow solution: map blocks to pairs of assertion id and
	 //                    set of variables.
         separate_killgen_domain_t _inv;
	 // map each assertion to a unique identifier
	 assert_map_t &_assert_map;
	 // control-dependence graph
	 const cdg_t &_cdg;
	 // parent basic block (XXX: needed because crab statements do
	 // not have a back pointer to their basic blocks)
	 basic_block_t &_bb;
	 
       public:
	 

         transfer_function (separate_killgen_domain_t inv,
			    const cdg_t &g, assert_map_t &am, basic_block_t &bb)
	   : _inv(inv), _cdg (g), _assert_map (am), _bb (bb) { }

	 separate_killgen_domain_t inv () {return _inv;}
	 
         void visit(bin_op_t &s){
	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n"
	 	                  << "\tBEFORE: " << _inv << "\n");
       	   apply_add_data_t f (add_data_deps (s.get_live ()));
       	   _inv = f (_inv);
	   CRAB_LOG("aa-step",
		    crab::outs () << "\tAFTER " << _inv << "\n";);
       	 }
         
         void visit(assign_t &s) {
	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n"
	 	                  << "\tBEFORE: " << _inv << "\n");	   
       	   apply_add_data_t f (add_data_deps (s.get_live ()));
       	   _inv = f (_inv);
	   CRAB_LOG("aa-step",
		    crab::outs () << "\tAFTER " << _inv << "\n";);
	   
         }
         
         void visit(assume_t &s) {
	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n"
	 	                  << "\tBEFORE: " << _inv << "\n");	   
	   // XXX: add data dependencies
       	   apply_add_data_t df (add_data_deps (s.get_live ()));
       	   _inv = df (_inv);
	   CRAB_LOG("aa-step",
		    crab::outs () << "\tAFTER data-dep " << _inv << "\n";);

	   // XXX: add control dependencies
	   // In the way LLVM programs are compiled, "assume"
	   // statements are located in the successors of the blocks
	   // where the original if-then-else was located.
	   for (auto const &pred: boost::make_iterator_range(_bb.prev_blocks ())) {
	     auto it = _cdg.find (/*_bb*/ pred);
	     if (it != _cdg.end ()) {
	       apply_add_control_t cf (add_control_deps (s.get_live (), it->second));
	       _inv = cf (_inv);
	       CRAB_LOG("aa-step",
			crab::outs () << "\tAFTER control-dep " << _inv << "\n";);
	     }
	   }

         }

         void visit(select_t &s) {
	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n"
	 	                  << "\tBEFORE: " << _inv << "\n");	   
       	   apply_add_data_t f (add_data_deps (s.get_live ()));
       	   _inv = f (_inv);
	   CRAB_LOG("aa-step",
		    crab::outs () << "\tAFTER " << _inv << "\n";);	   
         }
	 
         void visit(assert_t &s) {
	   auto it = _assert_map.find (&s);
	   if (it != _assert_map.end ()) return;
	     
	   var_dom_t vdom = var_dom_t::bottom ();
	   auto const& l = s.get_live ();
	   for (auto v: boost::make_iterator_range(l.uses_begin(), l.uses_end())) {
	     vdom += v;
	   } 

	   unsigned id = _assert_map.size ();
	   assert_wrapper_t val(id, _bb.label(), &s, &_assert_map, &_cdg);
	   _assert_map.insert (typename assert_map_t::value_type (&s, val));

	   _inv.set (val, vdom);

	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n" << "\tAdded " << vdom << "\n";);
	   
       	 }
	 
         void visit(unreach_t&) {
	   _inv = separate_killgen_domain_t::bottom();
	 }
	 
         void visit(havoc_t& s) {
	   CRAB_LOG("aa-step",
		    crab::outs () << "*** " << s << "\n"
	 	                  << "\tBEFORE: " << _inv << "\n");	   	   
       	   apply_remove_t f (remove_deps (s.variable ()));
       	   _inv = f (_inv);
	   CRAB_LOG("aa-step",
		    crab::outs () << "\tAFTER " << _inv << "\n";);	   
	 }

       };

      private:
       
       // global datastructure for the whole analysis of the CFG
       assert_map_t _assert_map;
       cdg_t _cdg;
       
      public:
       
       assumption_analysis_ops (CFG cfg)
	 : killgen_operations_api_t(cfg) { }
	 
       virtual bool is_forward() override { return false;}
       
       virtual std::string name () override { return "aa";}

       virtual void init_fixpoint() override {
	 crab::analyzer::graph_algo::control_dep_graph (this->_cfg, _cdg);
       }

       virtual separate_killgen_domain_t
       entry() override {
	 return separate_killgen_domain_t::bottom();
       }
       
       virtual separate_killgen_domain_t
       merge(separate_killgen_domain_t d1, separate_killgen_domain_t d2)  override {
	 return d1 | d2;
       }
              
       virtual separate_killgen_domain_t
       analyze (basic_block_label_t bb_id, separate_killgen_domain_t out) override {
         auto &bb = this->_cfg.get_node(bb_id);
         transfer_function vis(out,_cdg, _assert_map, bb);
	 for (auto &s: boost::make_iterator_range(bb.rbegin(),bb.rend())) {
	   s.accept (&vis);
	 }
         return vis.inv();
       }
     };

     // -- The analysis implementation
     template<class CFG>
     class assumption_analysis_impl:
       public boost::noncopyable, 
       public crab::iterators::killgen_fixpoint_iterator<CFG, assumption_analysis_ops<CFG> >{
       
      public:

       typedef typename CFG::basic_block_label_t basic_block_label_t;
       typedef typename CFG::varname_t varname_t;
       
      private:

       typedef crab::iterators::killgen_fixpoint_iterator<CFG, assumption_analysis_ops<CFG> > 
       kg_fixpo_iter_t;
       typedef assert_map<CFG> assert_map_t;
       
     public:
       
       typedef typename assert_map_t::iterator iterator;
       typedef typename assert_map_t::const_iterator const_iterator;
       
     private:
       
       // map each assertion to a vector of assumptions (i.e.,
       // conditions over other statements) that were assumed.
       assert_map_t _m;

      public:
       
       assumption_analysis_impl(CFG cfg) : kg_fixpo_iter_t(cfg) {}

       void exec() {
	 /// run the dataflow analysis:
	 //  compute for each basic block b a set of facts (i,V) such
	 //  that there exists a path from b that will check assertion
	 //  i and its evaluation depends on the set of variables V
	 
         this->run();

	 /// ASSUME: we are only interested in arithmetic operations that
	 /// can overflow.
	 /// TODO: cover select/assume with conditions that can overflow
	 /// 
	 /// If a block b has a statement of interest then
	 /// 1) Get the facts (invariants) that hold at the exit of b
	 /// 2) Propagate backwards the facts until a statement s of
	 ///    interest is found.
	 /// 3) record the assumption with the corresponding assertion.

	 //unsigned num_checked_statements = 0;
	 
	 for (auto &bb: boost::make_iterator_range(this->_cfg.begin(), this->_cfg.end())) {

	   // find out if the block is of interest
	   bool op_with_overflow = false;
	   
	   for (auto &s: bb) {
	     if (!s.is_bin_op ()) continue;
	     
	     auto bin_op_s = static_cast<const typename CFG::basic_block_t::z_bin_op_t*> (&s);
	     if (bin_op_s->op () == crab::BINOP_ADD ||
		 bin_op_s->op () == crab::BINOP_SUB ||
		 bin_op_s->op () == crab::BINOP_MUL)
	       op_with_overflow = true;
	   }
	   
	   if (op_with_overflow) {
	     auto out = this->_out_map [bb.label()];

	     CRAB_LOG("aa",
		      crab::outs () << "Basic block    : " << bb.label ()->getName () << "\n";
		      crab::outs () << "OUT invariants : " << out << "\n";);
	     
	     if (!out.is_bottom ()) {
	       // we just want to get the assert_map and cdg which are
	       // shared by all the entries in out so we extract them
	       // from the first entry.
	       auto kv = *(out.begin ());
	       typename assumption_analysis_ops<CFG>::transfer_function
		 vis(out, *(kv.first.cdg_ptr), *(kv.first.assert_map_ptr), bb);
	       for (auto &s: boost::make_iterator_range(bb.rbegin(),bb.rend())) {
		 // first propagate backwards the facts
		 s.accept (&vis);
		 // in contains the invariant that holds at the pre-state of s
		 auto in = vis.inv ();
		 
		 if (s.is_bin_op ()) {
		   auto bin_op_s= static_cast<const typename CFG::basic_block_t::z_bin_op_t*>(&s);
		   if (bin_op_s->op () == crab::BINOP_ADD ||
		       bin_op_s->op () == crab::BINOP_SUB ||
		       bin_op_s->op () == crab::BINOP_MUL) {

		     //num_checked_statements++;
		     
		     CRAB_LOG("aa",
			      crab::outs () << "Check s = " << s << "\n";
			      crab::outs () << "IN(s)   = " << in << "\n";);
		     
		     auto as = boost::make_shared<overflow_assumption<CFG> > (&s);
		     // traverse all pairs (i,V) where i is the id for
		     // the assertion and V is the variables computed
		     // by the dataflow analysis. If V intersect with
		     // the variables on the rhs of the arithmetic
		     // operation then we assume an assumption to the
		     // assertion.
		     for (auto kv: boost::make_iterator_range (in.begin(), in.end ())) {
		       auto vars = kv.second;
		       if (!(vars & as->get_vars ()).is_bottom ()) {
			 auto it = _m.find (kv.first.a);
			 if (it != _m.end ()) {
			   it->second.push_back (as);
			 } else {
			   vector<assumption_ptr<CFG> > ass = {as} ;
			   _m.insert (std::make_pair (kv.first.a, ass));
			 }
		       }
		     }
		   }
		 }
	       }
	     }
	   }
	 }
	 
         this->release_memory();
       }
       
       iterator begin () { return _m.begin ();}
       iterator end () { return _m.end ();}
       const_iterator begin () const { return _m.begin ();}
       const_iterator end () const { return _m.end ();}
       
     };


     ////////////////////////////////////
  
     template<class CFG>
     assumption_analysis<CFG>::assumption_analysis(CFG cfg)  
       : _impl(new assumption_analysis_impl<CFG> (cfg)) {}
	       

     template<class CFG>
     assumption_analysis<CFG>::~assumption_analysis() {
       if (_impl) delete _impl;
     }
  
     template<class CFG>
     void assumption_analysis<CFG>::exec() {
       _impl->exec ();
     }

     template<class CFG>
     typename assumption_analysis<CFG>::iterator assumption_analysis<CFG>::
     begin () { return _impl->begin();}
     template<class CFG>
     typename assumption_analysis<CFG>::iterator assumption_analysis<CFG>::
     end () { return _impl->end();}
     template<class CFG>
     typename assumption_analysis<CFG>::const_iterator assumption_analysis<CFG>::
     begin () const { return _impl->begin();}
     template<class CFG>
     typename assumption_analysis<CFG>::const_iterator assumption_analysis<CFG>::
     end () const { return _impl->end();}

     // specialization
     template class assumption_analysis<crab::cfg_impl::cfg_ref_t>;


     // LLVM pass
     bool AssumptionAnalysisPass::runOnModule (llvm::Module& M) {
       bool change=false;
       for (auto &F : M) {
	 change |= runOnFunction (F); 
       }
       return change;
     }
  
     bool AssumptionAnalysisPass::runOnFunction (llvm::Function& F) {
       // -- skip functions without a body
       if (F.isDeclaration () || F.empty ()) return false;
       // -- skip variadic functions
       if (F.isVarArg ()) return false;

       // -- build cfg
       VariableFactory vfac;
       tracked_precision tracklev = INT;
       DummyMemAnalysis mem; 
       CfgBuilder B (F, vfac, mem, tracklev, true,
		     &getAnalysis<TargetLibraryInfo>());
       auto cfg_ptr = B.getCfg ();

       crab::outs () << "Running assumption analysis .. \n";
       assumption_analysis<cfg_ref_t>  aa (*cfg_ptr);
       aa.exec ();
       { // Collect stats from the assumption analysis
	 unsigned num_assertions = 0;
	 unsigned num_assumptions = 0;
	 unsigned num_max_assum_per_assertion = 0;
	 for (auto &kv : boost::make_iterator_range(aa.begin(), aa.end())) {
	   crab::outs () << *(kv.first) << " verified\n";
	   num_assertions++;
	   unsigned k = 0;
	   for (auto as: kv.second) {
	     crab::outs () << "\t";
	     as->write (crab::outs ());
	     k++;
	     crab::outs () << "\n";
	   }
	   num_assumptions += k;
	   if (k > num_max_assum_per_assertion)
	     num_max_assum_per_assertion = k;
	   crab::outs () << "\n";
	 }
	 crab::outs () << "BRUNCH_STAT Number of Assertions "
		       << num_assertions << "\n";
	 // crab::outs () << "BRUNCH_STAT Number of Assumptions "
	 // 		  << num_checked_statements << "\n";
	 if (num_assertions > 0) {
	   float avg = (float) num_assumptions / (float) num_assertions;
	   crab::outs () << "BRUNCH_STAT Avg Number of Assumptions per Assertion "
			 << avg << "\n";
	 }
	 crab::outs () << "BRUNCH_STAT Max Number of Assumptions per Assertion "
		       << num_max_assum_per_assertion << "\n";
       }
       
       return false;
     }
  
     void AssumptionAnalysisPass::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
       AU.setPreservesAll ();
       
       AU.addRequired<llvm::DataLayoutPass>();
       AU.addRequired<llvm::TargetLibraryInfo>();
       AU.addRequired<llvm::UnifyFunctionExitNodes> ();
       AU.addRequired<crab_llvm::NameValues>();
     }

     char AssumptionAnalysisPass::ID = 0;
  
     llvm::Pass* createAssumptionAnalysisPass ()
     { return new AssumptionAnalysisPass (); }
  
} // end namespace

