#ifndef ASSUMPTION_ANALYSIS_HPP__
#define ASSUMPTION_ANALYSIS_HPP__

#include "crab_llvm/config.h"

#include <crab/cfg/cfg.hpp>
#include <crab/iterators/killgen_fixpoint_iterator.hpp> 

#include <boost/range/iterator_range.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/unordered_map.hpp>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"


/**
 *  Dataflow analysis that infers which unjustified assumptions must
 *  hold to prove an assertion.
 **/

namespace crab_llvm {

     using namespace crab::iterators;
     using namespace crab::domains;
     using namespace crab::cfg;

     // A class to represent an unjustified assumption in tthe
     // analysis
     template<class CFG>
     class assumption {

     public:
       typedef flat_killgen_domain<typename CFG::varname_t> var_dom_t;
       typedef typename CFG::basic_block_t::statement_t statement_t;

     protected:
       // statement where the unsound assumption was assumed.
       const statement_t * _s;       
       // a subset of s' variables on which the unsound assumption was assumed.
       var_dom_t _vars;
       
     public:
       
       assumption(const statement_t *s, var_dom_t vars):
	 _s(s), _vars (vars) { }

       var_dom_t get_vars () const { return _vars; }
       
       virtual void write(crab::crab_os& o) = 0;
       
       virtual ~assumption() {}
     };

     // Subclass of assumption for arithmetic overflow
     template<class CFG>
     class overflow_assumption: public assumption<CFG> {

     public:
       
       typedef assumption<CFG> base_type;
       typedef overflow_assumption<CFG> this_type;
       
       typedef typename base_type::var_dom_t var_dom_t;
       typedef typename base_type::statement_t statement_t;

     private:

       var_dom_t _get_vars (const statement_t *s) const {
	 assert (s->op () == crab::BINOP_ADD ||
		 s->op () == crab::BINOP_SUB ||
		 s->op () == crab::BINOP_MUL);
	 
	 var_dom_t vars;
	 auto lvars = s->get_live ();
	 for (auto v: boost::make_iterator_range(lvars.uses_begin(),
						 lvars.uses_end())) {
	   vars += v;
	 }
	 return vars;
       }
       
     public:
       
       overflow_assumption (const statement_t *s)
	 : base_type (s, _get_vars (s)) { }
       
       virtual void write (crab::crab_os& o) override {
	 o << *(this->_s) << " ===> "
	   << "DoesNotOverflow(" << this->_vars << ")";
       }
     };

     // Types for the analysis output
     template <typename CFG>
     using assumption_ptr = boost::shared_ptr<assumption<CFG> >;
  
     template <typename CFG>
     using assert_map =
	  boost::unordered_map
	     <typename statement_visitor<typename CFG::varname_t>::z_assert_t*,
	      std::vector<assumption_ptr <CFG> > >;

     // forward declaration
     template<typename CFG>
     class assumption_analysis_impl;
  
     // -- The analysis
     template<class CFG>
     class assumption_analysis {

       assumption_analysis_impl<CFG> *_impl;
       
     public:
       
       typedef typename assert_map<CFG>::iterator iterator;
       typedef typename assert_map<CFG>::const_iterator const_iterator;       
       
       assumption_analysis(CFG cfg);

       ~assumption_analysis();
       
       void exec();
       
       void write (ostream &o) const {}
       
       iterator begin ();
       iterator end ();
       const_iterator begin () const;
       const_iterator end () const;
       
     };

  class AssumptionAnalysisPass: public llvm::ModulePass {
  public:
    static char ID;
    AssumptionAnalysisPass (): llvm::ModulePass (ID) {}
    virtual bool runOnModule (llvm::Module& M);
    virtual bool runOnFunction (llvm::Function& F);    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const ;
    virtual const char* getPassName () const {return "AssumptionAnalysis";}
  };

  extern llvm::Pass* createAssumptionAnalysisPass ();
  
} // end namespace
#endif 
