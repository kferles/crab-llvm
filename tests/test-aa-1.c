extern int nd ();
extern void __CRAB_assert(int);

int main ()
{
  int i;
  int n = nd ();
  int x = 1;
  int y = 0;
  int z = 0;
  int h = 0;
  for (i=0;i<n;i++)
  {
    if (nd ()) {
      x = x+y; 
      y++;  
      if (x>0) {
	h++;
	if (nd () /*y>0*/) {
	  __CRAB_assert (/*z > 0*/0);
	}
      }
    }
    z++;  
  }

  __CRAB_assert(x >= y);
  __CRAB_assert(z >=0);
  return x+y;
}

/*
   assert (0) verified 
       i++
       x=x+y
       y++
   assert (x >= y) verified
       x=x+y
       y++
   assert (z >= 0) verified 
       z++
 */ 
