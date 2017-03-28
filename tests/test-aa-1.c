extern int nd ();
extern void __CRAB_assert(int);

int main ()
{
  int i;
  int n = nd ();
  int x = 1;
  int y = 0;
  int z = 0;
  for (i=0;i<n;i++)
  {
    if (nd ()) {
      x = x+y;
      //y = y+z;
      y++;
      if (x>0) {
	if (nd () /*y>0*/) {
	  __CRAB_assert (0);
	}
      }
    }
    i++;
    z++;
  }

  __CRAB_assert(x >= y);
  __CRAB_assert(z >=0);
  return x+y;
}
