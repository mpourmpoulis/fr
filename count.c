/*@ predicate consecutive (integer i, integer j, int *x) =
  @    j>=i>=0 && (\forall integer k ; i <= k < j ==> x[i]==x[k]);
  @*/


/*@ predicate consecutive_best (integer n, integer b, int *x) =
  @    (\exists integer i,j; 0<=i<=j<=n && j-i==b && consecutive(i,j,x))
  		&& (\forall integer i,j; (0<=i<=j<=n && consecutive(i,j,x)) ==> j-i<=b);
  @*/



/*@
  requires \valid_read(x + (0 .. N-1));
  requires N >= 1 ;
    
  assigns \nothing ;
  ensures 0 <= \result <= N ;
  
  ensures consecutive_best(N,\result,x);
  

*/
int countSameConsecutive(int N, int x[]) {
	int best = 0, i = 0;
	/*@
    loop invariant 0<= i <= N ;
    loop invariant ( 0<i<N ) ==> x[i]    != x[i-1];
    loop invariant ( 0<=best<=i);
    loop invariant consecutive_best(i,best,x);
     
    loop assigns i,best ;
    loop variant N-i ;
  */
	while (i < N) {
		int j = i+1;
	
		/*@
	    loop invariant i+1<= j <= N ;
	    loop invariant consecutive(i,j,x);
	    loop invariant (j<N && x[i] != x[j]) ==> x[j] != x[j-1];
	    loop invariant (j<N && x[i] == x[j]) ==> x[j] == x[j-1];
	    loop assigns j ;
	    loop variant N-j ;
	  	*/
		while (j < N && x[j] == x[i]) ++j;
		if (j-i > best) best = j-i;
		i = j;
	}
	return best;
}

