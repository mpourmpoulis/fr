/*@ predicate consecutive (integer n, integer i, integer best, int *x) =
  @   i+best <= n && (\forall integer k ; i <= k < i+best ==> x[i]==x[k]);
  @*/









/*@
  requires \valid_read(x + (0 .. N-1));
  requires N >= 1 ;
    
  assigns \nothing ;
  ensures 0 <= \result < N ;
  
  ensures \exists integer i ; consecutive(N,i,\result,x);
  ensures \forall integer i ; !consecutive(N,i,\result+1,x);
  

*/
int countSameConsecutive(int N, int x[]) {
	int best = 0, i = 0;
	/*@
    loop invariant 0<= i <= N ;
    loop invariant ( 0<i<N ) ==> x[i]    != x[i-1];
    loop invariant ( 0<=best<=i);
	loop invariant \exists integer b; b<=i-best && consecutive(N,b,best,x);
     
    loop assigns i,best ;
    loop variant N-i ;
  */
	while (i < N) {
	int j = i+1;

	/*@
    loop invariant i< j <= N ;
    loop invariant 
      \forall integer k ; i <= k < j ==> x[i]==x[k] ;
    loop assigns j ;
    loop variant N-j ;
  	*/
	while (j < N && x[j] == x[i]) ++j;
	if (j-i > best) best = j-i;
		i = j;
	}
	return best;
}
