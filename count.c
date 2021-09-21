/*@ predicate consecutive (integer n, integer i, integer best, int *x) =
  @   i>=0 && i+best <= n && (\forall integer k ; i <= k < i+best ==> x[i]==x[k]);
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
	loop invariant \exists integer b; 0<=b<=i && consecutive(N,b,best,x);
	loop invariant \forall integer b; (0<=b<=i  && best>0) ==> !consecutive(N,b,best+1,x);
     
    loop assigns i,best ;
    loop variant N-i ;
  */
	while (i < N) {
	int j = i+1;

	/*@
    loop invariant i+1<= j <= N ;
    loop invariant consecutive(N,i,j-i,x);
    loop invariant !consecutive(N,i-1,j-i+1,x);
    loop assigns j ;
    loop variant N-j ;
  	*/
	while (j < N && x[j] == x[i]) ++j;
	if (j-i > best) best = j-i;
		i = j;
	}
	return best;
}
