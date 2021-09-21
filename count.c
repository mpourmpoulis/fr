/*@
  requires \valid_read(x + (0 .. N-1));
  requires N >= 0 ;
    
  assigns best,i ;
  ensures 0 <= \result < N ;
  
  ensures \exists integer i ; \forall integer j; 0 <= j < \result ==>  x[i+j] == x[i] ;
  ensures \forall integer i ; 0<= i<N-\result ==> x[i+\result] != x[i] ;

*/
int countSameConsecutive(int N, int x[]) {
	int best = 0, i = 0;
	while (i < N) {
	int j = i+1;
	while (j < N && x[j] == x[i]) ++j;
	if (j-i > best) best = j-i;
		i = j;
	}
	return best;
}
