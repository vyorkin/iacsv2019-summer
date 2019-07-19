/*@ requires \valid(a + (0..n-1));
    requires \forall integer i, integer j; 0 <= i < j < n ==> a[i] <= a[j];
    assigns \nothing;
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] < val;
    ensures \forall integer k; \result <= k < n ==> val <= a[k];
*/
unsigned lower_bound(const int *a, unsigned n, int val)
{
   unsigned left = 0;
   unsigned right = n;
   unsigned middle = 0;

   /*@ loop invariant 0 <= left <= right <= n;
       loop assigns middle, left, right;
       loop invariant \forall integer i; 0 <= i < left ==> a[i] < val;
       loop invariant \forall integer i; right <= i < n ==> val <= a[i];
       loop variant right - left;
   */
   while (left < right) {
      middle = left + (right - left) / 2;
      if (a[middle] < val) {
         //@ assert \forall integer i; 0 <= i < middle+1 ==> a[i] < val;
         left = middle + 1;
      } else right = middle;
   }

   return left;
}
