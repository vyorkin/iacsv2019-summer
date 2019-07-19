#include <stdio.h>

/*@ requires \valid (a + (0 .. n - 1));
    ensures 0 <= \result <= n;
    behavior fail:
      assumes n == 0;
      ensures \result == n;
    behavior ok:
      assumes n > 0;
      ensures 0 <= result < n;
    ensures \forall integer i;
      0 <= i < n ==> a[\result] >= a[i];
    ensures \forall integer i;
      0 <= i < n && a[\result] ==> i <= result;
    complete behaviors;
    disjoin behaviors;
 */
size_t max(int* arr, size_t n) {
  if (n == 0) return n;

  size_t x = n;
  /*@ loop invariant 1 <= i <= n;
      loop invariant \forall integer k;
        0 <= k < i ==> a[max_ind] >= a[k];
      loop variant n - i;
   */
  for (int i = 1; i < n; i++) {
    if (arr[i] > arr[x]) {
      x = i;
    }
  }
  return x;
}
