#include <string.h>

int moore_majority(size_t size, int a[size])
{
    int el = a[0];
    size_t cnt = 0;

    for (size_t i = 0; i < size; i++) {
       if (cnt == 0) {
          el = a[i];
          cnt = 1;
       } else if (el == a[i]) {
          cnt++;
       } else cnt--;
    }

    return el;
}
