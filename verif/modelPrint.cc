
#include <stdio.h>
#include <stdarg.h>

#include "modelPrint.h"

void modelPrint(
  PrintLevel level,
  unsigned int t, // time
  char * modelinfo,
  char const * msg, ...
) {
  const char * levels[] = {"ERROR", "WARNING", "NOTE"};

  printf("%s:t%d:%s: ", levels[level], t-1, modelinfo);

  va_list vargs;
  va_start(vargs, msg);
  vprintf(msg, vargs);
  va_end(vargs);

  printf("\n");
  return;
}

