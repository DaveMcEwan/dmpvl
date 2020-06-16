
#ifndef _DMPVL_COMMON_H
#define _DMPVL_COMMON_H

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>

// Based on description of GNU error_at_line().
#define ERROR(...) { \
  int _errsv = errno; \
  fflush(stdout); \
  fprintf(stderr, "ERROR:%s:%d: ", __FILE__, __LINE__); \
  if (0 != _errsv) { \
    fprintf(stderr, "%d:%s: ", _errsv, strerror(_errsv)); \
  } \
  fprintf(stderr, __VA_ARGS__); \
  fprintf(stderr, "\n"); \
  exit(EXIT_FAILURE); \
}

#define VERB(...) { \
  if (verbose) { \
    printf("%s:%d: ", __FILE__, __LINE__); \
    printf(__VA_ARGS__); \
    printf("\n"); \
  } \
}

static bool verbose = false;

#endif // _DMPVL_COMMON_H
