
#ifndef _PTYBYTEPIPE_H
#define _PTYBYTEPIPE_H

// https://man7.org/linux/man-pages/man7/feature_test_macros.7.html
#define _XOPEN_SOURCE 500
#include <stdlib.h>

#include <errno.h>
#include <error.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

// Maximum number of pipes which can be instanced by tb.
// May be changed to larger number which will only increase static memory usage.
#define MAX_N_PTYBYTEPIPE 32

// Maximum number of characters for a symlink path.
#define MAX_SYMLINKPATH_LENGTH 256

typedef struct ptyBytePipe_Entry
{
  int fd;
  char symlinkPath[MAX_SYMLINKPATH_LENGTH];
  bool valid;
} ptyBytePipe_Entry;

void  ptyBytePipe_verboseOn(void);
void  ptyBytePipe_verboseOff(void);
int   ptyBytePipe_init(char * ptySymlinkPath);
int   ptyBytePipe_getByte(int fd);
void  ptyBytePipe_putByte(int fd, int b);

#endif // _PTYBYTEPIPE_H
