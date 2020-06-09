
#ifndef _PTYBYTEPIPE_H
#define _PTYBYTEPIPE_H

// https://man7.org/linux/man-pages/man7/feature_test_macros.7.html
#define _XOPEN_SOURCE 500
#include <stdlib.h>

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int ptyBytePipe_init(char * ptySymlinkPath);
int ptyBytePipe_getByte(int fd);
int ptyBytePipe_putByte(int fd, int b);

#endif // _PTYBYTEPIPE_H
