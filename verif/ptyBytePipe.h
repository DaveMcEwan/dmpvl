
#ifndef _PTYBYTEPIPE_H
#define _PTYBYTEPIPE_H

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "svdpi.h"

int ptyBytePipe_init(char * ptySymlinkPath);
int ptyBytePipe_getByte(int fd);
int ptyBytePipe_putByte(int fd, int b);

#endif // _PTYBYTEPIPE_H
