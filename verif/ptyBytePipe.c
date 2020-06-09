
#include "ptyBytePipe.h"

// Open a pseudo terminal (pty) then symlink to it from known path.
// Returns -1 on error, but will attempt to exit() first.
int
ptyBytePipe_init(char * ptySymlinkPath)
{
  int fd;
  char* ptsName;

  if ((fd = open("/dev/ptmx", O_RDWR | O_NOCTTY)) < 0) {
    perror(strerror(errno));
    exit(-1);
    return -1;
  } else if ( (grantpt(fd) != 0)                    ||
              (unlockpt(fd) != 0)                   ||
              ((ptsName = ptsname(fd)) == NULL)     ||
              (symlink(ptsName, ptySymlinkPath) != 0) ) {
    perror(strerror(errno));
    close(fd);
    exit(EXIT_FAILURE); return EXIT_FAILURE;
  } else {
    return fd;
  }
}

// Read and return a single byte from pty.
// If no data is immediately available return -1.
int
ptyBytePipe_getByte(int fd)
{
  int nRead;
  char buf[1];

  if ((nRead = read(fd, buf, 1)) < 1) {
    perror(strerror(errno));
    exit(EXIT_FAILURE); return EXIT_FAILURE;
  } else {
    return (int)buf[0];
  }
}

// Write a single byte to pty.
int
ptyBytePipe_putByte(int fd, int b)
{
  int nWritten;
  char buf[1] = { (char)(b & 0xff) };

  if ((nWritten = write(fd, buf, 1)) < 1) {
    perror(strerror(errno));
    exit(EXIT_FAILURE); return EXIT_FAILURE;
  } else {
    return nWritten;
  }
}
