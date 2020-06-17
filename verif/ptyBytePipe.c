
#include "ptyBytePipe.h"


void ptyBytePipe_verboseOn(void) {
  verbose = true;
}
void ptyBytePipe_verboseOff(void) {
  verbose = false;
}


static int nEntries = -1;
static ptyBytePipe_Entry entries[MAX_N_PTYBYTEPIPE];

// Close all file descriptors for PTY masters and delete all symlinks for PTY
// slaves on exit.
void ptyBytePipe_exit(void) {
  int i;

  if (0 > nEntries) {
    return;
  }

  for (i = 0; i < nEntries; i++) if (entries[i].valid) {

    // NOTE: Called within exit().
    // https://linux.die.net/man/2/close
    VERB("Closing fd[%d] %d", i, entries[i].fd);
    if (0 != close(entries[i].fd)) {
      fprintf(stderr, "ERROR: %s", strerror(errno));
    }

    VERB("Removing symlink[%d] %s", i, entries[i].symlinkPath);
    remove(entries[i].symlinkPath);

  }

  return;
}


// Open a pseudo terminal (pty) then symlink to it from known path.
// Returns -1 on error, but will attempt to exit() first.
// Caller is responsible for ensuring different paths are used on each call.
int ptyBytePipe_init(char* symlinkPath) {
  int fd;
  char* ptsName;

  // Check that there are free entries.
  if (nEntries >= MAX_N_PTYBYTEPIPE) {
    ERROR("Too many entries in ptyBytePipe");
  }
  if (0 > nEntries) {
    VERB("Registering with atexit");
    if (0 != atexit(ptyBytePipe_exit)) {
      ERROR("Cannot register exit function.");
    }

    nEntries = 0;
    memset(&entries, 0, sizeof(entries));
  }

  VERB("Opening /dev/ptmx");
  if (0 > (fd = open("/dev/ptmx", O_RDWR | O_NOCTTY | O_NONBLOCK))) {
    ERROR("Cannot open /dev/ptmx");
  }
  entries[nEntries].fd = fd;
  entries[nEntries].valid = true;
  VERB("fd: %d", fd);

  VERB("Granting access to slave PTY");
  // https://linux.die.net/man/3/grantpt
  if (0 != grantpt(fd)) {
    ERROR("Cannot grant access to slave PTY");
  }

  VERB("Unlocking PTY master/slave pair");
  // https://linux.die.net/man/3/unlockpt
  if (0 != unlockpt(fd)) {
    ERROR("Cannot unlock PTY master/slave pair");
  }

  VERB("Getting name of PTY slave");
  // https://linux.die.net/man/3/ptsname
  if (NULL == (ptsName = ptsname(fd))) {
    ERROR("Cannot get PTY slave name");
  }
  strncpy(entries[nEntries].symlinkPath, symlinkPath, MAX_SYMLINKPATH_LENGTH);
  VERB("PTY slave: %s", ptsName);

  VERB("Removing any existing symlink");
  // https://linux.die.net/man/3/remove
  remove(symlinkPath);

  VERB("Creating symlink %s --> %s", symlinkPath, ptsName);
  // https://linux.die.net/man/7/symlink
  if (0 != symlink(ptsName, symlinkPath)) {
    ERROR("Cannot symlink PTY slave");
  }

  VERB("Setting non-canonical mode");
  // https://linux.die.net/man/3/termios
  // https://blog.nelhage.com/2009/12/a-brief-introduction-to-termios/
  // https://blog.nelhage.com/2009/12/a-brief-introduction-to-termios-termios3-and-stty/
  // https://www.cmrr.umn.edu/~strupp/serial.html
  struct termios options;
  if (0 != tcgetattr(fd, &options)) {
    ERROR("Cannot get terminal attributes");
  }
  cfmakeraw(&options);
  if (0 != tcsetattr(fd, TCSANOW, &options)) {
    ERROR("Cannot set terminal attributes");
  }

  nEntries++;

  return fd;
}

// Read and return a single byte from pty, or -1 if no data is available.
int ptyBytePipe_getByte(int fd) {
  int ret;
  char buf[1];

  VERB("Enter fd=%d", fd);

  // https://linux.die.net/man/2/read
  int nRead = read(fd, buf, 1);
  if (0 > nRead) {
    ret = -1;
    VERB("  errno=%d", errno);

    if ((EAGAIN == errno) || (EWOULDBLOCK == errno)) {
      errno = 0;
    } else if (EIO == errno) {
      errno = 0;
    } else {
      ERROR("Cannot read byte");
    }
  } else {
    VERB("  nRead=%d buf[0]=%c errno=%d", nRead, buf[0], errno);
    ret = (1 == nRead) ? (int)buf[0] : -1;
  }


  VERB("  Exit ret=%d", ret);
  return ret;
}

// Write a single byte to pty.
int ptyBytePipe_putByte(int fd, int b) {
  int nWritten;
  char buf[1] = { (char)(b & 0xff) };

  VERB("Enter fd=%d b=%d", fd, b);

  nWritten = write(fd, buf, 1);

  if (1 < nWritten) {
    ERROR("nWritten=%d < 1", nWritten);
  }

  VERB("  Exit nWritten=%d", nWritten);
  return nWritten;
}
