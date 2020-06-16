
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

void ptyBytePipe_firstInit(void) {
  VERB("Registering with atexit");
  if (0 != atexit(ptyBytePipe_exit)) {
    ERROR("Cannot register exit function.");
  }

  nEntries = 0;
  memset(&entries, 0, sizeof(entries));

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
    ptyBytePipe_firstInit();
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

  nEntries++;

  return fd;
}

// Read and return a single byte from pty, or -1 if no data is available.
int ptyBytePipe_getByte(int fd) {
  int nRead;
  char buf[1];

  VERB("read()");
  // https://linux.die.net/man/2/read
  if (0 > (nRead = read(fd, buf, 1))) {
    if ((EAGAIN != errno) && (EWOULDBLOCK != errno)) {
      ERROR("Cannot read byte");
    }
  }

  return (1 == nRead) ? (int)buf[0] : -1;
}

// Write a single byte to pty.
void ptyBytePipe_putByte(int fd, int b) {
  int nWritten;
  char buf[1] = { (char)(b & 0xff) };

  VERB("write()");
  if (0 > (nWritten = write(fd, buf, 1))) {
    ERROR("Cannot write byte");
  }

  if (1 != nWritten) {
    ERROR("nWritten=%d instead of 1", nWritten);
  }

  return;
}
