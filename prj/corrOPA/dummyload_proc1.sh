
# Dave McEwan 2021-03-29
# Bash/Busybox compatible dummy workload for single processes.

# Verbose option for debugging.
#VERBOSE=true
verb () {
  if [ "$VERBOSE" = true ]; then
    echo "instance=${INSTANCE} <<< $@ >>>"
  fi
}

# Number of random bytes to gather in each block.
BLOCKSIZE=8

# Number of seconds to run for.
# Actual runtime will be slightly longer.
SECONDS_RUNTIME=10

# Number of attempts to find destination for each block.
# Any number greater than 1 should be fine as long as the system isn't running
# out of memory.
N_DST_RETRIES=5

# Number of seconds to attempt reading this process's FIFO.
SRC_TIMOUT=1

# Find location of dummyload scripts.
DUMMYLOAD_DIR=$(dirname $0)
DUMMYLOAD_PROC1=${DUMMYLOAD_DIR}/dummyload_proc1.sh
DUMMYLOAD_PROCN=${DUMMYLOAD_DIR}/dummyload_procN.sh

# {{{ process args
# First arg is ID number for this single process, integer in [0, N).
# Second arg is number of parallel dummy processes, integer in [1, 2**32).

USAGE="dummyload Provide a dummy workload to multiple communicating processes.

Usage: ${DUMMYLOAD_PROC1} <instance> <nProc>
  instance: integer in [0, N)
  nProc:    integer in [1, 2**32)

However, you likely want to run ${DUMMYLOAD_PROCN}"

if [ "$#" -lt 2 ]; then
  echo "${USAGE}"
  exit 1
fi
if [ 1 -le "$2" ] && [ "$2" -lt 4294967296 ]; then
  N_PROC="$2"
  RND_PROC_CMD="shuf -i 0-$((${N_PROC}-1)) -n 1"
else
  echo "${USAGE}"
  echo "*** nProc must be positive integer less than 2**32."
  exit 1
fi
if [ 0 -le "$1" ] && [ "$1" -lt "${N_PROC}" ]; then
  INSTANCE="$1"
  INSTANCE_FIFO=./dummyload_$1.fifo
else
  echo "${USAGE}"
  echo "*** instance must be positive integer less than nProc."
  exit 1
fi

# }}} process args
verb BEGIN ${INSTANCE} ${N_PROC}
#echo $SHELL
#exit 0

# Create FIFO which other processes can write to.
CLEANUP_CMD="rm -f ${INSTANCE_FIFO}"
trap "${CLEANUP_CMD}" EXIT
${CLEANUP_CMD}
mkfifo ${INSTANCE_FIFO}

## NOTE: read -u 3 line is Bash-specific
## This process reads fifo from file-descriptor 3.
##echo "" > ${INSTANCE_FIFO} & exec 3< ${INSTANCE_FIFO}
##read -u 3 line
# Use empty while loop to avoid the non-POSIX flag "-u"
echo "" > ${INSTANCE_FIFO} &
while read -r line; do break; done < ${INSTANCE_FIFO}

# Run this process for a set number of seconds.
SECONDS_BEGIN=$(date -u +%s)
while [ "$(($(date -u +%s) - SECONDS_BEGIN))" -lt "${SECONDS_RUNTIME}" ]; do

  # Send random block to a randomly-selected process, non-blocking.
  DST=""
  ATTEMPTS_REMAINING=${N_DST_RETRIES}
  while [ -z "${DST}" ] && [ 0 -lt "${ATTEMPTS_REMAINING}" ]; do
    ATTEMPTS_REMAINING=$((ATTEMPTS_REMAINING-=1))
    DST_MAYBE=./dummyload_$(${RND_PROC_CMD}).fifo
    if [ -p "${DST_MAYBE}" ]; then
      DST=${DST_MAYBE}
      B=$(dd bs=${BLOCKSIZE} count=1 status=none if=/dev/urandom | base64)
      echo ${B} > ${DST} &
      verb SENT ${B} to ${DST}
    fi
  done
  verb DST ${DST}

  # Consume all available blocks from the FIFO.
  BLOCKS=$(timeout ${SRC_TIMOUT} cat ${INSTANCE_FIFO})
  for BLOCK in ${BLOCKS}; do
    # Data is a space-separated list of decimal-formatted uint8's.
    # NOTE: hexdump -v is essential to avoid repetitions being replaced with *'s.
    BLOCK_BYTES=$(echo ${BLOCK} | base64 -d | hexdump -v -e '/1 " %u "')
    verb BLOCK_BYTES "${BLOCK_BYTES}"

    # Do something with our block.
    DUMMY_SUM=0; for x in ${BLOCK_BYTES}; do DUMMY_SUM=$((DUMMY_SUM+=x)); done
    DUMMY_ARITHMEAN=$(expr ${DUMMY_SUM} / ${BLOCKSIZE})
    echo "instance=${INSTANCE} RESULT ${DUMMY_SUM} ${DUMMY_ARITHMEAN}"
  done

done

