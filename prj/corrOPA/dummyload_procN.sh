
# Dave McEwan 2021-03-29
# Bash/Busybox compatible dummy workload for multiple processes.
# The intention is to create many inter-dependent processes in order to
# visualize the interactions between cores on SMP Linux.

# First, configure parameters in dummyproc_proc1.sh, like how long to run for.
# Run like:
#   ./dummyload_procN.sh 100 > /dev/null

# Find location of dummyload scripts.
DUMMYLOAD_DIR=$(dirname $0)
DUMMYLOAD_PROC1=${DUMMYLOAD_DIR}/dummyload_proc1.sh
DUMMYLOAD_PROCN=${DUMMYLOAD_DIR}/dummyload_procN.sh

if [ "$#" -lt 1 ]; then
  echo "${USAGE}"
  exit 1
fi
if [ 1 -le "$1" ] && [ "$1" -lt 4294967296 ]; then
  N_PROC="$1"
else
  echo "${USAGE}"
  echo "*** nProc must be positive integer less than 2**32."
  exit 1
fi

seq 0 $((${N_PROC}-1)) | xargs -i -P ${N_PROC} ${DUMMYLOAD_PROC1} '{}' ${N_PROC}
