
# Dave McEwan 2021-03-30
# Send a file over a slow character device character-by-character.
# Simply cat'ing drops characters on very slow serial link, so this just
# throttles the transaction.
# Characters are also echoed to STDOUT to give visual validation of what is
# being sent.
#
# First, prepare the receiver like:
#   base64 -d > foobar
# Run like:
#   sudo sendSlowly.sh foobar /dev/ttyUSB2
#
# Finally, check results with md5sum or whatever hasher is available.

INTERCHARACTER_DELAY=0.05

FNAMEI=$1
FNAMEO=$2

CHARS=$(cat ${FNAMEI} | base64 | sed -E -e 's/(.)/\1\n/g')
for c in ${CHARS}; do
  echo -n "$c" | tee ${FNAMEO}
  sleep ${INTERCHARACTER_DELAY}
done
