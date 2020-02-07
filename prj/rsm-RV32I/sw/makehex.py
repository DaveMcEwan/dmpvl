#!/usr/bin/env python3
#
# This is free and unencumbered software released into the public domain.
#
# Anyone is free to copy, modify, publish, use, compile, sell, or
# distribute this software, either in source code form or as a compiled
# binary, for any purpose, commercial or non-commercial, and by any
# means.

from sys import argv

binfile = argv[1]
nkbytes = int(argv[2])

nbytes = nkbytes * 1024
nwords = nkbytes * 256

with open(binfile, "rb") as f:
    bindata = f.read()

# Data must end on 32b boundary.
bindata_nbytes = len(bindata)
assert bindata_nbytes % 4 == 0

# Data must fit into given size.
assert bindata_nbytes < nbytes, "len(bindata)=%d, nbytes=%d" % \
                                (bindata_nbytes, nbytes)

for i in range(nwords):
    if i < len(bindata) // 4:
        w = bindata[4*i : 4*i+4]
        print("%02x%02x%02x%02x" % (w[3], w[2], w[1], w[0]))
    else:
        print("0")

