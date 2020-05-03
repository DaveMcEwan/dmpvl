
usbfsXoroshiro
==============

Simple PRNG implementing the xoroshiro128+ algorithm as example implementation
of BytePipe over USB-FS.

Use the `bytePipe-utils` script from dmppl to interact and test.
TODO: Document memmap, modify bytePipe.py to allow write ACK, plots.

```
# Activate your virtual environment.
source <your venv activate>

# Install dmppl from GitHub.
git clone https://github.com/DaveMcEwan/dmppl.git
cd dmppl
pip install -e .

# Connect the TinyFPGA-BX, then test the BytePipe implementation.
# This make rule uploads the bitfile then runs a series of tests.
make test
```

Assuming that you haven't reset the TinyFPGA-BX you can reconnect and perform
further actions, using `--no-prog` to avoid re-uploading the bitfile.

Run another test, using the verbose option (`-v`) to get messages describing
what's happening.
```
bytePipe-utils -v --no-prog test
```

Sequentially read each address and dump the values.
NOTE: These look random but include the register state, not just the result.
```
bytePipe-utils -v --no-prog dump
```

Get (read) an arbitrary number of bytes from an address to a file.
It is intended that some locations are backed by a FIFO or other stream of data
so this uses the underlying bandwidth of the USB-FS channel efficiently to
retreive a specified number of bytes.
```
bytePipe-utils -v --no-prog -a=55 -f=myFile.bin -n=123 get
```

Measure and record read bandwidth by reading a large number of bytes to nowhere.
The `--record-time` option creates a CSV file `./bpRecordTime.csv` with two
columns - number of bytes on the left, and time (ns since epoch) on the right.
```
bytePipe-utils -v --no-prog --record-time -a=55 -f=/dev/null -n=99999999 get
```

[bwRead]: ./img/usbfsXoroshiro_bandwidth25s_read.png "Bandwidth over 25s Read"

The dmppl repository also includes a general plotting tool for CSV data which
can be used to plot the bandwidth.
Shift and reduce time (X-axis) to get microseconds since the beginning of
transfer, and plot the transfer rate `bytes'/time'` over time.
```
plotCsv -v bpRecordTime.csv \
  --baseX --mulX=0.001 \
  --product --diffX --diffY --invX \
  --xlabel="Time (us)" --ylabel="Rate (MB/s)" --marker=""
```
![Bandwidth over 25s Read][bwRead]


