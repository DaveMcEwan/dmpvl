
usbfsBpRegMem
=============

Simple 128B register block as example implementation of BytePipe over USB-FS.

Use the `bytePipe-utils` script from dmppl to interact and test.

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
```
bytePipe-utils -v --no-prog dump
```

Identify the writable bits.
Write ones then zeros to each location and record the results.
Any bits which flipped are considered writable.
```
bytePipe-utils -v --no-prog bits
```

Reset the BytePipe FSM in case of confusion.
This performs a sequence of 256 single reads from address 0 (the burst counter)
which are allowed to return no data,
```
bytePipe-utils -v --no-prog reset
```

Peek the value from a particular location.
Decimal or hexadecimal formats are supported for address argument.
```
bytePipe-utils -v --no-prog -a=55 peek
bytePipe-utils -v --no-prog -a=0x37 peek
```

Poke a particular value to a particular location.
Decimal or hexadecimal formats are also supported for data argument.
```
bytePipe-utils -v --no-prog -a=55 -d=123 poke
bytePipe-utils -v --no-prog -a=0x37 -d=0x7b poke
```

Get (read) an arbitrary number of bytes from an address to a file.
It is intended that some locations are backed by a FIFO or other stream of data
so this uses the underlying bandwidth of the USB-FS channel efficiently to
retreive a specified number of bytes.
```
bytePipe-utils -v --no-prog -a=55 -f=myFile.bin -n=123 get
```

Put (write) an arbitrary number of bytes to an address from a file.
```
bytePipe-utils -v --no-prog -a=55 -f=myFile.bin -n=123 put
```

Measure and record read bandwidth by reading a large number of bytes to nowhere.
Or similarly, for write bandwidth by writing a large number of bytes from
anywhere.
The `--record-time` option creates a CSV file `./bpRecordTime.csv` with two
columns - number of bytes on the left, and time (ns since epoch) on the right.
This file may be processed and plotted as desired.
```
bytePipe-utils -v --no-prog --record-time -a=55 -f=/dev/null -n=99999999 get
bytePipe-utils -v --no-prog --record-time -a=55 -f=/dev/urandom -n=99999999 put
```


BytePipe Protocol
-----------------

[rdSingle]: ./img/BytePipe_rdSingle.wavedrom.svg "BytePipe Read Single"
[wrSingle]: ./img/BytePipe_wrSingle.wavedrom.svg "BytePipe Write Single"
[rdBurst]: ./img/BytePipe_rdBurst.wavedrom.svg "BytePipe Read Burst"
[wrBurst]: ./img/BytePipe_wrBurst.wavedrom.svg "BytePipe Write Burst"

The BytePipe protocol is designed to be very low cost and simple to implement
on top of any underlying protocol which sends and receives whole numbers of
bytes.
There are 17 mandatory bits of state (`addr:7b`, `burst:8b`, `rd:1b`, `wr:1b`),
and flow control uses valid/ready handshaking with the same semantics as AXI.

There ara a small number of simple rules foverning the internal state machine:
1. A transaction is initiated by the host sending the device 1 byte, while the
   device is not already processing a transaction.
2. The `addr` register is updated on the initiation of each transaction.
3. All single transactions cause the device to produce a 1B response.
4. The `burst` register may be written to with address `0` to indicate that the
   next transaction is "burst", rather than "single".

A single read transaction is initiated by the host sending a single byte with
the top bit clear; I.E. Value less than 128.
The device immediately returns a byte containing the value at whatever
address was previously in the `addr` register, and updates `addr`.
E.G. If `addr` contains `0x12`, and the host begins a single read transaction
by sending `0x55`, then the device will return the contents of location
`0x12` and update `addr` to be `0x55`.

![BytePipe Read Single][rdSingle]

A single write transaction is initiated by the host sending a single byte with
the top bit set; I.E. Value greater than 127.
The device immediately begins waiting for the data byte, and updates `addr`.
The next byte received by the device is then written to that the location
pointed to by `addr`.
This second byte causes the device to return 1B containing the value which is
now overwritten, in effect a write acknowledgement.
E.G. If the host begins a single write transaction by sending `0xD5`, then the
device will update `addr` to `0x55`.
When the host sends the next byte, `0xAA` the device will write the value `0xAA`
to address `0x55`.

![BytePipe Write Single][wrSingle]

A read burst is initiated by the host by performing a single write transaction
to address 0 where the value is the number of bytes desired.
Therefore, a read burst may be used to receive up to 255B.
The host then sends another byte with the top bit clear and the address in the
lower 7b, as with a single read.
The first byte returned is the value at address 0, which is
implementation-specific.
Each subsequent byte returned by the device decrements `burst`, and when
`burst=0` the transaction is complete.

![BytePipe Read Burst][rdBurst]

A write burst is initiated by the host by performing a single write transaction
to address 0 where the value is the number of bytes-1 desired.
Therefore, a write burst may be used to send up to 256B.
The host then sends another byte with the top bit set and the address in the
lower 7b, as with a single write.
Each subsequent byte received by the device decrements `burst`, and when
`burst=0` the transaction is complete.

![BytePipe Write Burst][wrBurst]

All burst transactions therefore have an overhead of 5B.
The maximum efficiency of a burst read is `255/(255+5)`, just over 98%.
The maximum efficiency of a burst read is `256/(256+5)`, just over 98%.

