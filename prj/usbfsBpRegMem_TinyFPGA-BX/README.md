
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
Decimal or hexadecimal formats are supported for both address and data options.
```
bytePipe-utils -v --no-prog -a=55 peek
bytePipe-utils -v --no-prog -a=0x37 peek
```

Poke a particular value to a particular location.
```
bytePipe-utils -v --no-prog -a=55 -d=123 poke
bytePipe-utils -v --no-prog -a=0x37 -d=0x7b poke
```

Get (read) an arbitrary number of bytes from an address into a file.
It is intended that some locations are backed by a FIFO or other stream of data
so this uses the underlying bandwidth of the USB-FS channel efficiently to
retreive a specified number of bytes.
```
bytePipe-utils -v --no-prog -a=55 -f=myFile.bin -n=123 get
```
