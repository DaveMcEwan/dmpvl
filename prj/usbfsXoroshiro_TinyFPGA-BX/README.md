
usbfsXoroshiro
==============

Simple PRNG implementing the xoroshiro128+ algorithm as example implementation
of BytePipe over USB-FS.

Xoroshiro128+ is a modern pseudo-random number generator (PRNG) algorithm based
on Marsaglia's Xorshift shift-register generators, developed by Sebastias Vigna
and David Blackman in 2016 thru 2018.
The main website <http://prng.di.unimi.it/> for the Xoroshiro family of PRNGs
provides all of the relevant detail for implementing these algorithms in
software.
This USB Full Speed project is a hardware device which runs the algorithm, by
implementing `next()` in hardware, at 48MHz.
Data is generated much faster than can be read over USB at 64b per cycle at
48MHz (3.072 Gb/s) so only the upper byte of the result is readable.

The algorithm's 128b (16B) state is readable using addresses 16 thru 31, and
the upper byte of the 64b result is readable using address 1.
Reading address 0 always returns the value 0.
The state is comprised of 2 64b registers `{s1,s0}` which are
seeded/initialized by writing to address 1 using a 16B BytePipe burst.
Since the generator begins to run as soon as the state is non-zero,
it is essential to use a burst write so that the registers take the 16B of seed
in consecutive clock cycles.
As each byte is written, the value in `{s1,s0}` is shifted up 8b and the new
seed byte placed into the bottom 8b, i.e. `{s1,s0} ← ({s1,s0} << 8) | newByte`.
This minimal memory map allows the device to be implemented using as few
resources as possible.


Use the `bytePipe-utils` script from dmppl to interact with the device.
```
# Activate your virtual environment.
source <your venv activate>

# Install dmppl from GitHub.
git clone https://github.com/DaveMcEwan/dmppl.git
cd dmppl
pip install -e .

# Connect the TinyFPGA-BX, upload the bitfile to configure the FPGA.
make prog
```

To stop the generator write 16B of zeros to address 1 in order to clear all
128b of generator state.
```
bytePipe-utils -v --no-prog -a=1 -f=/dev/zero -n=16 put
```

To start the generator write 16B of seed to address 1.
In this example the seed is generated using the host's `/dev/urandom` linear
congrential generator.
The registers `s1` then `s0` are written with most significant bytes first.
```
bytePipe-utils -v --no-prog -a=1 -f=/dev/urandom -n=16 put
```

To acquire 12345B of pseudo-random data the generator read from address 1.
In this example data is placed into the file `myData.bin`.
```
bytePipe-utils -v --no-prog -a=1 -f=myData.bin -n=12345 get
```

The Lattice iCE40LP process is fairly slow in the field of FPGA processes as it
is intended to be used in low-cost and low-power applications.
Utilization of the part on the TinyFPGA-BX (iCE40LP8K) is reported by nextpnr:

     ICESTORM_LC:  1274/ 7680    16%
    ICESTORM_RAM:     3/   32     9%
           SB_IO:     5/  256     1%
           SB_GB:     5/    8    62%
    ICESTORM_PLL:     1/    2    50%
     SB_WARMBOOT:     0/    1     0%

The design should also have plenty of timing slack with nextpnr reporting a
maximum clock speed of around 60MHz, although this is restricted to 48MHz in
order for the USB interface to function correctly.

