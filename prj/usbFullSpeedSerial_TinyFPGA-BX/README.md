
usbFullSpeedSerial
==================

The verification components under `verif/usbFullSpeed*` are synthesizable so
this project uses them to build a working USB serial device.
The device is simple in that it just echos characters sent to it and flips the
case bit - e.g. `a --> A` or `b --> B`.

The verification components are written with verification in mind so are not
tuned for performance, power, or resource usage.
Therefore the resulting design is not particularly good, but it mainly
demonstrates that the components are correct enough to talk USB on real
hardware.

Expected resource usage is approximately 820 LUTs, synthing to around 60MHz.

A matching testbench is under `tb/usbFullSpeedSerial` with the host behaviour
defined by tb/usbFullSpeedSerial/driveHost.v` which can be used to simulate and
see waveforms for what *might* be happening on the hardware.


Usage
-----

To synthesize with Yosys, then place-and-route with NextPnR, analyse the
bitstream with Icetime, and program the TinyFPGA-BX board with tinyprog:

    > make && make prog

Now, assuming the programming executed without error, you can open a serial
terminal and try typing some characters.
If using the ACM configuration the device will show up as something like
`/dev/ttyACM0` with no further action required to enable it.
If using the generic serial configuration you'll need to find the VID:PID pair
and load the kernel module with the appropriate parameters:

    > lsusb
    ... snip ...
    Bus 002 Device 001: ID 1d6b:0003 Linux Foundation 3.0 root hub
    Bus 001 Device 010: ID 413c:2113 Dell Computer Corp.
    Bus 001 Device 012: ID 0525:a4a6 Netchip Technology, Inc. Linux-USB Serial Gadget
    Bus 001 Device 126: ID 0424:2734 Standard Microsystems Corp.
    ... snip ...
    > # Looks like device 12, but the VID:PID is configurable.
    > # "usbserial" is generic for prototypes, not production devices.
    > sudo modprobe usbserial vendor=0x0525 product=0xa4a6
    > # Driver binds device to something like /dev/ttyUSB0.

To check what the driver thinks is happening:

    > sudo dmesg --clear
    ... plug in device, wait a couple of seconds ...
    > sudo dmesg

Wireshark is also useful to examine higher level transactions, but only sees
activity at the OS level so you can't see individual packets.


MultiPnR
--------

The makefile contains recipies for quantifying the quality of a design by
seeing how much difference changing a random seed, or PnR tool has on the timing
results.
To perform many PNR runs with different seed values and compare Arachne-PnR
against NextPnR:

    > make synth && make multipnr N_RUNS=1000 -j8
    > xdg-open multipnr/*.pdf

Arachne is end-of-lifed already but remains useful due to the simple nature of
the placeing algorithm which is not timing aware.

NextPnR itself produces a timing estimate, but this is usually more optimistic
that the estimate given by Icetime.
Arachne does not produce a timing estimate itself.

A higher quality design not only synthesizes faster logic, but does so
consistently with little regard for placing algorithm or the seed the algorithm
is initialized with.
Consistency means that moving the design to a different FPGA family or process
node is likely to be less effort, and resynthesizing with *slight* modifications
shouldn't vastly change the attributes of the design.

Informally, when looking at the plot in the PDF, you want a peak as far to the
right (fast) as possible, and as narrow (consistent) as possible.
If some tools have very wide peaks and others have narrow peaks this indicates
you're relying on the tools to do a good job, rather than the design being
intrinsically "good".
A small number of runs will not produce useful plots so this type of analysis
can't be performed many times per hour for every little change.

