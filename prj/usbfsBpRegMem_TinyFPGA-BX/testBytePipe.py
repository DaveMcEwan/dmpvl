#!/usr/bin/env python3

# Test BytePipe (USB Host Utility)
# Dave McEwan 2020-04-20
#
# Plug in the board then run like:
#    testBytePipe.py &
#
# A bitfile implementing the usbfsBpRegMem logic is required to be build from
# the SystemVerilog2005 implementation
# The bitfile to immediately program the board with is found using the first of
# these methods:
# 1. Argument `-b,--bitfile`
# 2. Environment variable `$TESTBYTEPIPE_BITFILE`
# 3. The last item of the list `./usbfsBpRegMem.*.bin`
# 4. './usbfsBpRegMem.bin`
# Depends on PyPI package "tinyprog", which also depends on "pyserial".
#
# After programming, the board presents itself as a USB serial device.
# The device to connect to is found using the first of these methods:
# 1. Argument `-d,--device`
# 2. Environment variable `$TESTBYTEPIPE_DEVICE`
# 3. The last item of the list `/dev/ttyACM*`

# mypy --ignore-missing-imports testBytePipe.py

# Standard library
import argparse
import functools
import glob
import locale
import os
import subprocess
import sys
import time
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, \
    Tuple, Union, cast

# PyPI
import serial

# git clone https://github.com/DaveMcEwan/dmppl.git && pip install -e dmppl
from dmppl.base import run, verb, dbg

__version__ = "0.1.0"

# {{{ types

BpAddrs = Sequence[int]
#BpAddrValues = Tuple[Tuple[int, int], ...]
BpAddrValues = Sequence[Tuple[int, int]]

# Specific type for the values of the whole addressable range (128B).
BpMem = Tuple[int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int,
              int, int, int, int, int, int, int, int]

# }}} types

def getBitfilePath(argBitfile) -> str: # {{{

    envBitfile = os.environ.get("TESTBYTEPIPE_BITFILE")
    orderedBitfiles = sorted(glob.glob("usbfsBpRegMem.*.bin"))

    if argBitfile is not None:
        ret = argBitfile
    elif envBitfile is not None:
        ret = envBitfile
    elif len(orderedBitfiles) > 0:
        ret = orderedBitfiles[-1]
    else:
        ret = os.sep.join((os.path.dirname(os.path.abspath(__file__)),
                           "usbfsBpRegMem.bin"))

    return ret
# }}} def getBitfilePath

def getDevicePath(argDevice) -> str: # {{{

    envDevice = os.environ.get("TESTBYTEPIPE_DEVICE")
    orderedDevices = sorted(glob.glob("/dev/ttyACM*"))

    if argDevice is not None:
        ret = argDevice
    elif envDevice is not None:
        ret = envDevice
    elif len(orderedDevices) > 0:
        ret = orderedDevices[-1]
    else:
        ret = "/dev/null" # Useful for debug.
        # TODO: raise OSError("Device not found. Use --help for details.")

    return ret
# }}} def getDevicePath

def uploadBitfile(bitfile): # {{{

    p = subprocess.run(("tinyprog", "-p", bitfile))

    return p.returncode
# }}} def uploadBitfile

def bpAddrValuesToMem(addrValues:BpAddrValues) -> BpMem: # {{{

    ret_:List[int] = [-1]*128
    for addr,value in addrValues:
        assert isinstance(addr, int), (type(addr), addr)
        assert 0 <= addr < 128, addr
        assert isinstance(value, int), (type(value), value)
        assert 0 <= value < 256, value
        ret_[addr] = value

    assert isinstance(ret_, list), (type(ret_), ret_)
    assert 128 == len(ret_), (len(ret_), ret_)
    ret:BpMem = cast(BpMem, tuple(ret_))

    assert isinstance(ret, tuple), (type(ret), ret)
    assert 128 == len(ret), (len(ret), ret)
    return ret
# }}} def bpAddrValuesToMem

def bpReadSequential(device, addrs:BpAddrs) -> BpAddrValues: # {{{

    ret_ = []
    for i,addr in enumerate(addrs):

        # Send read command
        assert isinstance(addr, int), (type(addr), addr)
        assert 0 <= addr < 128, (i, addr)
        assert 1 == device.write(bytes([addr]))

        # First return value is discarded.
        if 0 == i:
            continue
        else:
            value:int = ord(device.read(1))
            dbg(value)
            ret_.append((addrs[i-1], value))

    # Last address is sent again,
    assert 1 == device.write(bytes([addrs[-1]]))
    ret_.append((addrs[-1], ord(device.read(1))))

    # Finalize return value.
    ret = tuple(ret_)

    assert len(ret) == len(addrs), (ret, addrs)
    assert all((a == ra) for a,(ra,rv) in zip(addrs, ret))
    assert all((rv < 256) for ra,rv in ret)

    return ret
# }}} def bpReadSequential

def bpWriteSequential(device, addrValues:BpAddrValues) -> BpAddrValues: # {{{

    ret_ = []
    for i,(addr,value) in enumerate(addrValues):

        # Send write command
        assert isinstance(addr, int), (type(addr), addr)
        assert 0 <= addr < 128, (i, addr)
        assert 2 == device.write(bytes([addr + 128, value]))

        ret_.append((addr, ord(device.read(1))))

    # Finalize return value.
    ret:BpAddrValues = tuple(ret_)

    assert len(ret) == len(addrValues), (ret, addrValues)
    assert all((a == ra) for (a,v),(ra,rv) in zip(addrValues, ret))
    assert all((rv < 256) for ra,rv in ret)

    return ret
# }}} def bpWriteSequential

# {{{ argparser

argparser = argparse.ArgumentParser(
    formatter_class = argparse.ArgumentDefaultsHelpFormatter
)

argparser.add_argument("-b", "--bitfile",
    type=str,
    default=None,
    help="Bitfile for FPGA implementing hardware."
         " If None then try using environment variable `$TESTBYTEPIPE_BITFILE`;"
         " Then try using the last item of `./usbfsBpRegMem.*.bin`;"
         " Then try using the bundled bitfile.")

argparser.add_argument("--no-prog",
    action="store_true",
    help="Don't attempt to program a bitfile."
         " Assume there's already a programmed device available.")

argparser.add_argument("-d", "--device",
    type=str,
    default=None,
    help="Serial device to connect to (immediately after progrmming)."
         " If None then try using environment variable `$TESTBYTEPIPE_DEVICE`;"
         " Then try using the last item of `/dev/ttyACM*`.")

# }}} argparser

def main(args) -> int: # {{{
    '''
    1. Upload bitfile to TinyFPGA-BX (optional).
    2. Open connection to device.
    3. Discover writable bits.
    '''

    locale.setlocale(locale.LC_ALL, '')

    if not args.no_prog:
        bitfile = getBitfilePath(args.bitfile)
        verb("Uploading bitfile %s ..." % bitfile, end='')
        uploadBitfile(bitfile)
        verb("Done")

        # Allow OS time to enumerate USB before looking for device.
        waitTime = 4.5 # seconds
        verb("Waiting %0.01fs before connecting..." % waitTime, end='')
        time.sleep(waitTime)
        verb("Done")

    devicePath = getDevicePath(args.device)

    # Keep lock on device to prevent other processes from accidentally messing
    # with the state machine.
    verb("Connecting to device %s" % devicePath)
    with serial.Serial(devicePath, timeout=1.0, write_timeout=1.0) as device:
        rd:Callable = functools.partial(bpReadSequential, device)
        wr:Callable = functools.partial(bpWriteSequential, device)
        mem:Callable = bpAddrValuesToMem

        verb("Reading all register locations...", end='')
        init0:BpMem = mem( rd(list(range(128))) )
        verb("Done")

        verb("Writing ones to all register locations...", end='')
        init1:BpMem = mem( wr(list((addr, 0xff) for addr in range(128))) )
        verb("Checking previous unchanged...", end='')
        assert all((i0 == i1) for i0,i1 in zip(init0, init1))
        verb("Done")

        verb("Writing zeros to all register locations...", end='')
        ones:BpMem = mem( wr(list((addr, 0x00) for addr in range(128))) )
        verb("Done")

        verb("Reading all register locations...", end='')
        zeros:BpMem = mem( rd(list(range(128))) )
        verb("Checking writable bits...", end='')
        symdiff:BpMem = cast(BpMem, tuple(o ^ z for o,z in zip(ones, zeros)))
        verb("Done")

        # Increasing left-to-right and top-to-bottom.
        # Text of 16 lines of 8 bytes.
        print("Writable bits:")
        for i in range(16):
            base = i*8

            line = ' '.join("%02x" % symdiff[base + offset] \
                            for offset in range(8))

            print("  %3d .. %3d: %s" % (base, base+7, line))

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

