#!/usr/bin/env python3

# Test BytePipe (USB Host Utility)
# Dave McEwan 2020-04-20
#
# Plug in the board then run like:
#    python testBytePipe.py
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
from dmppl.bytePipe import BpAddrs, BpAddrValues, BpMem, \
    bpReadSequential, bpWriteSequential, bpPrintMem, bpAddrValuesToMem

__version__ = "0.1.0"

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
        raise OSError("Device not found. Use --help for details.")

    return ret
# }}} def getDevicePath

def uploadBitfile(bitfile): # {{{

    p = subprocess.run(("tinyprog", "-p", bitfile))

    return p.returncode
# }}} def uploadBitfile

def actionBits(rd, wr, mem): # {{{
    verb("Writing ones to all register locations...", end='')
    _ = mem( wr(list((addr, 0xff) for addr in range(128))) )
    verb("Done")

    verb("Writing zeros to all register locations...", end='')
    ones:BpMem = mem( wr(list((addr, 0x00) for addr in range(128))) )
    verb("Done")

    verb("Reading all register locations...", end='')
    zeros:BpMem = mem( rd(list(range(128))) )
    verb("Checking writable bits...", end='')
    symdiff:BpMem = cast(BpMem, tuple(o ^ z for o,z in zip(ones, zeros)))
    verb("Done")

    bpPrintMem("Writable bits", symdiff)

    return # No return value
# }}} def actionBits

def actionDump(rd, wr, mem): # {{{
    verb("Reading all register locations...", end='')
    init0:BpMem = mem( rd(list(range(128))) )
    verb("Done")

    bpPrintMem("Dump", init0)

    return # No return value
# }}} def actionDump

def actionTest(rd, wr, mem): # {{{
    verb("Reading all register locations...", end='')
    init0:BpMem = mem( rd(list(range(128))) )
    verb("Done")
    bpPrintMem("Initial values", init0)

    verb("Writing ones to all register locations...", end='')
    init1:BpMem = mem( wr(list((addr, 0xff) for addr in range(128))) )
    verb("Done")
    bpPrintMem("Initial values (again)", init1)
    verb("Checking previous unchanged...", end='')
    assert all((i0 == i1) for i0,i1 in zip(init0, init1))
    verb("Done")

    verb("Writing zeros to all register locations...", end='')
    ones:BpMem = mem( wr(list((addr, 0x00) for addr in range(128))) )
    verb("Done")
    bpPrintMem("Ones", ones)

    verb("Reading all register locations...", end='')
    zeros:BpMem = mem( rd(list(range(128))) )
    verb("Checking writable bits...", end='')
    symdiff:BpMem = cast(BpMem, tuple(o ^ z for o,z in zip(ones, zeros)))
    verb("Done")
    bpPrintMem("Zeros", zeros)
    bpPrintMem("Writable bits", symdiff)

    verb("Writing unique values to all register locations...", end='')
    _ = mem( wr(list((addr, addr+10) for addr in range(128))) )
    verb("Reading back...", end='')
    addrPlus10:BpMem = mem( rd(list(range(128))) )
    verb("Done")
    bpPrintMem("mem[addr] <-- (addr+10)", addrPlus10)

    return # No return value
# }}} def actionTest

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

actions = {
    "bits": actionBits,
    "dump": actionDump,
    "test": actionTest,
}
argparser.add_argument("action",
    nargs='?',
    choices=actions.keys(),
    default="bits",
    help="Perform a full test,"
         " just dump the memory contents,"
         " or identify all writable bits.")

# }}} argparser

def main(args) -> int: # {{{
    '''
    1. Upload bitfile to TinyFPGA-BX (optional).
    2. Open connection to device.
    3. Discover writable bits.
    '''

    locale.setlocale(locale.LC_ALL, '')

    if args.no_prog:
        devicePath = getDevicePath(args.device)
    else:
        bitfile = getBitfilePath(args.bitfile)
        verb("Uploading bitfile %s ..." % bitfile, end='')
        assert 0 == uploadBitfile(bitfile)
        verb("Done")

        # Allow OS time to enumerate USB before looking for device.
        nAttempts = 10
        waitTime = 1 # seconds
        verb("Waiting up to %0.01fs..." % (nAttempts * waitTime), end='')

        maybeDevicePath_:Optional[str] = None
        for _ in range(nAttempts):
            time.sleep(waitTime)
            try:
                maybeDevicePath_ = getDevicePath(args.device)
                break
            except OSError:
                pass

        if maybeDevicePath_ is None:
            return 1
        else:
            devicePath = maybeDevicePath_

        verb("Done")


    # Keep lock on device to prevent other processes from accidentally messing
    # with the state machine.
    verb("Connecting to device %s" % devicePath)
    with serial.Serial(devicePath, timeout=1.0, write_timeout=1.0) as device:
        rd:Callable = functools.partial(bpReadSequential, device)
        wr:Callable = functools.partial(bpWriteSequential, device)
        mem:Callable = bpAddrValuesToMem

        actions[args.action](rd, wr, mem)

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

