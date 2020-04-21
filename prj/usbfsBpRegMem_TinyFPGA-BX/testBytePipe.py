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
#
# After programming, the board presents itself as a USB serial device.
# The device to connect to is found using the first of these methods:
# 1. Argument `-d,--device`
# 2. Environment variable `$TESTBYTEPIPE_DEVICE`
# 3. The last item of the list `/dev/ttyACM*`

import argparse
import functools
import glob
import locale
import os
import subprocess
import sys
import time
from typing import Any, Callable, Dict, List, Optional, Union

from dmppl.base import run, verb, dbg

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
        ret = "/dev/null" # Useful for debug.
        # TODO: raise OSError("Device not found. Use --help for details.")

    return ret
# }}} def getDevicePath

def uploadBitfile(bitfile): # {{{

    p = subprocess.run(("tinyprog", "-p", bitfile))

    return p.returncode
# }}} def uploadBitfile

def hwReadRegs(device, addrs:List[int]) -> Dict[int, int]: # {{{
    return {addr: 0 for addr in addrs}
# }}} def hwReadRegs

def hwWriteRegs(device, addrValues:Dict[int, int]) -> Dict[int, int]: # {{{
    return {addr: 0 for addr,value in addrValues.items()}
# }}} def hwWriteRegs

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

        waitTime = 2.5 # seconds
        verb("Waiting %0.01fs before connecting..." % waitTime, end='')
        # Allow OS time to enumerate USB before looking for device.
        time.sleep(waitTime)
        verb("Done")

    devicePath = getDevicePath(args.device)

    # Keep lock on device to prevent other processes from accidentally messing
    # with the state machine.
    verb("Connecting to device %s" % devicePath)
    with open(devicePath, "w+b") as device:
        rd:Callable = functools.partial(hwReadRegs, device)
        wr:Callable = functools.partial(hwWriteRegs, device)

        verb("Reading all register locations...", end='')
        regs128_init0:Dict[int, int] = rd(list(range(128)))
        verb("Done")

        verb("Writing ones to all register locations...", end='')
        regs128_init1:Dict[int, int] = wr({addr: 0xff for addr in range(128)})
        verb("Checking previous unchanged...", end='')
        assert all(value == regs128_init1[addr] \
                   for addr,value in regs128_init0.items())
        verb("Done")

        verb("Writing zeros to all register locations...", end='')
        regs128_ones:Dict[int, int] = wr({addr: 0 for addr in range(128)})
        verb("Done")

        verb("Reading all register locations...", end='')
        regs128_zeros:Dict[int, int] = rd(list(range(128)))
        verb("Checking writable bits...", end='')
        regs128_symdiff:Dict[int, int] = \
            {addr: (regs128_ones[addr] ^ regs128_zeros[addr]) \
             for addr in range(128)}
        verb("Done")

        # Increasing left-to-right and top-to-bottom.
        # Text of 16 lines of 8 bytes.
        print("Writable bits:")
        for i in range(16):
            base = i*8

            line = ' '.join("%02x" % regs128_symdiff[base + offset] \
                              for offset in range(8))

            print("  %3d .. %3d: %s" % (base, base+7, line))

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

