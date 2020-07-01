#!/usr/bin/env python3

# Correlator (USB Host Utility)
# Dave McEwan 2020-04-12
#
# Usage:
#   1. Plug in the board.
#   2. Program with `make prog` or with the `--prog` option of correlator-tui.
#   3. (optional) Experiment with correlator-tui to setup desired configuration.
#   4. Record correlation data for a number of windows:
#           correlator_record.py -o myData.out
#      This gives a binary file with each window represented by a fixed-size
#      packet (5B) which may be converted to human-readable text using the
#      option --txt <filepath>.
#
# After programming, the board presents itself as a USB serial device.
# The device to connect to is found using the first of these methods:
# 1. Argument `-d,--device`
# 2. Environment variable `$CORRELATOR_DEVICE`
# 3. The last item of the list `/dev/ttyACM*`

# Standard library
import argparse
import enum
import functools
import locale
import sys
import time
from typing import Any, Callable, Dict, Iterable, List, Optional, Union

# PyPI
import serial

from dmppl.base import run, verb, dbg
from dmppl.bytePipe import bpReadSequential, bpWriteSequential, \
    bpReadAddr, bpWriteAddr

from correlator_common import __version__, maxSampleRate_kHz, WindowShape, \
    getDevicePath, \
    HwReg, hwReadRegs, hwWriteRegs, \
    calc_bitsPerWindow, \
    argparse_positiveInteger, \
    argparse_WindowLengthExp, argparse_WindowShape, \
    argparse_SamplePeriodExp, argparse_SampleJitterExp


def record(device, args, hwRegs:Dict[HwReg, Any]) -> None: # {{{
    '''TODO
    - Display progress/status line.
    - Read up to 50 packets in each burst.
      - pktPerBurst = maxRdBurst // nBytesPerWindow
      - 50 = 255B // 5B
    - Update progress/status line after each burst.
    - Append to output after each burst.
    '''

    deviceName:str = device.name # TODO: Display as status. Report
    rdBytePipe:Callable = functools.partial(bpReadSequential, device)
    wrBytePipe:Callable = functools.partial(bpWriteSequential, device)
    rd:Callable = functools.partial(hwReadRegs, rdBytePipe)
    wr:Callable = functools.partial(hwWriteRegs, wrBytePipe)

    output = args.output
    nWindows:int = args.nWindows

    nBytesPerWindow:int = 5
    maxRdBurst:int = 255

    samplePeriod_cycles:int = 2**hwRegs[HwReg.SamplePeriodExp]
    samplePeriod_ms:float =  samplePeriod_cycles / float(maxSampleRate_kHz)
    sampleRate_kHz:float =  1.0 / samplePeriod_ms

    windowLength_samples:int = 2**hwRegs[HwReg.WindowLengthExp]
    windowPeriod_ms:float = windowLength_samples * samplePeriod_ms
    windowRate_kHz:float = 1.0 / windowPeriod_ms

    totalNSamples:int = nWindows * windowLength_samples
    totalNBytes:int = nWindows * nBytesPerWindow # TODO: Display as status
    totalTime_ms:int = nWindows * windowPeriod_ms # TODO: Display as status
    totalBitrate_kbps:float = (8 * totalNBytes) / (1000 * totalTime_ms) # TODO: Display as status

    nWindowPerBurst:int = maxRdBurst // nBytesPerWindow
    burstTime_ms:float = nWindowPerBurst * windowPeriod_ms
    nBytesPerBurst:int = nWindowPerBurst * nBytesPerWindow

    # <winNum> <countX> <countY> <countIsect> <countSymdiff>
    lineFmt = ' '.join(["%03d"]*5)

    ## TODO: Open output file, or STDOUT.
    ## TODO: wrLines() taking generator as input
    #if output is None:
    #    fd = sys.stdout
    #else:
    #    assert isinstance(output, str)
    #    assert 0 < len(output)
    #    fd = open(output, 'w')

    # Flush the packet fifo.
    wr({HwReg.PktfifoFlush: 1})

    #nWindowsRemaining_ = nWindows
    #while (0 < nWindowsRemaining_):
    #    nBytesThisWindow = min(nWindowsRemaining_ * nBytesPerWindow,
    #                           nBytesPerBurst)
    #    bs = bpReadAddr(device, HwReg.PktfifoRd.value, nBytesThisWindow)
    #    # TODO: Translate bs to output line.
    #    nWindowsRemaining_ -= nWindows

    #if fd != sys.stdout:
    #    fd.close()

    return # No return value
# }}} def record

# {{{ argparser

argparser = argparse.ArgumentParser(
    formatter_class = argparse.ArgumentDefaultsHelpFormatter
)

argparser.add_argument("-d", "--device",
    type=str,
    default=None,
    help="Serial device to connect to (immediately after programming)."
         " If None then try using environment variable `$CORRELATOR_DEVICE`;"
         " Then try using the last item of `/dev/ttyACM*`.")

argparser.add_argument("--init-windowLengthExp",
    type=argparse_WindowLengthExp,
    default=None,
    help="windowLength = 2**windowLengthExp  (samples)")

argparser.add_argument("--init-windowShape",
    type=argparse_WindowShape,
    default=None,
    help="Shape of sampling window function.")

argparser.add_argument("--init-samplePeriodExp",
    type=argparse_SamplePeriodExp,
    default=None,
    help="sampleRate = maxSampleRate * 2**-samplePeriodExp  (Hz)")

argparser.add_argument("--init-sampleJitterExp",
    type=argparse_SampleJitterExp,
    default=None,
    help="sampleJitter < 2**sampleJitterExp  (samples)")

argparser.add_argument("--prng-seed",
    type=int,
    default=None,
    help="Seed for xoshiro128+ PRNG used for sampling jitter.")

argparser.add_argument("-o", "--output",
    type=str,
    default="correlator.out",
    help="File to record data.")

argparser.add_argument("-n", "--nWindows",
    type=functools.partial(argparse_positiveInteger, "nWindows"),
    default=10,
    help="Number of windows to record.")

# }}} argparser

def main(args) -> int: # {{{
    '''
    1. Open connection to device.
    2. Read config RO registers.
    3. Write config RW registers if --init-* is used.
    4. Read/check config RW registers.
    5. Record data with burst reads from pktfifo.
    '''

    locale.setlocale(locale.LC_ALL, '')

    devicePath = getDevicePath(args.device)

    # Keep lock on device to prevent other processes from accidentally messing
    # with the state machine.
    verb("Connecting to device %s" % devicePath)
    with serial.Serial(devicePath, timeout=1.0, write_timeout=1.0) as device:
        rdBytePipe:Callable = functools.partial(bpReadSequential, device)
        wrBytePipe:Callable = functools.partial(bpWriteSequential, device)
        rd:Callable = functools.partial(hwReadRegs, rdBytePipe)
        wr:Callable = functools.partial(hwWriteRegs, wrBytePipe)

        verb("Reading RO registers...", end='')
        hwRegsRO:Dict[HwReg, Any] = rd((
            HwReg.MaxWindowLengthExp,
            HwReg.LogdropPrecision,
            HwReg.MaxSamplePeriodExp,
            HwReg.MaxSampleJitterExp,
        ))
        verb("Done")

        # Gather registers required for initialization.
        initRegsRW:Dict[HwReg, Any] = {}
        if args.init_windowLengthExp is not None:
            initRegsRW[HwReg.WindowLengthExp] = args.init_windowLengthExp
        if args.init_windowShape is not None:
            initRegsRW[HwReg.WindowShape] = args.init_windowShape
        if args.init_samplePeriodExp is not None:
            initRegsRW[HwReg.SamplePeriodExp] = args.init_samplePeriodExp
        if args.init_sampleJitterExp is not None:
            initRegsRW[HwReg.SampleJitterExp] = args.init_sampleJitterExp


        if 0 < len(initRegsRW):
            verb("Initializing RW registers...", end='')
            wr(initRegsRW)
            verb("Checking...", end='')
            hwRegsRW:Dict[HwReg, Any] = rd(initRegsRW.keys())
            assert all(initRegsRW[k] == v for k,v in hwRegsRW.items()), hwRegsRW
            verb("Done")


        if args.prng_seed is not None:
            seed:int = abs(args.prng_seed)
            verb("Initializing PRNG (xoshiro128+ %s)..." % hex(seed), end='')
            bpWriteAddr(device, HwReg.PrngSeed.value, 16, [0]*16)
            bpWriteAddr(device, HwReg.PrngSeed.value, 4, [
                (seed >> 3*8) & 0xff,
                (seed >> 2*8) & 0xff,
                (seed >> 1*8) & 0xff,
                (seed >> 0*8) & 0xff,
            ])
            verb("Done")


        verb("Reading RW registers...", end='')
        hwRegsRW:Dict[HwReg, Any] = rd([
            HwReg.WindowLengthExp,
            HwReg.WindowShape,
            HwReg.SamplePeriodExp,
            HwReg.SampleJitterExp,
        ])
        verb("Done")

        try:
            verb("Recording...")
            record(device, args, {**hwRegsRO, **hwRegsRW})
            verb("Recording Done")
        except KeyboardInterrupt:
            verb("KeyboardInterrupt. Exiting.")

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

