
# Standard library
import argparse
import enum
import glob
import os
import subprocess
from typing import Any, Callable, Dict, Iterable, List, Optional, Union

from dmppl.bytePipe import BpAddrs, BpAddrValues, BpMem, \
    bpReadSequential, bpWriteSequential, bpPrintMem, bpAddrValuesToMem, \
    bpWriteAddr

__version__ = "0.1.0"

maxSampleRate_kHz:int = 48000

# NOTE: Must match addresses in bpReg.v
@enum.unique
class HwReg(enum.Enum): # {{{
    # Rfifo
    PktfifoRd               = 1

    # WO
    PktfifoFlush            = 2
    PrngSeed                = 3

    # Static, RO
    PktfifoDepth            = 4
    MaxWindowLengthExp      = 5
    LogdropPrecision        = 6
    MaxSamplePeriodExp      = 7
    MaxSampleJitterExp      = 8

    # Dynamic, RW
    WindowLengthExp         = 9
    WindowShape             = 10
    SamplePeriodExp         = 11
    SampleJitterExp         = 12

# }}} Enum HwReg
mapHwAddrToHwReg:Dict[int, HwReg] = {e.value: e for e in HwReg}

@enum.unique
class WindowShape(enum.Enum): # {{{
    Rectangular = 0
    Logdrop     = 1
# }}} class WindowShape

def getBitfilePath(argBitfile) -> str: # {{{

    envBitfile = os.environ.get("CORRELATOR_BITFILE")
    orderedBitfiles = sorted(glob.glob("correlator.*.bin"))

    if argBitfile is not None:
        ret = argBitfile
    elif envBitfile is not None:
        ret = envBitfile
    elif len(orderedBitfiles) > 0:
        ret = orderedBitfiles[-1]
    else:
        ret = os.sep.join((os.path.dirname(os.path.abspath(__file__)),
                           "correlator.bin"))

    return ret
# }}} def getBitfilePath

def getDevicePath(argDevice) -> str: # {{{

    envDevice = os.environ.get("CORRELATOR_DEVICE")
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

def hwReadRegs(rd, keys:Iterable[int]) -> Dict[HwReg, Any]: # {{{
    values = rd([k.value for k in keys])
    assert len(keys) == len(values)

    ret_ = {}
    for k,(a,v) in zip(keys, values):
        assert isinstance(k, HwReg), k
        assert isinstance(a, int), a
        assert isinstance(v, int), v
        assert a == k.value, (a, k.value)

        if HwReg.WindowShape == k:
            ret_[k] = WindowShape.Rectangular \
                if 0 == v else \
                WindowShape.Logdrop
        else:
            ret_[k] = v

    return ret_
# }}} def hwReadRegs

def hwWriteRegs(wr, keyValues:Dict[HwReg, Any]): # {{{

    addrValues_ = []
    for k,v in keyValues.items():
        addr = k.value

        if isinstance(v, enum.Enum):
            addrValues_.append((addr, v.value))
        else:
            assert isinstance(v, int), v
            addrValues_.append((addr, v))

    ret = wr(addrValues_)

    return ret
# }}} def hwWriteRegs

def calc_bitsPerWindow(hwRegs:Dict[HwReg, Any]) -> int: # {{{

    precision:int = hwRegs[HwReg.LogdropPrecision] # bits
    nInputs:int = 2 # unitless

    ret:int = precision * (nInputs**2 - nInputs)

    return ret
# }}} def calc_bitsPerWindow

def argparse_WindowLengthExp(s): # {{{
    i = int(s)
    if not (0 <= i <= 99):
        msg = "Window length exponent must be in [2, maxWindowLengthExp]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_WindowLengthExp

def argparse_WindowShape(s): # {{{
    i = s.lower()
    if "rectangular" == i:
        ret = WindowShape.Rectangular
    elif "logdrop" == i:
        ret = WindowShape.Logdrop
    else:
        msg = "Window shape must be in {RECTANGULAR, LOGDROP}"
        raise argparse.ArgumentTypeError(msg)
    return ret
# }}} def argparse_WindowShape

def argparse_SamplePeriodExp(s): # {{{
    i = int(s)
    if not (0 <= i <= 99):
        msg = "Sample rate divisor exponent must be in [0, maxSamplePeriodExp]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_SamplePeriodExp

def argparse_SampleJitterExp(s): # {{{
    i = int(s)
    if not (0 <= i <= 99):
        msg = "Sample jitter exponent must be in [0, maxSampleJitterExp)"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_SampleJitterExp

