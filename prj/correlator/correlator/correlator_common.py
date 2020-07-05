
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
    WindowPrecision         = 6
    MaxSamplePeriodExp      = 7
    MaxSampleJitterExp      = 8

    # Dynamic, RW
    WindowLengthExp         = 9
    WindowShape             = 10
    SamplePeriodExp         = 11
    SampleJitterExp         = 12
    LedSource               = 13

# }}} Enum HwReg
mapHwAddrToHwReg:Dict[int, HwReg] = {e.value: e for e in HwReg}

@enum.unique
class WindowShape(enum.Enum): # {{{
    Rectangular = 0
    Logdrop     = 1
# }}} class WindowShape

@enum.unique
class LedSource(enum.Enum): # {{{
    WinNum          = 0
    X               = 1
    Y               = 2
    Isect           = 3
    Symdiff         = 4
    # NOTE: No unicode in enum names.
    Cov             = 5
    Dep             = 6
    Ham             = 7
# }}} class LedSource

mapHwRegToEnum = {
    HwReg.WindowShape:  WindowShape,
    HwReg.LedSource:    LedSource,
}

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

def hwReadRegs(rd, keys:Iterable[HwReg]) -> Dict[HwReg, Any]: # {{{
    '''Wrapper for reader function including checks and type conversion.

    Reader function must take an iterable of integers representing address,
    and return an iterable of (addr, value) pairs.
    rd :: [int] -> [(int, int)]
    '''
    values = rd([k.value for k in keys])
    assert len(keys) == len(values)

    ret_ = {}
    for k,(a,v) in zip(keys, values):
        assert isinstance(k, HwReg), k
        assert isinstance(a, int), a
        assert isinstance(v, int), v
        assert a == k.value, (a, k.value)

        if k in mapHwRegToEnum.keys():
            ret_[k] = mapHwRegToEnum[k](v)
        else:
            ret_[k] = v

    return ret_
# }}} def hwReadRegs

def hwWriteRegs(wr, keyValues:Dict[HwReg, Any]) -> Dict[HwReg, Any]: # {{{
    '''Wrapper for writer function including checks and type conversion.

    Writer function must take an iterable of (addr, value) pairs,
    and return an iterable of (addr, value) pairs.
    wr :: [(int, int)] -> [(int, int)]
    '''

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

    precision:int = hwRegs[HwReg.WindowPrecision] # bits
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

def argparse_LedSource(s): # {{{

    sClean = s.encode("ascii", "ignore").decode("ascii").casefold()

    try:
        i = int(sClean)
        if not (0 <= i <= 7):
            msg = "LED source must be in [0, 7]"
            raise argparse.ArgumentTypeError(msg)

    except ValueError:
        mapNameToInt = {e.name.casefold(): e.value for e in LedSource}

        if sClean not in mapNameToInt.keys():
            allowedNames = ','.join(e.name for e in LedSource)
            msg = "LED source must be in {%s}" % allowedNames
            raise argparse.ArgumentTypeError(msg)

        i = mapNameToInt[sClean]

    return LedSource(i)
# }}} def argparse_LedSource

def argparse_positiveInteger(nm, s): # {{{
    i = int(s)
    if not (0 < i):
        msg = "%s must be positive integer" % nm
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_positiveInteger

def argparse_nonNegativeInteger(nm, s): # {{{
    i = int(s)
    if not (0 <= i):
        msg = "%s must be non-negative integer" % nm
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_nonNegativeInteger

def argparse_positiveReal(nm, s): # {{{
    i = float(s)
    if not (0.0 < i):
        msg = "%s must be positive real/float" % nm
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_positiveReal

def argparse_nonNegativeReal(nm, s): # {{{
    i = float(s)
    if not (0.0 <= i):
        msg = "%s must be non-negative real/float" % nm
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparse_nonNegativeReal

