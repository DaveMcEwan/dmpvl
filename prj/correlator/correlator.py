#!/usr/bin/env python3

# Correlator (USB Host Utility)
# Dave McEwan 2020-04-12
#
# Plug in the board then run like:
#    correlator.py &
#
# A bitfile implementing the correlator logic is required to be build from
# the SystemVerilog2005 implementation
# The bitfile to immediately program the board with is found using the first of
# these methods:
# 1. Argument `-b,--bitfile`
# 2. Environment variable `$CORRELATOR_BITFILE`
# 3. The last item of the list `./correlator.*.bin`
# 4. './correlator.bin`
#
# After programming, the board presents itself as a USB serial device.
# The device to connect to is found using the first of these methods:
# 1. Argument `-d,--device`
# 2. Environment variable `$CORRELATOR_DEVICE`
# 3. The last item of the list `/dev/ttyACM*`

# Standard library
import argparse
import curses
import enum
import functools
import glob
import locale
import os
import subprocess
import sys
import time
from typing import Any, Callable, Dict, Iterable, List, Optional, Union

# PyPI
import serial

from dmppl.base import run, verb, dbg
from dmppl.bytePipe import BpAddrs, BpAddrValues, BpMem, \
    bpReadSequential, bpWriteSequential, bpPrintMem, bpAddrValuesToMem
from dmppl.color import CursesWindow, cursesInitPairs, \
    whiteBlue, whiteRed, greenBlack

__version__ = "0.1.0"

maxSampleRate_kHz:int = 48000

# NOTE: Must match dmpvl/prj/correlator/bpReg.v
@enum.unique
class HwReg(enum.Enum): # {{{
    # Static, RO
    Precision               = 0
    MetricA                 = 1
    MetricB                 = 2
    MaxNInputs              = 3
    MaxWindowLengthExp      = 4
    MaxSampleRateNegExp     = 5
    MaxSampleJitterNegExp   = 6

    # Dynamic, RW
    NInputs                 = 7
    WindowLengthExp         = 8
    WindowShape             = 9
    SampleRateNegExp        = 10
    SampleMode              = 11
    SampleJitterNegExp      = 12
# }}} Enum HwReg
mapHwAddrToHwReg:Dict[int, HwReg] = {e.value: e for e in HwReg}

@enum.unique
class WindowShape(enum.Enum): # {{{
    Rectangular = 0
    Logdrop     = 1
# }}} class WindowShape

@enum.unique
class SampleMode(enum.Enum): # {{{
    NonJitter   = 0
    NonPeriodic = 1
# }}} class SampleMode

@enum.unique
class UpdateMode(enum.Enum): # {{{
    Batch       = enum.auto()
    Interactive = enum.auto()
# }}} class UpdateMode

@enum.unique
class GuiReg(enum.Enum): # {{{
    # Software-only
    UpdateMode      = enum.auto()

    # Derived from hardware
    NInputs         = enum.auto()
    WindowLength    = enum.auto()
    WindowShape     = enum.auto()
    SampleRate      = enum.auto()
    SampleMode      = enum.auto()
    SampleJitter    = enum.auto()
# }}} Enum GuiReg

@enum.unique
class KeyAction(enum.Enum): # {{{
    NavigateUp          = enum.auto()
    NavigateDown        = enum.auto()
    ModifyIncrease      = enum.auto()
    ModifyDecrease      = enum.auto()
    SendUpdate          = enum.auto()
    Quit                = enum.auto()
# }}} Enum KeyAction

listGuiReg:List[GuiReg] = list(r for i,r in enumerate(GuiReg))

# NOTE: Some values are carefully updated with string substitution on the
# initial read of the RO registers.
mapGuiRegToDomain_:Dict[GuiReg, str] = { # {{{
    # Controls no hardware register (GUI state only).
    GuiReg.UpdateMode: "∊ {%s}" % ", ".join(m.name for m in UpdateMode),

    # Controls register "NInputs".
    # Domain defined by HwReg.MaxNInputs
    GuiReg.NInputs: "∊ ℤ ∩ [2, %d]",

    # Controls register "WindowLengthExp".
    # Domain defined by HwReg.MaxWindowLengthExp
    GuiReg.WindowLength: "(samples) = 2**w; w ∊ ℤ ∩ [1, %d]",

    # Controls register "WindowShape".
    GuiReg.WindowShape: "∊ {%s}" % ", ".join(s.name for s in WindowShape),

    # Controls register "SampleRateNegExp".
    # Domain defined by HwReg.MaxSampleRateNegExp
    GuiReg.SampleRate: "(kHz) = %d/2**r; r ∊ ℤ ∩ [0, %%d]" % maxSampleRate_kHz,

    # Controls register "SampleMode".
    GuiReg.SampleMode: "∊ {%s}" % ", ".join(m.name for m in SampleMode),

    # Controls register "SampleJitterNegExp".
    # Domain defined by HwReg.MaxSampleJitterNegExp
    GuiReg.SampleJitter: "(samples) = WindowLength/2**j; j ∊ ℤ ∩ [1, %d]",
} # }}}

mapMetricIntToStr:Dict[int, str] = { # {{{
    1: "Ċls",
    2: "Ċos",
    3: "Ċov",
    4: "Ḋep",
    5: "Ḣam",
    6: "Ṫmt",
} # }}}

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

        if HwReg.SampleMode == k:
            ret_[k] = SampleMode.NonJitter \
                if 0 == v else \
                SampleMode.NonPeriodic
        elif HwReg.WindowShape == k:
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

def hwRegsToGuiRegs(hwRegs:Dict[HwReg, Any]) -> Dict[GuiReg, Any]: # {{{

    windowLength:int = 2**hwRegs[HwReg.WindowLengthExp]

    sampleJitter:Optional[int] = None \
        if hwRegs[HwReg.SampleMode] == SampleMode.NonJitter else \
        (windowLength // 2**hwRegs[HwReg.SampleJitterNegExp])

    sampleRate = float(maxSampleRate_kHz) / 2**hwRegs[HwReg.SampleRateNegExp]

    ret = {
        GuiReg.NInputs:      hwRegs[HwReg.NInputs],
        GuiReg.WindowLength: windowLength,
        GuiReg.WindowShape:  hwRegs[HwReg.WindowShape],
        GuiReg.SampleRate:   sampleRate,
        GuiReg.SampleMode:   hwRegs[HwReg.SampleMode],
        GuiReg.SampleJitter: '-' if sampleJitter is None else sampleJitter,
    }
    return ret
# }}} def hwRegsToGuiRegs

def updateRegs(selectIdx:int,
               guiRegs_:Dict[GuiReg, Any],
               hwRegs_:Dict[HwReg, Any],
               decrNotIncr:bool) -> None: # {{{
    '''Update state in guiRegs_ and hwRegs_ in response to keypress.
    '''
    gr:GuiReg = listGuiReg[selectIdx]

    if GuiReg.UpdateMode == gr:
        guiRegs_[GuiReg.UpdateMode] = UpdateMode.Interactive \
            if UpdateMode.Batch == guiRegs_[GuiReg.UpdateMode] else \
            UpdateMode.Batch

    elif GuiReg.NInputs == gr:
        n = hwRegs_[HwReg.NInputs]
        m = (n-1) if decrNotIncr else (n+1)
        lo, hi = 2, hwRegs_[HwReg.MaxNInputs]
        hwRegs_[HwReg.NInputs] = max(lo, min(m, hi))

    elif GuiReg.WindowLength == gr:
        n = hwRegs_[HwReg.WindowLengthExp]
        m = (n-1) if decrNotIncr else (n+1)
        lo, hi = 1, hwRegs_[HwReg.MaxWindowLengthExp]
        hwRegs_[HwReg.WindowLengthExp] = max(lo, min(m, hi))

    elif GuiReg.WindowShape == gr:
        hwRegs_[HwReg.WindowShape] = WindowShape.Rectangular \
            if WindowShape.Logdrop == hwRegs_[HwReg.WindowShape] else \
            WindowShape.Logdrop

    elif GuiReg.SampleRate == gr:
        n = hwRegs_[HwReg.SampleRateNegExp]
        m = (n+1) if decrNotIncr else (n-1)
        lo, hi = 0, hwRegs_[HwReg.MaxSampleRateNegExp]
        hwRegs_[HwReg.SampleRateNegExp] = max(lo, min(m, hi))

    elif GuiReg.SampleMode == gr:
        hwRegs_[HwReg.SampleMode] = SampleMode.NonPeriodic \
            if SampleMode.NonJitter == hwRegs_[HwReg.SampleMode] else \
            SampleMode.NonJitter

    elif GuiReg.SampleJitter == gr and \
         guiRegs_[GuiReg.SampleMode] == SampleMode.NonPeriodic:
        n = hwRegs_[HwReg.SampleJitterNegExp]
        m = (n+1) if decrNotIncr else (n-1)
        lo, hi = 1, hwRegs_[HwReg.MaxSampleJitterNegExp]
        hwRegs_[HwReg.SampleJitterNegExp] = max(lo, min(m, hi))

    else:
        pass

    guiRegs_.update(hwRegsToGuiRegs(hwRegs_))

    return
# }}} def updateRegs

class FullWindow(CursesWindow): # {{{
    '''The "full" window is a rectangle in the middle of the screen.

    +----------- ... -------------+
    |Title...                     |
    |                             |
    | inputs/parameters           |
    |                             |
    ...                         ...
    |                             |
    | outputs/results             |
    |                             |
    |Status...                    |
    +----------- ... -------------+
    '''
    def drawTitle(self, deviceName, hwRegs) -> None: # {{{
        '''Draw the static title section.
        Intended to be called only once.

        <appName> ... <precision> <metricA> <metricB> ... <devicePath>
        '''

        appName:str = "Correlator"
        devicePath:str = deviceName
        precision:str = "%db" % hwRegs[HwReg.Precision]
        metricA:str = mapMetricIntToStr[hwRegs[HwReg.MetricA]]
        metricB:str = mapMetricIntToStr[hwRegs[HwReg.MetricB]]

        left:str = appName
        mid:str = ' '.join((precision, metricA, metricB))
        right:str = devicePath

        midBegin:int = (self.nChars // 2) - (len(mid) // 2)
        rightBegin:int = self.charRight - len(right) + 1

        # Fill whole line with background.
        self.drawStr(" "*self.charsWidth)

        self.drawStr(left)
        self.drawStr(mid, midBegin)
        self.drawStr(right, rightBegin)

        return # No return value
    # }}} def drawTitle

    def drawStatus(self) -> None: # {{{
        '''Draw/redraw the status section.

        Up/Down: Move ... Left/Right: Change ... Enter: Send
        '''

        left:str = "Up/Down: Navigate"
        mid:str = "Left/Right: Modify"
        right:str = "Enter: Send Update"

        midBegin:int = (self.nChars // 2) - (len(mid) // 2)
        rightBegin:int = self.charRight - len(right) + 1

        # Fill whole line with background.
        self.drawStr(" "*self.charsWidth, y=self.lineBottom)

        self.drawStr(left, y=self.lineBottom)
        self.drawStr(mid, midBegin, y=self.lineBottom)
        self.drawStr(right, rightBegin, y=self.lineBottom)

        return # No return value
    # }}} def drawStatus
# }}} class FullWindow

class InputWindow(CursesWindow): # {{{
    '''The "inpt" window contains a list of parameters with their values.

    The user can modify values using the left/right arrow keys.
    No box.
    Asterisk at topLeft indicates if display is up to date with hardware.

    +----------- ... -------------+
    |label0     value0     domain0|
    |label1     value1     domain1|
    ...                         ...
    |labelN     valueN     domainN|
    +----------- ... -------------+
    '''
    def draw(self,
                   guiRegs:Dict[GuiReg, Any],
                   selectIdx:int=0,
                   outstanding:bool=False) -> None: # {{{
        '''Draw all the parameter lines.

        <label> ... <value> ... <domain>
        '''

        maxLenName:int = max(len(r.name) for r in GuiReg)

        self.win.clear()

        for i,(r,d) in enumerate(mapGuiRegToDomain_.items()):
            nm:str = r.name

            left:str = ' '*(maxLenName - len(nm)) + nm + " = "
            right:str = d

            v = guiRegs[r]
            if isinstance(v, str):
              mid = v
            elif isinstance(v, bool):
              mid = "True" if v else "False"
            elif isinstance(v, int):
              mid = "%d" % v
            elif isinstance(v, float):
              mid = "%0.5f" % v
            elif isinstance(v, enum.Enum):
              mid = v.name
            else:
              mid = str(v)

            midBegin:int = len(left) + 2
            rightBegin:int = 30

            # Fill whole line with background.
            self.drawStr(' '*self.charsWidth, y=i+1)

            self.drawStr(left, y=i+1)
            self.drawStr(mid, midBegin, y=i+1,
                attr=(curses.A_REVERSE if i == selectIdx else curses.A_NORMAL))
            self.drawStr(right, rightBegin, y=i+1)

        if outstanding:
            ready:str = "*ready*"
            self.win.addstr(1, self.charRight-len(ready),
                            ready, curses.color_pair(whiteRed))

        return # No return value
    # }}} def draw
# }}} class InputWindow

def gui(scr, deviceName, rd, wr, hwRegs): # {{{
    '''
    Window objects:
    - scr: All available screen space.
    - full: Rectangle in the centre of scr.
    - inpt: Rectangle below title for dynamic inputs.
    - otpt: Rectangle above status for dynamic outputs (unimplemented).

    Each of the window objects is refreshed individually.
    '''

    guiRegs_:Dict[GuiReg, Any] = hwRegsToGuiRegs(hwRegs)
    guiRegs_.update({GuiReg.UpdateMode: UpdateMode.Batch})
    assert all(k in guiRegs_.keys() for k in GuiReg)
    selectIdx_ = 0
    outstanding_ = False
    hwRegs_ = hwRegs

    curses.curs_set(0) # Hide the cursor.
    cursesInitPairs() # Initialize colors

    full:CursesWindow = FullWindow(scr,
        nLines=len(GuiReg)+6, nChars=80,
        colorPair=whiteBlue)
    full.win.box()
    full.drawTitle(deviceName, hwRegs)
    full.drawStatus()
    full.win.refresh()

    inpt:CursesWindow = InputWindow(full.win,
        nLines=len(GuiReg)+2, nChars=full.nChars-2,
        colorPair=greenBlack,
        beginY=full.lineTop+1, beginX=1)
    inpt.draw(guiRegs_)
    inpt.win.keypad(True)
    inpt.win.refresh()

    while 1:
        c = inpt.win.getch() # Calls refresh for this and derived windows.

        # Map keypress/character to action.
        if curses.KEY_UP == c and 0 < selectIdx_:
            keyAction:KeyAction = KeyAction.NavigateUp
        elif curses.KEY_DOWN == c and (len(GuiReg)-1) > selectIdx_:
            keyAction:KeyAction = KeyAction.NavigateDown
        elif curses.KEY_LEFT == c:
            keyAction:KeyAction = KeyAction.ModifyDecrease
        elif curses.KEY_RIGHT == c:
            keyAction:KeyAction = KeyAction.ModifyIncrease
        elif curses.KEY_ENTER == c or ord('\n') == c:
            keyAction:KeyAction = KeyAction.SendUpdate
        elif ord('q') == c or ord('Q') == c:
            keyAction:KeyAction = KeyAction.Quit
        else:
            continue

        # Change states according to action.
        if keyAction == KeyAction.NavigateUp:
            selectIdx_ -= 1
        elif keyAction == KeyAction.NavigateDown:
            selectIdx_ += 1
        elif keyAction == KeyAction.ModifyDecrease:
            updateRegs(selectIdx_, guiRegs_, hwRegs_, True)
        elif keyAction == KeyAction.ModifyIncrease:
            updateRegs(selectIdx_, guiRegs_, hwRegs_, False)
        elif keyAction == KeyAction.Quit:
            break
        else:
            pass

        # Send updates to hardware and readback to ensure display matches the
        # actual values reported from hardware.
        if guiRegs_[GuiReg.UpdateMode] == UpdateMode.Interactive or \
           keyAction == KeyAction.SendUpdate:
            _ = wr(hwRegs_)
            hwRegs_:Dict[HwReg, Any] = rd(hwRegs_.keys())
            guiRegs_.update(hwRegsToGuiRegs(hwRegs_))
            outstanding_ = False
        elif guiRegs_[GuiReg.UpdateMode] == UpdateMode.Batch and \
           keyAction in (KeyAction.ModifyDecrease, KeyAction.ModifyIncrease):
            outstanding_ = True
        else:
            pass

        # Update display.
        inpt.draw(guiRegs_, selectIdx_, outstanding_)
        inpt.win.refresh()

    return # No return value
# }}} def gui

# {{{ argparser

argparser = argparse.ArgumentParser(
    formatter_class = argparse.ArgumentDefaultsHelpFormatter
)

argparser.add_argument("-b", "--bitfile",
    type=str,
    default=None,
    help="Bitfile for FPGA implementing correlator hardware."
         " If None then try using environment variable `$CORRELATOR_BITFILE`;"
         " Then try using the last item of `./correlator.*.bin`;"
         " Then try using the bundled bitfile.")

argparser.add_argument("--no-prog",
    action="store_true",
    help="Don't attempt to program a bitfile."
         " Assume there's already a programmed device available.")

argparser.add_argument("-d", "--device",
    type=str,
    default=None,
    help="Serial device to connect to (immediately after progrmming)."
         " If None then try using environment variable `$CORRELATOR_DEVICE`;"
         " Then try using the last item of `/dev/ttyACM*`.")

def argparseNInputs(s): # {{{
    i = int(s)
    if not (2 <= i <= 99):
        msg = "Number of active inputs must be in [2, maxNInputs]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparseNInputs
argparser.add_argument("--init-nInputs",
    type=argparseNInputs,
    default=2,
    help="Number of inputs to calculate correlation between.")

def argparseWindowLengthExp(s): # {{{
    i = int(s)
    if not (0 <= i <= 99):
        msg = "Window length exponent must be in [2, maxWindowLengthExp]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparseWindowLengthExp
argparser.add_argument("--init-windowLengthExp",
    type=argparseWindowLengthExp,
    default=10,
    help="windowLength = 2**windowLengthExp  (samples)")

def argparseWindowShape(s): # {{{
    i = s.lower()
    if "rectangular" == i:
        ret = WindowShape.Rectangular
    elif "logdrop" == i:
        ret = WindowShape.Logdrop
    else:
        msg = "Window shape must be in {RECTANGULAR, LOGDROP}"
        raise argparse.ArgumentTypeError(msg)
    return ret
# }}} def argparseWindowShape
argparser.add_argument("--init-windowShape",
    type=argparseWindowShape,
    default=WindowShape.Rectangular,
    help="Shape of sampling window function.")

def argparseSampleRateNegExp(s): # {{{
    i = int(s)
    if not (0 <= i <= 99):
        msg = "Sample rate divisor exponent must be in [0, maxSampleRateNegExp]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparseSampleRateNegExp
argparser.add_argument("--init-sampleRateNegExp",
    type=argparseSampleRateNegExp,
    default=0,
    help="sampleRate = maxSampleRate * 2**-sampleRateNegExp  (Hz)")

def argparseSampleMode(s): # {{{
    i = s.lower()
    if "nonjitter" == i:
        ret = SampleMode.NonJitter
    elif "nonperiodic" == i:
        ret = SampleMode.NonPeriodic
    else:
        msg = "Sample mode must be in {PERIODIC, NONPERIODIC}"
        raise argparse.ArgumentTypeError(msg)
    return ret
# }}} def argparseSampleMode
argparser.add_argument("--init-sampleMode",
    type=argparseSampleMode,
    default=SampleMode.NonJitter,
    help="Sample periodically or non-periodically (using pseudo-random jitter)")

def argparseSampleJitterNegExp(s): # {{{
    i = int(s)
    if not (1 <= i <= 99):
        msg = "Sample rate divisor exponent must be in [1, maxSampleJitterNegExp]"
        raise argparse.ArgumentTypeError(msg)
    return i
# }}} def argparseSampleJitterNegExp
argparser.add_argument("--init-sampleJitterNegExp",
    type=argparseSampleJitterNegExp,
    default=1,
    help="sampleJitter = windowLength * 2**-sampleJitterNegExp  (samples)")

# }}} argparser

def main(args) -> int: # {{{
    '''
    1. Upload bitfile to FPGA.
    2. Open connection to device.
    3. Read config RO registers.
    4. Write config RW registers.
    5. Read/check config RW registers.
    6. Initialize GUI
    7. GUI output loop:
        1. Sleep for refresh period.
        2. Read results RO registers.
        2. Update results section.
    8. GUI config loop:
        1. Wait for <Enter>
        2. Write config RW registers.
        3. Read config RW registers, check they're what was written.
    9. GUI input loop:
        1. Wait for keypress.
        2. Handle keypress by moving highlighted line or changing value.
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
        rdBytePipe:Callable = functools.partial(bpReadSequential, device)
        wrBytePipe:Callable = functools.partial(bpWriteSequential, device)
        rd:Callable = functools.partial(hwReadRegs, rdBytePipe)
        wr:Callable = functools.partial(hwWriteRegs, wrBytePipe)

        verb("Reading RO registers...", end='')
        hwRegsRO:Dict[HwReg, Any] = rd((HwReg.Precision,
                     HwReg.MetricA,
                     HwReg.MetricB,
                     HwReg.MaxNInputs,
                     HwReg.MaxWindowLengthExp,
                     HwReg.MaxSampleRateNegExp,
                     HwReg.MaxSampleJitterNegExp))
        verb("Done")

        # Fill in missing values of parameter domains.
        mapGuiRegToDomain_.update({
            GuiReg.NInputs: mapGuiRegToDomain_[GuiReg.NInputs] %
                hwRegsRO[HwReg.MaxNInputs],
            GuiReg.WindowLength: mapGuiRegToDomain_[GuiReg.WindowLength] %
                hwRegsRO[HwReg.MaxWindowLengthExp],
            GuiReg.SampleRate: mapGuiRegToDomain_[GuiReg.SampleRate] %
                hwRegsRO[HwReg.MaxSampleRateNegExp],
            GuiReg.SampleJitter: mapGuiRegToDomain_[GuiReg.SampleJitter] %
                hwRegsRO[HwReg.MaxSampleJitterNegExp],
        })

        verb("Initializing RW registers...", end='')
        initRegsRW:Dict[HwReg, Any] = {
            HwReg.NInputs:              args.init_nInputs,
            HwReg.WindowLengthExp:      args.init_windowLengthExp,
            HwReg.WindowShape:          args.init_windowShape,
            HwReg.SampleRateNegExp:     args.init_sampleRateNegExp,
            HwReg.SampleMode:           args.init_sampleMode,
            HwReg.SampleJitterNegExp:   args.init_sampleJitterNegExp,
        }
        wr(initRegsRW)
        verb("Checking...", end='')
        hwRegsRW:Dict[HwReg, Any] = rd(initRegsRW.keys())
        assert all(initRegsRW[k] == v for k,v in hwRegsRW.items()), hwRegsRW
        verb("Done")

        try:
            verb("Starting GUI (curses)...")
            curses.wrapper(gui, device.name, rd, wr, {**hwRegsRO, **hwRegsRW})
            verb("GUI Done")
        except KeyboardInterrupt:
            verb("KeyboardInterrupt. Exiting.")

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

