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
import locale
import sys
import time
from typing import Any, Callable, Dict, Iterable, List, Optional, Union

# PyPI
import serial

from dmppl.base import run, verb, dbg
from dmppl.bytePipe import bpReadSequential, bpWriteSequential, bpWriteAddr
from dmppl.color import CursesWindow, cursesInitPairs, \
    whiteBlue, whiteRed, greenBlack, yellowBlack

from correlator_common import __version__, maxSampleRate_kHz, \
    WindowShape, LedSource, \
    getBitfilePath, getDevicePath, uploadBitfile, \
    HwReg, hwReadRegs, hwWriteRegs, \
    calc_bitsPerWindow, \
    argparse_nonNegativeReal, \
    argparse_WindowLengthExp, argparse_WindowShape, \
    argparse_SamplePeriodExp, argparse_SampleJitterExp, \
    argparse_LedSource


@enum.unique
class UpdateMode(enum.Enum): # {{{
    Batch       = enum.auto()
    Interactive = enum.auto()
# }}} class UpdateMode

@enum.unique
class TuiReg(enum.Enum): # {{{
    # Software-only
    UpdateMode      = enum.auto()

    # Derived from hardware
    WindowLength    = enum.auto()
    WindowShape     = enum.auto()
    SampleRate      = enum.auto()
    SampleJitter    = enum.auto()
    LedSource       = enum.auto()
# }}} Enum TuiReg

@enum.unique
class KeyAction(enum.Enum): # {{{
    NavigateUp          = enum.auto()
    NavigateDown        = enum.auto()
    ModifyIncrease      = enum.auto()
    ModifyDecrease      = enum.auto()
    SendUpdate          = enum.auto()
    Quit                = enum.auto()
# }}} Enum KeyAction

listTuiReg:List[TuiReg] = list(r for i,r in enumerate(TuiReg))

# NOTE: Some values are carefully updated with string substitution on the
# initial read of the RO registers.
mapTuiRegToDomain_:Dict[TuiReg, str] = { # {{{
    # Controls no hardware register (TUI state only).
    TuiReg.UpdateMode: "∊ {%s}" % ", ".join(m.name for m in UpdateMode),

    # Controls register "WindowLengthExp".
    # Domain defined by HwReg.MaxWindowLengthExp
    TuiReg.WindowLength: "(samples) = 2**w; w ∊ ℤ ∩ [3, %d]",

    # Controls register "WindowShape".
    TuiReg.WindowShape: "∊ {%s}" % ", ".join(s.name for s in WindowShape),

    # Controls register "SamplePeriodExp".
    # Domain defined by HwReg.MaxSamplePeriodExp
    TuiReg.SampleRate: "(kHz) = %d/2**r; r ∊ ℤ ∩ [0, %%d]" % maxSampleRate_kHz,

    # Controls register "SampleJitterExp".
    # Domain defined by HwReg.MaxSampleJitterExp
    TuiReg.SampleJitter: "(cycles) < 2**j; j ∊ ℤ ∩ [0, %d)",

    # Controls register "LedSource".
    TuiReg.LedSource: "∊ {%s}" % ", ".join(s.name for s in LedSource),
} # }}}

def hwRegsToTuiRegs(hwRegs:Dict[HwReg, Any]) -> Dict[TuiReg, Any]: # {{{

    windowLength:int = 2**hwRegs[HwReg.WindowLengthExp]

    sampleRate = float(maxSampleRate_kHz) / 2**hwRegs[HwReg.SamplePeriodExp]

    sampleJitter:Optional[int] = 2**hwRegs[HwReg.SampleJitterExp]

    ret = {
        TuiReg.WindowLength: windowLength,
        TuiReg.WindowShape:  hwRegs[HwReg.WindowShape],
        TuiReg.SampleRate:   sampleRate,
        TuiReg.SampleJitter: sampleJitter,
        TuiReg.LedSource:    hwRegs[HwReg.LedSource],
    }
    return ret
# }}} def hwRegsToTuiRegs

def updateRegs(selectIdx:int,
               tuiRegs_:Dict[TuiReg, Any],
               hwRegs_:Dict[HwReg, Any],
               decrNotIncr:bool) -> None: # {{{
    '''Update state in tuiRegs_ and hwRegs_ in response to keypress.
    '''
    gr:TuiReg = listTuiReg[selectIdx]

    if TuiReg.UpdateMode == gr:
        tuiRegs_[TuiReg.UpdateMode] = UpdateMode.Interactive \
            if UpdateMode.Batch == tuiRegs_[TuiReg.UpdateMode] else \
            UpdateMode.Batch

    elif TuiReg.WindowLength == gr:
        n = hwRegs_[HwReg.WindowLengthExp]
        m = (n-1) if decrNotIncr else (n+1)
        lo, hi = 3, hwRegs_[HwReg.MaxWindowLengthExp]
        hwRegs_[HwReg.WindowLengthExp] = max(lo, min(m, hi))

    elif TuiReg.WindowShape == gr:
        hwRegs_[HwReg.WindowShape] = WindowShape.Rectangular \
            if WindowShape.Logdrop == hwRegs_[HwReg.WindowShape] else \
            WindowShape.Logdrop

    elif TuiReg.SampleRate == gr:
        n = hwRegs_[HwReg.SamplePeriodExp]
        m = (n+1) if decrNotIncr else (n-1)
        lo, hi = 0, hwRegs_[HwReg.MaxSamplePeriodExp]
        hwRegs_[HwReg.SamplePeriodExp] = max(lo, min(m, hi))

    elif TuiReg.SampleJitter == gr:
        n = hwRegs_[HwReg.SampleJitterExp]
        m = (n-1) if decrNotIncr else (n+1)
        lo, hi = 0, hwRegs_[HwReg.MaxSampleJitterExp]-1
        hwRegs_[HwReg.SampleJitterExp] = max(lo, min(m, hi))

    elif TuiReg.LedSource == gr:
        n = hwRegs_[HwReg.LedSource].value
        m = (n-1) if decrNotIncr else (n+1)
        lo, hi = 0, 7
        hwRegs_[HwReg.LedSource] = LedSource(max(lo, min(m, hi)))

    else:
        pass

    tuiRegs_.update(hwRegsToTuiRegs(hwRegs_))

    return
# }}} def updateRegs

def calc_windowsPerSecond(tuiRegs:Dict[TuiReg, Any]) -> float: # {{{

    sampleRate:float = tuiRegs[TuiReg.SampleRate] # kHz
    windowLength:int = tuiRegs[TuiReg.WindowLength] # samples

    ret:float = 1000 * sampleRate / windowLength

    return ret
# }}} def calc_windowsPerSecond

def calc_bitRate(tuiRegs:Dict[TuiReg, Any], hwRegs:Dict[HwReg, Any]) -> float: # {{{

    bitsPerWindow:int = calc_bitsPerWindow(hwRegs)
    windowsPerSecond:float = calc_windowsPerSecond(tuiRegs)

    ret:float = bitsPerWindow * windowsPerSecond

    return ret
# }}} def calc_bitRate

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

        <appName> ... <precision> ... <devicePath>
        '''

        appName:str = "Correlator"
        devicePath:str = deviceName

        left:str = appName
        mid:str = ' '
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
    def draw(self, tuiRegs:Dict[TuiReg, Any],
                   selectIdx:int=0,
                   outstanding:bool=False) -> None: # {{{
        '''Draw all the parameter lines.

        <label> ... <value> ... <domain>
        '''

        maxLenName:int = max(len(r.name) for r in TuiReg)

        self.win.clear()

        for i,(r,d) in enumerate(mapTuiRegToDomain_.items()):
            nm:str = r.name

            left:str = ' '*(maxLenName - len(nm)) + nm + " = "
            right:str = d

            v = tuiRegs[r]
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

class InfoCalcsWindow(CursesWindow): # {{{
    '''This window contains a list of convenience calculations.

    +----------- ... -------------+
    |section0                     |
    |  calc0 =  value0    (unit0) |
    |  calc1 =  value1    (unit1) |
    ...                         ...
    |  calcN =  valueN    (unitN) |
    |                             |
    |section1                     |
    |  calc0 =  value0    (unit0) |
    |  calc1 =  value1    (unit1) |
    ...                         ...
    |  calcN =  valueN    (unitN) |
    +----------- ... -------------+
    '''
    def draw(self, hwRegs:Dict[HwReg, Any]) -> None: # {{{

        samplePeriod_cycles:int = 2**hwRegs[HwReg.SamplePeriodExp]
        samplePeriod_ms:float = samplePeriod_cycles / float(maxSampleRate_kHz)
        sampleRate_kHz:float = 1.0 / samplePeriod_ms
        windowLength_samples:int = 2**hwRegs[HwReg.WindowLengthExp]
        windowPeriod_ms:float = windowLength_samples * samplePeriod_ms
        windowRate_kHz:float = 1.0 / windowPeriod_ms
        pktfifoBitrate_kBps:float = 5 * windowRate_kHz

        lines = (
            "SampleStrobe",
            "  Regularity (cycles)  ≈ %d"       % samplePeriod_cycles,
            "  Period     (ms)      ≈ %0.5f"    % samplePeriod_ms,
            "  Rate       (kHz)     = %0.5f"    % sampleRate_kHz,
            "",
            "Window",
            "  Length     (samples) = %d"       % windowLength_samples,
            "  Period     (ms)      ≈ %0.5f"    % windowPeriod_ms,
            "  Rate       (kHz)     ≈ %0.5f"    % windowRate_kHz,
            "",
            "Pktfifo",
            "  PacketSize (B/window) = %d"      % 5,
            "  Bitate     (kB/s)     ≈ %0.5f"    % pktfifoBitrate_kBps,
        )

        self.win.clear()

        for i,line in enumerate(lines):

            # Fill whole line with background.
            self.drawStr(' '*self.charsWidth, y=i+1)

            self.drawStr(line, y=i+1)

        return # No return value
    # }}} def draw
# }}} class InfoCalcsWindow

class InfoHwRegsWindow(CursesWindow): # {{{
    '''This window contains a list of absolute addresses and values.

    +------------- ... ---------------+
    |name0 (type0 @ address0) = value0|
    |name1 (type1 @ address1) = value1|
    ...                         ...
    |nameN (typeN @ addressN) = valueN|
    +------------- ... ---------------+
    '''
    def draw(self, hwRegs:Dict[HwReg, Any]) -> None: # {{{

        # Fixed 10 lines of 34 characters.
        lines = (
            ("PktfifoDepth        (RO @ %2d) = %2d", HwReg.PktfifoDepth),
            ("MaxWindowLengthExp  (RO @ %2d) = %2d", HwReg.MaxWindowLengthExp),
            ("WindowPrecision     (RO @ %2d) = %2d", HwReg.WindowPrecision),
            ("MaxSamplePeriodExp  (RO @ %2d) = %2d", HwReg.MaxSamplePeriodExp),
            ("MaxSampleJitterExp  (RO @ %2d) = %2d", HwReg.MaxSampleJitterExp),
            ("WindowLengthExp     (RW @ %2d) = %2d", HwReg.WindowLengthExp),
            ("WindowShape         (RW @ %2d) = %2d", HwReg.WindowShape),
            ("SamplePeriodExp     (RW @ %2d) = %2d", HwReg.SamplePeriodExp),
            ("SampleJitterExp     (RW @ %2d) = %2d", HwReg.SampleJitterExp),
            ("LedSource           (RW @ %2d) = %2d", HwReg.LedSource),
        )

        self.win.clear()
        self.win.border(0, ' ', ' ', ' ', ' ', ' ', ' ', ' ')

        for i,(fmt,r) in enumerate(lines):

            addr = r.value
            v = hwRegs[r]

            if isinstance(v, enum.Enum):
              value = v.value
            else:
              assert isinstance(v, int)
              value = v

            line = fmt % (addr, value)

            self.drawStr(line, 2, y=i+1)

        return # No return value
    # }}} def draw
# }}} class InfoHwRegsWindow

def tui(scr, deviceName, rd, wr, hwRegs): # {{{
    '''
    Window objects:
    - scr: All available screen space.
    - full: Rectangle in the centre of scr.
    - inpt: Rectangle below title for dynamic inputs.
    - otpt: Rectangle above status for dynamic outputs (unimplemented).

    Each of the window objects is refreshed individually.
    '''

    tuiRegs_:Dict[TuiReg, Any] = hwRegsToTuiRegs(hwRegs)
    tuiRegs_.update({TuiReg.UpdateMode: UpdateMode.Batch})
    assert all(k in tuiRegs_.keys() for k in TuiReg)
    selectIdx_ = 0
    outstanding_ = False
    hwRegs_ = hwRegs

    infoHwRegs_nLines = 10
    infoHwRegs_lineLength = 34
    infoCalcs_nLines = 13
    nInfoLines = 3

    curses.curs_set(0) # Hide the cursor.
    cursesInitPairs() # Initialize colors

    full:CursesWindow = FullWindow(scr,
        nLines=len(TuiReg) + 7 + max(infoCalcs_nLines, infoHwRegs_nLines),
        nChars=80,
        colorPair=whiteBlue)
    full.win.box()
    full.drawTitle(deviceName, hwRegs)
    full.drawStatus()
    full.win.refresh()

    inpt:CursesWindow = InputWindow(full.win,
        nLines=len(TuiReg)+2, nChars=full.nChars-2,
        colorPair=greenBlack,
        beginY=full.lineTop+1, beginX=1)
    inpt.draw(tuiRegs_)
    inpt.win.keypad(True)
    inpt.win.refresh()

    infoCalcs:CursesWindow = InfoCalcsWindow(full.win,
        nLines=infoCalcs_nLines+2, nChars=80-infoHwRegs_lineLength-4,
        colorPair=yellowBlack,
        beginY=full.lineTop+len(TuiReg)+2, beginX=1)
    infoCalcs.draw(hwRegs_)
    infoCalcs.win.refresh()

    infoHwRegs:CursesWindow = InfoHwRegsWindow(full.win,
        nLines=infoHwRegs_nLines+2, nChars=infoHwRegs_lineLength + 2,
        colorPair=yellowBlack,
        beginY=full.lineTop+len(TuiReg)+2, beginX=79-infoHwRegs_lineLength-3)
    infoHwRegs.draw(hwRegs_)
    infoHwRegs.win.refresh()

    while 1:
        c = inpt.win.getch() # Calls refresh for this and derived windows.

        # Map keypress/character to action.
        if curses.KEY_UP == c and 0 < selectIdx_:
            keyAction:KeyAction = KeyAction.NavigateUp
        elif curses.KEY_DOWN == c and (len(TuiReg)-1) > selectIdx_:
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
            updateRegs(selectIdx_, tuiRegs_, hwRegs_, True)
        elif keyAction == KeyAction.ModifyIncrease:
            updateRegs(selectIdx_, tuiRegs_, hwRegs_, False)
        elif keyAction == KeyAction.Quit:
            break
        else:
            pass

        actionIsModify = keyAction in (KeyAction.ModifyDecrease,
                                       KeyAction.ModifyIncrease)

        isInteractive = (tuiRegs_[TuiReg.UpdateMode] == UpdateMode.Interactive)
        isBatch = (tuiRegs_[TuiReg.UpdateMode] == UpdateMode.Batch)
        assert isBatch or isInteractive

        # Send updates to hardware and readback to ensure display matches the
        # actual values reported from hardware.
        if (isInteractive and actionIsModify) or \
           keyAction == KeyAction.SendUpdate:
            _ = wr(hwRegs_)
            hwRegs_:Dict[HwReg, Any] = rd(hwRegs_.keys())
            tuiRegs_.update(hwRegsToTuiRegs(hwRegs_))
            outstanding_ = False
        elif isBatch and actionIsModify:
            outstanding_ = True
        else:
            pass

        # Update display.
        inpt.draw(tuiRegs_, selectIdx_, outstanding_)
        inpt.win.refresh()

        infoCalcs.draw(hwRegs_)
        infoCalcs.win.refresh()

        infoHwRegs.draw(hwRegs_)
        infoHwRegs.win.refresh()

    return # No return value
# }}} def tui

# {{{ argparser

argparser = argparse.ArgumentParser(
    formatter_class = argparse.ArgumentDefaultsHelpFormatter
)

argparser.add_argument("--prog",
    action="store_true",
    help="Attempt to program a bitfile before starting TUI.")

argparser.add_argument("-b", "--bitfile",
    type=str,
    default=None,
    help="Bitfile for FPGA implementing correlator hardware, used with --prog."
         " If None then try using environment variable `$CORRELATOR_BITFILE`;"
         " Then try using the last item of `./correlator.*.bin`;"
         " Then try using the bundled bitfile.")

argparser.add_argument("--no-init",
    action="store_true",
    help="Do not perform any writes on startup.")

argparser.add_argument("-d", "--device",
    type=str,
    default=None,
    help="Serial device to connect to (immediately after programming)."
         " If None then try using environment variable `$CORRELATOR_DEVICE`;"
         " Then try using the last item of `/dev/ttyACM*`.")

argparser.add_argument("--timeout",
    type=functools.partial(argparse_nonNegativeReal, "timeout"),
    default=1.0,
    help="Maximum expected time (seconds) required to read a burst of 256B."
         " Passed directly to pySerial.")

argparser.add_argument("--init-windowLengthExp",
    type=argparse_WindowLengthExp,
    default=16,
    help="windowLength = 2**windowLengthExp  (samples)")

argparser.add_argument("--init-windowShape",
    type=argparse_WindowShape,
    default=WindowShape.Rectangular,
    help="Shape of sampling window function.")

argparser.add_argument("--init-samplePeriodExp",
    type=argparse_SamplePeriodExp,
    default=0,
    help="sampleRate = maxSampleRate * 2**-samplePeriodExp  (Hz)")

argparser.add_argument("--init-sampleJitterExp",
    type=argparse_SampleJitterExp,
    default=0,
    help="sampleJitter < 2**sampleJitterExp  (cycles)")

argparser.add_argument("--init-ledSource",
    type=argparse_LedSource,
    default=LedSource.WinNum,
    help="Data source for LED brightness, either string like 'Cov' or integer.")

argparser.add_argument("--prng-seed",
    type=int,
    default=0xacce55ed,
    help="Seed for xoshiro128+ PRNG used for sampling jitter.")

# }}} argparser

def main(args) -> int: # {{{
    '''
    1. Upload bitfile to FPGA.
    2. Open connection to device.
    3. Read config RO registers.
    4. Write config RW registers.
    5. Read/check config RW registers.
    6. Initialize TUI
    7. TUI output loop:
        1. Sleep for refresh period.
        2. Read results RO registers.
        2. Update results section.
    8. TUI config loop:
        1. Wait for <Enter>
        2. Write config RW registers.
        3. Read config RW registers, check they're what was written.
    9. TUI input loop:
        1. Wait for keypress.
        2. Handle keypress by moving highlighted line or changing value.
    '''

    locale.setlocale(locale.LC_ALL, '')

    if args.prog:
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
    else:
        devicePath = getDevicePath(args.device)


    # Keep lock on device to prevent other processes from accidentally messing
    # with the state machine.
    verb("Connecting to device %s" % devicePath)
    with serial.Serial(devicePath,
                       timeout=args.timeout,
                       write_timeout=args.timeout) as device:
        rdBytePipe:Callable = functools.partial(bpReadSequential, device)
        wrBytePipe:Callable = functools.partial(bpWriteSequential, device)
        rd:Callable = functools.partial(hwReadRegs, rdBytePipe)
        wr:Callable = functools.partial(hwWriteRegs, wrBytePipe)

        verb("Reading RO registers...", end='')
        hwRegsRO:Dict[HwReg, Any] = rd((
            HwReg.PktfifoDepth,
            HwReg.MaxWindowLengthExp,
            HwReg.WindowPrecision,
            HwReg.MaxSamplePeriodExp,
            HwReg.MaxSampleJitterExp,
        ))
        verb("Done")

        # Fill in missing values of parameter domains.
        mapTuiRegToDomain_.update({
            TuiReg.WindowLength: mapTuiRegToDomain_[TuiReg.WindowLength] %
                hwRegsRO[HwReg.MaxWindowLengthExp],
            TuiReg.SampleRate: mapTuiRegToDomain_[TuiReg.SampleRate] %
                hwRegsRO[HwReg.MaxSamplePeriodExp],
            TuiReg.SampleJitter: mapTuiRegToDomain_[TuiReg.SampleJitter] %
                hwRegsRO[HwReg.MaxSampleJitterExp],
        })


        # Gather registers required for TUI.
        initRegsRW:Dict[HwReg, Any] = {
            HwReg.WindowLengthExp:      args.init_windowLengthExp,
            HwReg.WindowShape:          args.init_windowShape,
            HwReg.SamplePeriodExp:      args.init_samplePeriodExp,
            HwReg.SampleJitterExp:      args.init_sampleJitterExp,
            HwReg.LedSource:            args.init_ledSource,
        }

        if args.no_init:
            verb("Reading RW registers...", end='')
            hwRegsRW:Dict[HwReg, Any] = rd(initRegsRW.keys())
            verb("Done")
        else:
            verb("Initializing RW registers...", end='')
            wr(initRegsRW)
            verb("Checking...", end='')
            hwRegsRW:Dict[HwReg, Any] = rd(initRegsRW.keys())
            assert all(initRegsRW[k] == v for k,v in hwRegsRW.items()), hwRegsRW
            verb("Done")

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

        try:
            verb("Starting TUI (curses)...")
            curses.wrapper(tui, device.name, rd, wr, {**hwRegsRO, **hwRegsRW})
            verb("TUI Done")
        except KeyboardInterrupt:
            verb("KeyboardInterrupt. Exiting.")

    return 0
# }}} def main

def entryPoint(argv=sys.argv):
    return run(__name__, argv=argv)

if __name__ == "__main__":
    sys.exit(entryPoint())

