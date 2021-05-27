#!/usr/bin/env python3

from __future__ import print_function
from __future__ import absolute_import
from __future__ import division

import sys
import time
import traceback

if __name__ == "__main__":
    print("Not a standalone module.")
    sys.exit(1)

#from dmppl.base import verb, dbg

from test_env import send_msg, recv_msg, codec
from ust_evaluation import TargetDisconnected, \
    configureMessageInfrastructure, disableModules, discoverStatusMonitor, \
    receiveStatusMonCounterDataMessages

nQualifiers = 16

windowLengthExp     = 15        # 32k samples
windowShape         = "rectangular" # 1'd1
samplePeriodExp     = 0         # Lockstep with interval-timer.
sampleJitterExp     = 0         # Jitter not supported because of interval-timer message-push mechanism.
pwmSelect           = 0         # winNum

if "fnameo" not in test_params:
    test_params["fnameo"] = "test0.csv"
fnameo = str(test_params["fnameo"])

if "nSamples" not in test_params:
    test_params["nSamples"] = 1000
nSamples = int(test_params["nSamples"])

if "probeX" not in test_params:
    test_params["probeX"] = 10      # 22    <-->    10
probeX = int(test_params["probeX"])

if "probeY" not in test_params:
    test_params["probeY"] = 2       # 5     <-->    2
probeY = int(test_params["probeY"])

def receiveStatusMonCorrelatorMessages(target_sm, discovery, output): # {{{

  global sw_link_disconnected

  assert 0 == discovery.fields['accumulator_width'].value
  assert 1 == discovery.fields['counters'].value
  assert 32 == {1:16, 2:24, 3:32, 4:48, 5:64}[discovery.fields['counter_width'].value]

  def is_monitor_type_data(msg_type, msg):
      if codec.msg_generation < 2:
          return msg.header == 'monitor_data'   and msg.fields['type'] == 'monitor_'+msg_type+'_data'
      else:
          return msg.header == 'system_control' and msg.fields['msg_type'] == 'monitor_'+msg_type+'_data'

  output.write("x, y, x_isect_y, x_symdiff_y\n")

  sample = 0
  while True:
      try:

        m = recv_msg()

        if m.module == target_sm and is_monitor_type_data('counter', m):
            assert 0 == m.fields['cause'].value # Interval timer expiry
            pkt = m.fields['counters'].value
            x, y, x_isect_y, x_symdiff_y = (
                ((pkt >> (0*8)) & 0xff),
                ((pkt >> (1*8)) & 0xff),
                ((pkt >> (2*8)) & 0xff),
                ((pkt >> (3*8)) & 0xff),
            )
            output.write("%d,%d,%d,%d\n" % (x, y, x_isect_y, x_symdiff_y))
            sample += 1

            if not (x == y == x_isect_y) or not (0 == x_symdiff_y):
                print("LOOK HERE:", sample, x, y, x_isect_y, x_symdiff_y)

            if sample >= nSamples:
                print("Ending test: sample limit reached...")
                disableModules()
                break

      except TargetDisconnected:
        # Return control to test script if sw-link disconnects
        print("Ending test: sw-link disconnected...")
        sw_link_disconnected = True
        raise TargetDisconnected("test script ending")
        break
      except Exception as e:
        print("Unexpected exception [%s]" % (e.__class__.__name__))
        traceback.print_exc()
        sys.exit()
# }}} def receiveStatusMonCorrelatorMessages


# Configure the UltraDebug message infrastructure and return handles to the
# message engine and status monitor.
(me, sm) = configureMessageInfrastructure('sm')

# Send a discovery_request message (UG 6.1.2) to the status monitor, and store
# its response
discovery = discoverStatusMonitor(sm)

# {{{ Initally disable module and all qualifiers. (UG 5.1.16)
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_enabled",        # 6'h04
        "operation"             : "apply",              # 2'b00
        "module_enable"         : 0,                    # 1'
        "qualifier_enable"      : 0x0000,               # 16'
    }
)

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()
# }}} Initally disable module and all qualifiers. (UG 5.1.16)

# {{{ power/clock-gating
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_power",          # 6'h07
    }
)
recv_msg()

#send_msg(
#    module=sm,
#    fields={
#        "msg_type"              : "sc",                 # 2'b00
#        "control_code"          : "set_power",          # 6'h08
#        "clk_disable"           : 1,                    # 1'
#    }
#)
#
#send_msg(
#    module=sm,
#    fields={
#        "msg_type"              : "sc",                 # 2'b00
#        "control_code"          : "get_power",          # 6'h07
#    }
#)
#recv_msg()
## }}} power/clock-gating

# {{{ Setup monitor module counter
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_monitor",        # 6'h30
    }
)
recv_msg()

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_monitor",        # 6'h31
        "sys_timestamp"         : 1,                    # 1'
        "sys_flow"              : 0,                    # 2'
        "match_timestamp"       : 1,                    # 1'
        "match_flow"            : 0,                    # 2'
        "match_throttle_level"  : 1,                    # 2' Never
        "counters_timestamp"    : 1,                    # 1'
        "counters_flow"         : 0,                    # 2'
        "counters_throttle_level" : 1,                  # 2' Never
        "counters_trigger"      : 0,                    # 17'
        "counters_interval_trigger" : 1,                # 1' Snapshot on interval expiry
        "counters_event_control" : 0,                   # 1'
    }
)

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_monitor",        # 6'h30
    }
)
recv_msg()
# }}} Setup monitor module counter

# {{{ Setup interval-timer
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_period",         # 6'h1d
    }
)
recv_msg()

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_period",         # 6'h1e
        "timer_enable"          : 1,                    # 2'd1 Continuous
        "timer_interval"        : 2**(windowLengthExp+samplePeriodExp), # 64'
        "timer_index_trigger"   : 0,                    # 8'd0
    }
)

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_period",         # 6'h1d
    }
)
recv_msg()
# }}} Setup interval-timer

# {{{ Setup correlator
# View initial state.
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_correlator",     # 6'h3d
        "correlator"            : 0,                    # 4'd0 There is only one.
    }
)
recv_msg()

# Setup correlator.
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_correlator",     # 6'h3e
        "correlator"            : 0,                    # 4'd0 There is only one.
        "window_length_exp"     : windowLengthExp,
        "window_shape"          : windowShape,
        "sample_period_exp"     : samplePeriodExp,
        "sample_jitter_exp"     : sampleJitterExp,
        "pwm_select"            : pwmSelect,
        "probe_x"               : probeX,
        "probe_y"               : probeY,
    }
)

# View modified state.
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_correlator",     # 6'h3d
        "correlator"            : 0,                    # 4'd0 There is only one.
    }
)
recv_msg()
# }}} Setup correlator

# Seed the strobe PRNG.
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "seed_correlator",    # 6'h3f
        "correlator"            : 0,                    # 4'd0 There is only one.
        "byte"                  : 0x55,
    }
)

# {{{ Setup qualifiers.
for i in range(nQualifiers):
    send_msg(
        module=sm,
        fields={
            "msg_type"              : "sc",                 # 2'b00
            "control_code"          : "get_sts_qualifier",  # 6'h3b
            "qualifier"             : i,                    # 4'
        }
    )
    recv_msg()

    send_msg(
        module=sm,
        fields={
            "msg_type"              : "sc",                 # 2'b00
            "control_code"          : "set_sts_qualifier",  # 6'h3c
            "qualifier"             : i,                    # 4'
            "qualifier_enable"      : 1,                    # 1'
            "issue_mode"            : 0,                    # 3' Don't issue anything.
            "input_select"          : i,                    # 8' Wire qual(i) from match(i)
            "pfunction"             : 0,                    # 3' Match when input high
            "sfunction"             : 0,                    # 3' Ignored
            "match_mode"            : 0,                    # 2' Ignored
            "event"                 : 0,                    # 8'
            "enable_trigger"        : 0,                    # 17'
            "event_enable_control"  : 0,                    # 1'
            "disable_trigger"       : 0,                    # 17'
            "event_disable_control" : 0,                    # 1'
            "match_threshold"       : 0,                    # 16'
            "threshold_mode"        : 0,                    # 3'
        }
    )

    send_msg(
        module=sm,
        fields={
            "msg_type"              : "sc",                 # 2'b00
            "control_code"          : "get_sts_qualifier",  # 6'h3b
            "qualifier"             : i,                    # 4'
        }
    )
    recv_msg()
# }}} Setup qualifiers.

# {{{ Enable module and all qualifiers. (UG 5.1.16)
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_enabled",        # 6'h04
        "operation"             : "apply",              # 2'b00
        "module_enable"         : 1,                    # 1'
        "qualifier_enable"      : 0xffff,               # 16'
    }
)

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()
# }}} Enable module and all qualifiers. (UG 5.1.16)

with open("../../"+fnameo, 'w') as fd:
    receiveStatusMonCorrelatorMessages(sm, discovery, fd)

# {{{ Finally disable module and all qualifiers. (UG 5.1.16)
send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "set_enabled",        # 6'h04
        "operation"             : "apply",              # 2'b00
        "module_enable"         : 0,                    # 1'
        "qualifier_enable"      : 0x0000,               # 16'
    }
)

send_msg(
    module=sm,
    fields={
        "msg_type"              : "sc",                 # 2'b00
        "control_code"          : "get_enabled",        # 6'h03
    }
)
recv_msg()
# }}} Finally disable module and all qualifiers. (UG 5.1.16)

print("Test FINISHED")

