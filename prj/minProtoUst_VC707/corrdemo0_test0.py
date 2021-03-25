#!/usr/bin/env python3

from __future__ import print_function
from __future__ import absolute_import
from __future__ import division

import sys
import time

if __name__ == "__main__":
    print("Not a standalone module.")
    sys.exit(1)

#from dmppl.base import verb, dbg

from test_env import send_msg, recv_msg
from ust_evaluation import configureMessageInfrastructure, \
    discoverStatusMonitor, receiveStatusMonCounterDataMessages

# NOTE: test_params is used by receiveStatusMonCounterDataMessages().
if "sample_limit" not in test_params:
    test_params["sample_limit"] = 5
sample_limit = int(test_params["sample_limit"])


fnameo = "test0.csv"
nQualifiers = 16

windowLengthExp     = 15        # 32k samples
windowShape         = "logdrop" # 1'd1
samplePeriodExp     = 0         # Lockstep with interval-timer.
sampleJitterExp     = 0         # Jitter not supported because of interval-timer message-push mechanism.
pwmSelect           = 5         # Cov
probeX              = 10        # 22    <-->    10
probeY              = 2         # 5     <-->    2

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
        "timer_interval"        : 1 << windowLengthExp, # 64'
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

with open(fnameo, 'w') as fd:
    receiveStatusMonCounterDataMessages(sm, discovery, fd)

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

