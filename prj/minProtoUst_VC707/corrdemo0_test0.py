#!/usr/bin/env python3

from __future__ import print_function
from __future__ import absolute_import
from __future__ import division

import sys
import time

if __name__ == "__main__":
    print("Not a standalone module.")
    sys.exit(1)

from dmppl.base import verb, dbg

from test_env import send_msg, recv_msg
from ust_evaluation import configureMessageInfrastructure, \
    discoverStatusMonitor, receiveStatusMonCounterDataMessages

# NOTE: test_params is used by receiveStatusMonCounterDataMessages().
if "sample_limit" not in test_params:
    test_params["sample_limit"] = 10
sample_limit = int(test_params["sample_limit"])


fnameo = "test0.csv"
windowLengthExp     = 15        # 32k samples
windowShape         = "logdrop" # 1'd1
samplePeriodExp     = 8         # 1/256 cycles
sampleJitterExp     = 2         # variance of 4/256
pwmSelect           = 5         # Cov
probeX              = 9         #
probeY              = 10        #

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

# {{{ Setup interval timer
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
# }}} Setup interval timer

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

print("Test FINISHED")

