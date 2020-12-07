
fifoScoreboards
===============

This is a single constrained-random testbench used to test many different types
of fifo with different parameters, running fully parallel via `make`, and the
checks performed using `diff`.


Runtime Control
---------------

Using GNU/make for runtime control means there is no dependence on a collection
of unwieldy scripts and parallel tests can be run with the standard `-j` flag.
A CSV file is read to define a collection of parameter sets (default `all.csv`)
which is mapped onto preprocessor defines passed to the testbench.

Which designs to test, the run length of each test, and how wide to run is
specified using command line arguments, for example:
`make CSV=cdcFifo N_CYCLES=999 -j8`


Data Integrity Checks
---------------------

The testbench produces logfiles (`*.pushed.log`, `*.popped.log`) for all data
observed going in and out, so data integrity can be checked by comparing the
difference between the dataflows at each end.
This method removes the need for many runtime assertions and works for both
single-clock and CDC designs.

A clean diff implies the following checks have passed:
  1. No data dropped.
  2. No extraeous data inserted.
  3. No data contents changed.
  4. No data re-ordered.

If a problem is found with a dirty diff, then the logfiles may be consulted to
determine the exact times (`nCycles_q` of `tbclk`) where divergence occurred.
I have found this useful with a graphical diff because patterns of bad data are
immediately visible.


Clock Domain Crossing Testbench
-------------------------------

Absolute time for the testbench is tracked via the `nCycles_q` counter.
This is incremented every cycle until it equals the `N_CYCLES` parameter, then
the testbench is allowed to run for a further 1k cycles with data-push disabled
in order to allow data to flow out naturally.

Support for different clocks on write and read sides of the DUT is enabled via
a non-zero value `CDC` column of the CSV file.
When CDC is disabled, both write and read clocks run at the same rate as the
testbench.
When CDC is enabled, the frequency of write and read clocks are randomly
adjusted to a relative rate of between 1/8 and 8/1 (randomly chosen).
The random selection occurs approximately each 32k testbench clock cycles.

Support for power saving clock-gating is also built-in with different clock
gates for write and read sides dropping at random rates.
Different random rates are chosen approximately each 64k testbench clock cycles
to between 1/20 and 1/640.

Resets are not properly tested in this testbench, and simply dropped at the
beginning of the test.

