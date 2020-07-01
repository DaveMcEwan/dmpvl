
# Start the tb as a background process which creates the fifo "tbCtrl" then
# listens to it for commands.
./build/Vcorrelator_tb > ./build/run.log &
sleep 1

# Initialize the design to look like it has come out of reset for a few cycles.
echo "reset" > tbCtrl
echo "step 10" > tbCtrl

# Let the design run freely at a slow clockrate.
# This sets the period between clock ticks to a fixed number of microseconds,
# and execution time for evaluating each tick is ignored, so actual frequency
# will be slightly (or a lot) less.
echo "frequency_Hz 100" > tbCtrl
echo "continue" > tbCtrl

# Run the interactive application as a foreground process.
../../prj/correlator/correlator/correlator_tui.py --no-prog --device=ptyBytePipe_bp0 --verbose

# Now that the application has finished, stop the tb.
echo "step 10" > tbCtrl
echo "quit" > tbCtrl

