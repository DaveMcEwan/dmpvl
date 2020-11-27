
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
echo "frequency_Hz 2000" > tbCtrl
echo "continue" > tbCtrl

# Run the interactive application as a foreground process.
# When doing interactive use the VCD will be very large unless the frequency is
# kept low, say to 200Hz.
#correlator-tui -v --device=ptyBytePipe_bp0

# Run recording application as a (short-lived) foreground process.
correlator-record -v --device=ptyBytePipe_bp0 \
  --init-xSelect=1 --init-ySelect=2 \
  --init-windowLengthExp=5 -n=200 \
  --timeout=10.0 -o ./build/data.txt

# Now that the application has finished, stop the tb.
echo "discontinue" > tbCtrl
echo "step 10" > tbCtrl
sleep 1
echo "quit" > tbCtrl

# Compress VCD to FST format for faster wave browsing.
vcd2fst ./build/correlator_tb.verilator.vcd ./build/correlator_tb.verilator.fst

# Plot recorded data.
plotCsv --skiprows=1 --labels=X,Y,isect,symdiff -o ./build/plot ./build/data.txt

