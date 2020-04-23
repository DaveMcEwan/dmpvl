
usbfsBpRegMem
=============

Simple 128B register block as example implementation of BytePipe over USB-FS.

Use the `bytePipe-utils` script from dmppl to interact and test.

```
# Activate your virtual environment.
source <your venv activate>

# Install dmppl from GitHub.
git clone https://github.com/DaveMcEwan/dmppl.git
cd dmppl
pip install -e .

# Save some typing.
export BYTEPIPE_BITFILE=./build/top.icepack.bin

# Connect the TinyFPGA-BX, then test the BytePipe implementation.

# Dump the values already in place.
bytePipe-utils -v dump

# Identify the writable bits.
bytePipe-utils -v bits

# Run a full test.
bytePipe-utils -v test
```
