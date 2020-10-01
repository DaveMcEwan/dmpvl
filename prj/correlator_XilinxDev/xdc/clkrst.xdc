
create_clock -name clk_fpga_0 -period "20" [get_pins "PS7_i/FCLKCLK[0]"]
set_input_jitter clk_fpga_0 0.6
#The clocks are asynchronous, user should constrain them appropriately.#

set_property iostandard "LVCMOS18" [get_ports "PS_PORB"]
set_property PACKAGE_PIN "B5" [get_ports "PS_PORB"]
set_property slew "fast" [get_ports "PS_PORB"]

set_property iostandard "LVCMOS18" [get_ports "PS_SRSTB"]
set_property PACKAGE_PIN "C9" [get_ports "PS_SRSTB"]
set_property slew "fast" [get_ports "PS_SRSTB"]

set_property iostandard "LVCMOS18" [get_ports "PS_CLK"]
set_property PACKAGE_PIN "F7" [get_ports "PS_CLK"]
set_property slew "fast" [get_ports "PS_CLK"]

