module IOBUF #(
  parameter integer DRIVE = 12,
  parameter         IBUF_LOW_PWR = "TRUE",
  parameter         IOSTANDARD = "DEFAULT",
  parameter         SLEW = "SLOW"
) (
  output wire         O,
  inout  wire         IO,
  input  wire         I,
  input  wire         T
);

wire direction;

or      u0 (direction, T);
bufif0  u1 (IO, I, direction);
buf     u2 (O, IO);

endmodule
