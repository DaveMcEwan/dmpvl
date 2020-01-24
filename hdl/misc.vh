`ifndef MISC_VH_
`define MISC_VH_

// Select the least siginficant bits from a net, or a parameter.
// This is useful when tools don't support things like "8'(10'd123)".
`define LSb(n) [n-1:0]

`endif // MISC_VH_
