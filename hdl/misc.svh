`ifndef MISC_SVH_
`define MISC_SVH_

// Select the least siginficant bits from a net, or a parameter.
// This is useful when tools don't support things like "8'(10'd123)".
`define LSb(n) [n-1:0]

// Construct string literal from preprocessor define.
// See IEEE1800-2005 section 23.2, page 391.
`define STRING(x) `"x`"

`endif // MISC_SVH_
