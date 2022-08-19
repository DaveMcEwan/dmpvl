
The Rule
--------

You should explicitly declare each module/package localparam/parameter with a
2-state datatype.

Background on Datatypes
-----------------------

To understand the reasoning behind this (seemingly simple) rule, it is
important to understand some details around SystemVerilog integral datatypes.
Integral datatypes are the "usual" types used in digital design code, though
other datatypes are commonly used in analog designs and in verification
environments, e.g. `real`, `void`, `chandle`, `string`, and `event`.
Integral datatypes are summarised in the following table.

| Keyword  | 2/4-state | Value $^1$ | Vector $^2$ | Width  | Signedness $^4$ |
|:---------|:---------:|:----------:|:-----------:|:------:|:---------------:|
| bit      |     2     |    `'0`    |     yes     | 1 $^3$ |     unsigned    |
| byte     |     2     |    `'0`    |     no      | 8      |      signed     |
| shortint |     2     |    `'0`    |     no      | 16     |      signed     |
| int      |     2     |    `'0`    |     no      | 32     |      signed     |
| longint  |     2     |    `'0`    |     no      | 63     |      signed     |
| logic    |     4     |    `'X`    |     yes     | 1 $^3$ |     unsigned    |
| integer  |     4     |    `'X`    |     no      | 32     |      signed     |
| time     |     4     |    `'X`    |     no      | 64     |     unsigned    |

1. Values of nets or variables can be overridden using one of the assignment
   constructs with (blocking, non-blocking, continuous, and procedural).
   The value of a parameter, i.e. an elaboration-time constant, is set by
   either a parameter override in a module instance (such as
   `Mod #(.FOO(5)) u_inst ();`), or a default value in the module declaration
   (such as `module Mod #(int FOO = 123) ();`.
2. Vector types may have packed dimensions which are specified before the
   identifier like `bit [5:0] foo`, as well as unpacked dimensions which are
   specified after the identifier like `bit foo [5]`.
   Non-vector types may not have packed dimensions.
3. The default width of a vector type is overridden using packed dimensions.
4. The default signedness of any integral type may be overridden using the
  `signed` or `unsigned` keywords.

SystemVerilog also allows the user to define their own aggregate datatypes
consisting of packed/unpacked structures, unions, enumerations, dynamic arrays,
associative array, and queues.
The aggregate datatypes relevant to this discussion are packed structures.
A packed structure is essentially a bit vector with named bit slices, i.e. it
can be operated on as a whole, and has the same attributes as a `bit` or
`logic`.
As such, a packed structure can be either 2-state or 4-state, which is inferred
from the datatypes of its members.
If any of a packed structure's members are 4-state, then the whole structure
is treated as 4-state.

```systemverilog
typedef struct packed {
  bit b;      // 2-state
  int a;      // 2-state
} s2;

typedef struct packed
  logic b;    // 4-state
  integer a;  // 4-state
} s4;

typedef struct packed
  logic b;    // 4-state
  int a;      // 2-state
} sM;

// 2-state constants, good practice.
localparam s2 FOO_A = {1'b1, 32'd123};
localparam s2 FOO_B = '1;
localparam s2 FOO_C = constantFoo();

// 4-state constants, warrants close inspection.
localparam s4 BAR_A = {1'bZ, 32'b01XZ}; // Used in a wildcard comparison?
localparam s4 BAR_B = 'X;               // Legal, but probably nonsense!

// Accidentally 4-state constants, intended to be 2-state.
localparam sM BAR_A = {1'b1, 32'd123};  // All bits are 0 or 1, but 4-state.
localparam sM BAZ_B = constantBaz();    // Maybe hidden X/Z in here.
```

Overriding Module Parameters
----------------------------

Let's use a couple of example modules to demonstrate exactly what datatypes
are inferred by different styles of declaration.
Firstly, child modules are defined with almost the same set of parameters.

In the `CI` module (child, implicit types), the type of each parameter is
inferred from its default value (`integer`), but will be changed to the type of
any override value from a parent module.
It is therefore sensible to somehow check within `CI` that the parameters are
of the expected type (using `type`) and size (using `$size`).
The default type of all parameters is `logic [MSB:0]` where `MSB` is at least
31 but is implementation-dependent (see page 121).
The default value of `NOVALUE` is `'X`.
```systemverilog
module CI
  #(parameter FIVE = 5
  , parameter VEC1D = {1, 2, 3}
  , parameter NOVALUE
  ) ();
endmodule
```

In the `CE2` module (child, explicit 2-state types), the type of each parameter
is explicitly declared and cannot be overriden by a parent module.
This is the approach advocated in this document.
No further checks on the type or size of these parameters are required because
any override values froma a parent module are converted to the explicitly
declared type.
The default values of `NOVALUE_INT` and `NOVALUE_BIT` are `32'd0` and `1'd0`
respectively.
```systemverilog
module CE2
  #(parameter int FIVE = 5
  , parameter bit [2:0][31:0] VEC1D = {1, 2, 3}
  , parameter int NOVALUE_INT
  , parameter bit NOVALUE_BIT
  ) ();
endmodule
```

The `CE4` module (child, explicit 4-state types) is similar to `CE2` except
that the explicitly declared types are 4-state instead of 2-state.
The default values of `NOVALUE_INTEGER` and `NOVALUE_LOGIC` are `32'bX` and
`1'bX` respectively.
```systemverilog
module CE4
  #(parameter integer FIVE = 5
  , parameter logic [2:0][31:0] VEC1D = {1, 2, 3}
  , parameter integer NOVALUE_INTEGER
  , parameter logic NOVALUE_LOGIC
  ) ();
endmodule
```

NOTE: WIP/UNFINISHED
```systemverilog
module PI ();

 // TODO: Implicit type localparams for overrides.
 // TODO: More instances with expected/unexpected types, especially for VEC1D.

  CI
  #(.FIVE     ()
  , .VEC1D    ()
  , .NOVALUE  ()
  ) u_ci ();

  CE2
  #(.FIVE         ()
  , .VEC1D        ()
  , .NOVALUE_INT  ()
  , .NOVALUE_BIT  ()
  ) u_ce2 ();

  CE4
  #(.FIVE         ()
  , .VEC1D        ()
  , .NOVALUE_INT  ()
  , .NOVALUE_BIT  ()
  ) u_ce4 ();
endmodule
```

- TODO: Examples with parents PI and PE
- TODO: Constant functions and default values.
- TODO: Why does it matter?
- TODO: Comparison operations and X-propagation.
- TODO: Casting operator.

Checking Parameter Values
-------------------------
TODO: Elaboration System Tasks



Appendix: Key Quotes from the Language Reference Manual (IEEE1800-2017)
-----------------------------------------------------------------------

These are key pieces of the SystemVerilog specification, reproduced here to
provide an overview of where the most relevant information lies.
Although care is taken to provide a reasonable amount of context here, there is
no substitute for reading the LRM.


### Table 6-7 Default variable initial values

| Type             | Default initial value |
|:-----------------|:---------------------:|
| 4-state integral |         `'X`          |
| 2-state integral |         `'0`          |
| ...              |         ...           |


### Table 6-8 Integer data types

| Keyword    | Attributes                                                 |
|:-----------|:-----------------------------------------------------------|
| `shortint` | 2-state data type, 16-bit signed integer                   |
| `int`      | 2-state data type, 32-bit signed integer                   |
| `longint`  | 2-state data type, 64-bit signed integer                   |
| `byte`     | 2-state data type, 8-bit signed integer or ASCII character |
| `bit`      | 2-state data type, user-defined vector size, unsigned      |
| `logic`    | 4-state data type, user-defined vector size, unsigned      |
| `reg`      | 4-state data type, user-defined vector size, unsigned      |
| `integer`  | 4-state data type, 32-bit signed integer                   |
| `time`     | 4-state data type, 64-bit unsigned integer                 |


### Clause 6.4 Singular and aggregate types

Data types are categorized as either singular or aggregate.
A singular type shall be any data type except an unpacked structure, unpacked
union, or unpacked array (see 7.4 on arrays).
An aggregate type shall be any unpacked structure, unpacked union, or unpacked
array data type.
A singular variable or expression represents a single value, symbol, or handle.
Aggregate expressions and variables represent a set or collection of singular
values.
Integral types (see 6.11.1) are always singular even though they can be sliced
into multiple singular values.
The `string` data type is singular even though a string can be indexed in a
similar way to an unpacked array of bytes.

These categories are defined so that operators and functions can simply refer
to these data types as a collective group.
For example, some functions recursively descend into an aggregate variable
until reaching a singular value and then perform an operation on each singular
value.

Although a class is a type, there are no variables or expressions of class type
directly, only class object handles that are singular.
Therefore, classes need not be categorized in this manner (see Clause 8 on
classes).


### Clause 6.11.2 2-state (two-value) and 4-state (4-value) data types

Types that can have unknown and high-impedance values are called 4-state types.
These are `logic`, `reg`, `integer`, and `time`.
The other types do not have unknown values and are called 2-state types, for
example, `bit` and `int`.

The difference between `int` and `integer` is that `int` is a 2-state type and
`integer` is a 4-state type.
The 4-state values have additional bits, which encode the `X` and `Z` states.
The 2-state data types can simulate faster, take less memory, and are preferred
in some design styles.

The keyword `reg` does not always accurately describe user intent, as it could
be perceived to imply a hardware register.
The keyword `logic` is a more descriptive term.
`logic` and `reg` denote the same type.

Automatic type conversions from a smaller number of bits to a larger number of
bits involve zero extensions if unsigned or sign extensions if signed.
Automatic type conversions from a larger number of bits to a smaller number of
bits involve truncations of the most significant bits (MSBs).
When a 4-state value is automatically converted to a 2-state value, any unknown
or high-impedance bits shall be converted to zeros.


### Clause 6.20.1 Parameter declaration syntax (bottom of page 120)

The `parameter` keyword can be omitted in a parameter port list.


### Clause 6.20.2 Value parameters (bottom half of page 121)

A parameter constant can have a type specification and a range specification.
The type and range of parameters shall be in accordance with the following
rules:

- A parameter declaration with no type or range specification shall default to
  the type and range of the final value assigned to the parameter, after any
  value overrides have been applied.
  If the expression is real, the parameter is real.
  If the expression is integral, the parameter is a logic vector of the same
  size with range `[size-1:0]`.
- A parameter with a range specification, but with no type specification, shall
  have the range of the parameter declaration and shall be unsigned.
  The sign and range shall not be affected by value overrides.
- A parameter with a type specification, but with no range specification, shall
  be of the type specified.
  A signed parameter shall default to the range of the final value assigned to
  the parameter, after any value overrides have been applied.
- A parameter with a signed type specification and with a range specification
  shall be signed and shall have the range of its declaration.
  The sign and range shall not be affected by value overrides.
- A parameter with no range specification and with either a signed type
  specification or no type specification shall have an implied range with an
  lsb equal to 0 and an msb equal to one less than the size of the final value
  assigned to the parameter.
- A parameter with no range specification, with either a signed type
  specification or no type specification, and for which the final value
  assigned to it is unsized shall have an implied range with an lsb equal to 0
  and an msb equal to an implementation-dependent value of at least 31.


### Clause 7.2.1 Packed structures

A packed structure is a mechanism for subdividing a vector into subfields,
which can be conveniently accessed as members.
Consequently, a packed structure consists of bit fields, which are packed
together in memory without gaps.
An unpacked structure has an implementation-dependent packing, normally
matching the C compiler.
A packed structure differs from an unpacked structure in that, when a packed
structure appears as a primary, it shall be treated as a single vector.

A packed structure can also be used as a whole with arithmetic and logical
operators, and its behavior is determined by its signedness, with unsigned
being the default.
The first member specified is the most significant and subsequent members
follow in decreasing significance.

```systemverilog
struct packed signed {
  int a;
  shortint b;
  byte c;
  bit [7:0] d;
} pack1; // signed, 2-state

struct packed unsigned {
  time a;
  integer b;
  logic [31:0] c;
} pack2; // unsigned, 4-state
```

The signing of unpacked structures is not allowed.
The following declaration would be considered illegal:

```systemverilog
typedef struct signed {
  int f1 ;
  logic f2 ;
} sIllegalSignedUnpackedStructType; // illegal declaration
```

If all data types within a packed structure are 2-state, the structure as a
whole is treated as a 2-state vector.

If any data type within a packed structure is 4-state, the structure as a whole
is treated as a 4-state vector.
If there are also 2-state members in the structure, there is an implicit
conversion from 4-state to 2-state when reading those members and from 2-state
to 4-state when writing them.

One or more bits of a packed structure can be selected as if it were a packed
array with the range [n-1:0]: `pack1 [15:8] // c`
Only packed data types and the integer data types summarized in Table 6-8 (see
6.11) shall be legal in packed structures.

A packed structure can be used with a typedef.
```systemverilog
typedef struct packed { // default unsigned
  bit [3:0] GFC;
  bit [7:0] VPI;
  bit [11:0] VCI;
  bit CLP;
  bit [3:0] PT ;
  bit [7:0] HEC;
  bit [47:0] [7:0] Payload;
  bit [2:0] filler;
} s_atmcell;
```


### Clause 23.10 Overriding module parameters (between pages 731,732)

A value parameter (see 6.20.2) can have a type specification and a range
specification.
The effect of parameter overrides on a value parameter’s type and range shall
be in accordance with the following rules:

- A value parameter declaration with no type or range specification shall
  default to the type and range of the final override value assigned to the
  parameter.
- A value parameter with a range specification, but with no type specification,
  shall have the range of the parameter declaration and shall be unsigned.
  An override value shall be converted to the type and range of the parameter.
- A value parameter with a type specification, but with no range specification,
  shall be of the type specified.
  An override value shall be converted to the type of the parameter.
  A signed parameter shall default to the range of the final override value
  assigned to the parameter.
- A value parameter with a signed type specification and with a range
  specification shall be signed and shall have the range of its declaration.
  An override value shall be converted to the type and range of the parameter.
