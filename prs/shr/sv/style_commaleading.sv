/* Comma-Leading Style
<https://gist.github.com/isaacs/357981>
<https://github.com/tibbe/haskell-style-guide/blob/master/haskell-style.md#list-declarations>
*/
module M
#(int FOO = 1 // comment
, bit BAR = 2 /* comment */
, bit [31:0] BAZ = 2
, parameter int BUZZ = 4
)
( input  var logic i_abc // comment
, inout  var logic b_def /* comment */
, output var logic o_ghi
);

/* Each item on its own line.
Nicest for readability:
- short lines
- every list indented to same level
*/
assign {foo, bar} =
  { i_abc
  , 12'h345
  , b_def     // comment
  , 16'h3456  /* comment */
  };

/* Everything fits on one line.
Omit space after opening parenthesis/bracket/brace.
*/
assign singleline1D = {i_abc, 12'h345, b_def, 16'h3456};
assign singleline2D = {{foo, bar}, {foo, bar}, {foo, bar}};

/* First item on same line.
No indent alignment issue.
*/
assign foobar = { i_abc
                , 12'h345
                , b_def
                , 16'h3456
                };

/* First item on same line, again.
Extra space after `=` to align with indent.
*/
assign foo =  { i_abc
              , 12'h345
              , b_def
              , 16'h3456
              };

/* Multi-dimensional concatenation
Innermost array on one line.
*/
assign matrix2D_A =
  { {elem21, elem20}
  , {elem11, elem10} // comment
  , {elem01, elem00} /* comment */
  };
assign matrix2D_B =
  { { elem21
    , elem20
    }
  , { elem11 // comment
    , elem10 /* comment */
    }
  , { elem01
    , elem00
    }
  };
assign matrix3D_A =
  { { {elem211, elem210}
    , {elem201, elem200}
    }
  , { {elem111, elem110} // comment
    , {elem101, elem100} /* comment */
    }
  , { {elem011, elem010}
    , {elem001, elem000}
    }
  };
assign matrix3D_A =
  { { { elem211
      , elem210
      }
    , { elem201 // comment
      , elem200 /* comment */
      }
    }
  , { { elem110
      , elem110
      }
    , { elem100
      , elem100
      }
    }
  , { { elem010
      , elem010
      }
    , { elem000
      , elem000
      }
    }
  };

endmodule
