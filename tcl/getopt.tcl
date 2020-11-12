
# getopt() usage:
#   Option with default value:
#     getopt argv <shName> <tclName> <defaultValue>
#   OR
#   Boolean flag:
#     set <tclName> [getopt argv <shName>]
#   E.g.
#     $ vivado -mode tcl -tclargs --foo 123 -a
#       % getopt argv --foo abc 456
#       % puts $abc                     --> "123"
#       % getopt argv --bar xyz 789
#       % puts $xyz                     --> "789"
#       % set $boolA [getopt argv a]
#       % puts $boolA                   --> "1"
#       % set $boolB [getopt argv b]
#       % puts $boolB                   --> "0"
# https://wiki.tcl-lang.org/page/getopt
proc getopt {_argv name {_var ""} {default ""}} {
  upvar 1 $_argv argv $_var var
  set pos [lsearch -regexp $argv ^$name]
  if {$pos>=0} {
    set to $pos
    if {$_var ne ""} {
      set var [lindex $argv [incr to]]
    }
    set argv [lreplace $argv $pos $to]
    return 1
  } else {
    if {[llength [info level 0]] == 5} {set var $default}
      return 0
  }
}

