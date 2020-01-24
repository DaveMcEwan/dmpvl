#! /usr/bin/env perl
## crc16.pl <bits>
## E.g: crc16.pl 1000111
## NRZ stream is sent in left to right order.
## Generated CRC should also be sent out in left to right order.
sub xor16 {
  local(@x) = @_[0..15];
  local(@y) = @_[16..31];
  local(@results16) = ();
  for($j=0;$j<16;$j++) {
    if (shift(@x) eq shift(@y)) { push(@results16, '0'); }
    else { push(@results16, '1'); }
  }
  return(@results16[0..15]);
}

{
  local($st_data) = $ARGV[0];
  local(@G) = ('1','0','0','0','0','0','0','0','0','0','0','0','0','1','0','1');
  local(@data) = split (//,$st_data);
  local(@hold) = ('1','1','1','1','1','1','1','1','1','1','1','1','1','1','1','1');
  if (scalar(@data) > 0) {
    loop16: while (scalar(@data) > 0) {
      $nextb=shift(@data);
      if (($nextb ne "0") && ($nextb ne "1")) {next loop16}
      if ($nextb eq shift(@hold)) {push(@hold, '0')}
      else { push(@hold, '0'); @hold = &xor16(@hold,@G); }
      print (@hold); print "\n";
    }
  }

  # Invert shift reg contents to generate crc field.
  for ($i=0;$i<=$#hold;$i++) {
    if (@hold[$i] eq "1") {print("0")}
    else {print("1")}
  }
  print "\n";
}
