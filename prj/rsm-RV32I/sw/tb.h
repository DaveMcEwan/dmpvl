// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#ifndef TB_H
#define TB_H

#include <stdint.h>

#define PRINT_ADDR 0x10000000

void print_chr(char ch);
void print_str(const char *p);
void print_dec(unsigned int val);
void print_hex(unsigned int val, int digits);

// testbench.v
void tb_pass(void);
void tb_fail(void);
void tb_dumpoff(void);
void tb_dumpon(void);
void tb_dumpmem(void);

#endif
