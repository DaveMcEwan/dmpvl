// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#include "tb.h"

void print_chr(char ch)
{
  *((volatile uint32_t*)PRINT_ADDR) = ch;
}

void print_str(const char *p)
{
  while (*p != 0)
    *((volatile uint32_t*)PRINT_ADDR) = *(p++);
}

void print_dec(unsigned int val)
{
  char buffer[10];
  char *p = buffer;
  while (val || p == buffer) {
    *(p++) = val % 10;
    val = val / 10;
  }
  while (p != buffer) {
    *((volatile uint32_t*)PRINT_ADDR) = '0' + *(--p);
  }
}

void print_hex(unsigned int val, int digits)
{
  for (int i = (4*digits)-4; i >= 0; i -= 4)
    *((volatile uint32_t*)PRINT_ADDR) = "0123456789ABCDEF"[(val >> i) % 16];
}

