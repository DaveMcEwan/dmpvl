// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

    .section .text
    .global irq
    .global main
    .global tb_pass
    .global tb_fail
    .global tb_dumpoff
    .global tb_dumpon
    .global tb_dumpmem
    .global tb_loadmem

reset_vec:
    // No more than 16 bytes here!
    j start

start:

    // Zero-initialize all registers
    addi x1, zero, 0
    addi x2, zero, 0
    addi x3, zero, 0
    addi x4, zero, 0
    addi x5, zero, 0
    addi x6, zero, 0
    addi x7, zero, 0
    addi x8, zero, 0
    addi x9, zero, 0
    addi x10, zero, 0
    addi x11, zero, 0
    addi x12, zero, 0
    addi x13, zero, 0
    addi x14, zero, 0
    addi x15, zero, 0
    addi x16, zero, 0
    addi x17, zero, 0
    addi x18, zero, 0
    addi x19, zero, 0
    addi x20, zero, 0
    addi x21, zero, 0
    addi x22, zero, 0
    addi x23, zero, 0
    addi x24, zero, 0
    addi x25, zero, 0
    addi x26, zero, 0
    addi x27, zero, 0
    addi x28, zero, 0
    addi x29, zero, 0
    addi x30, zero, 0
    addi x31, zero, 0

    // set stack pointer
    lui sp,(64*1024)>>12

    // set gp and tp
    lui gp, %hi(0xdeadbeef)
    addi gp, gp, %lo(0xdeadbeef)
    addi tp, gp, 0

    jal ra,main

    // trap
    ebreak


.balign 32
// Write magic value to mark test as PASS in testbench.v
tb_pass:
    li a0, 0x20000000
    li a1, 0xacce5500
    sw a1,0(a0)
    ret

// Write magic value to unmark test as PASS in testbench.v
tb_fail:
    li a0, 0x20000000
    li a1, 0xacce5501
    sw a1,0(a0)
    ret

// Write magic value to $dumpoff in testbench.v
tb_dumpoff:
    li a0, 0x20000000
    li a1, 0xacce5502
    sw a1,0(a0)
    nop
    nop
    nop
    nop
    ret

// Write magic value to $dumpon in testbench.v
tb_dumpon:
    li a0, 0x20000000
    li a1, 0xacce5503
    sw a1,0(a0)
    nop
    nop
    nop
    nop
    ret

// Write magic value to dump memory contents to memory.hex
tb_dumpmem:
    li a0, 0x20000000
    li a1, 0xacce5504
    sw a1,0(a0)
    ret

