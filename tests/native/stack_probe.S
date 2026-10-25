/* Read back stack32's scratch store after it restores sp (mirrors pcode-lean's stack_probe.S). */
.option norvc
.section .text.probe_stack32,"ax",@progbits
.globl probe_stack32
probe_stack32:
  mv t6, ra
  call stack32
  ld a0, -32(sp)
  mv ra, t6
  ret
