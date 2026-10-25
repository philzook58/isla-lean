/* RV64I ports of pcode-lean's examples/routines.S and tests/probes.S (no compressed encodings).
   Calling convention: arguments in a0..a3, results in a0 (and a1/a2 where noted), return via ra.
   afgap64 has no port: RISC-V has no flags, so there is no auxiliary-carry behavior to witness. */
.option norvc

.section .text.inc64,"ax",@progbits
.globl inc64
inc64:
  addi a0, a0, 1
  ret

.section .text.umax64,"ax",@progbits
.globl umax64
umax64:
  bgeu a0, a1, 1f
  mv a0, a1
1:
  ret

.section .text.count64,"ax",@progbits
.globl count64
count64:
  li t0, 0
  beqz a0, 2f
1:
  addi t0, t0, 1
  addi a0, a0, -1
  bnez a0, 1b
2:
  mv a0, t0
  ret

/* OR of a0 64-bit limbs at a1. */
.section .text.scan64,"ax",@progbits
.globl scan64
scan64:
  li t0, 0
  beqz a0, 2f
1:
  ld t1, 0(a1)
  or t0, t0, t1
  addi a1, a1, 8
  addi a0, a0, -1
  bnez a0, 1b
2:
  mv a0, t0
  ret

/* (a1:a0) + (a3:a2), returning (a1:a0) with the carry beyond 128 bits in a2. */
.section .text.add128,"ax",@progbits
.globl add128
add128:
  add t0, a0, a2
  sltu t1, t0, a0
  add a1, a1, a3
  sltu t2, a1, a3
  add a1, a1, t1
  sltu t3, a1, t1
  or a2, t2, t3
  mv a0, t0
  ret

/* Two-limb add of the buffers at a1 and a2 into a0; returns the carry. Like the x86 version, the
   high limbs are loaded after the low limb is stored. */
.section .text.addmem,"ax",@progbits
.globl addmem
addmem:
  ld t0, 0(a1)
  ld t1, 0(a2)
  add t2, t0, t1
  sltu t3, t2, t0
  sd t2, 0(a0)
  ld t0, 8(a1)
  ld t1, 8(a2)
  add t2, t0, t1
  sltu t4, t2, t0
  add t2, t2, t3
  sltu t5, t2, t3
  or t4, t4, t5
  sd t2, 8(a0)
  mv a0, t4
  ret

/* Store a2 into a1 consecutive limbs at a0. */
.section .text.fill64,"ax",@progbits
.globl fill64
fill64:
  beqz a1, 2f
1:
  sd a2, 0(a0)
  addi a0, a0, 8
  addi a1, a1, -1
  bnez a1, 1b
2:
  ret

.section .text.stack32,"ax",@progbits
.globl stack32
stack32:
  addi sp, sp, -32
  sd a0, 0(sp)
  addi sp, sp, 32
  ret

.section .text.reserve256,"ax",@progbits
.globl reserve256
reserve256:
  addi sp, sp, -256
  addi sp, sp, 256
  ret

/* Probes. alias64: 32-bit W operations sign-extend (RISC-V's analogue of x86 sub-register writes). */
.section .text.alias64,"ax",@progbits
.globl alias64
alias64:
  addw a0, a0, a1
  addiw a0, a0, 0x5a
  ret

/* stack64: push/add-in-memory/pop through the stack. */
.section .text.stack64,"ax",@progbits
.globl stack64
stack64:
  addi sp, sp, -8
  sd a0, 0(sp)
  ld t0, 0(sp)
  add t0, t0, a1
  sd t0, 0(sp)
  ld a0, 0(sp)
  addi sp, sp, 8
  ret

/* shift64: shift counts are taken modulo 64. */
.section .text.shift64,"ax",@progbits
.globl shift64
shift64:
  sll a0, a0, a1
  ret
