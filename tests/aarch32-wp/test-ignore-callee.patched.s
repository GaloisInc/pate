	.arch armv5t
	.fpu softvfp
	.eabi_attribute 20, 1
	.eabi_attribute 21, 1
	.eabi_attribute 23, 3
	.eabi_attribute 24, 1
	.eabi_attribute 25, 1
	.eabi_attribute 26, 2
	.eabi_attribute 30, 6
	.eabi_attribute 34, 0
	.eabi_attribute 18, 4
	.file	"test-ignore-callee.patched.c"
	.text
	.global	g
	.data
	.align	2
	.type	g, %object
	.size	g, 4
g:
	.word	-11
	.text
	.align	2
	.global	f
	.syntax unified
	.arm
	.type	f, %function
f:
	@ args = 0, pretend = 0, frame = 0
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	ldr	r3, .L2
	mov	r2, #2
	str	r2, [r3]
	nop
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
.L3:
	.align	2
.L2:
	.word	g
	.size	f, .-f
	.align	2
	.global	_start
	.syntax unified
	.arm
	.type	_start, %function
_start:
	@ args = 0, pretend = 0, frame = 0
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	bl	f
	.syntax divided
@ 13 "test-ignore-callee.patched.c" 1
	mov     %r7, $1
@ 0 "" 2
@ 13 "test-ignore-callee.patched.c" 1
	svc #0
@ 0 "" 2
	.arm
	.syntax unified
	nop
	pop	{fp, pc}
	.size	_start, .-_start
	.ident	"GCC: (Ubuntu 11.2.0-5ubuntu1) 11.2.0"
	.section	.note.GNU-stack,"",%progbits
