	.file	"test-write-then-read.original.c"
	.machine ppc
	.section	".text"
	.align 2
	.globl f
	.type	f, @function
f:
.LFB0:
	.cfi_startproc
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	stw 31,28(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	li 9,1
	stw 9,8(31)
	lwz 9,8(31)
	slwi 9,9,1
	mr 3,9
	addi 11,31,32
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	f,.-f
	.globl g
	.section	".sbss","aw",@nobits
	.align 2
g:
	.zero	4
	.size	g, 4
	.type	g, @object
	.section	".text"
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB1:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	mflr 0
	stw 0,20(1)
	stw 31,12(1)
	.cfi_offset 65, 4
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	bl f
	mr 10,3
	lis 9,g@ha
	stw 10,g@l(9)
	nop
	addi 11,31,16
	lwz 0,4(11)
	mtlr 0
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE1:
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 10.3.0-1ubuntu1) 10.3.0"
	.section	.note.GNU-stack,"",@progbits
