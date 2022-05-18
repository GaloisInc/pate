	.file	"test-int-ref.original.c"
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
	stw 3,8(31)
	lwz 9,8(31)
	li 10,1
	stw 10,0(9)
	lwz 9,8(31)
	lwz 9,0(9)
	cmpwi 0,9,1
	bne 0,.L2
	li 9,1
	b .L3
.L2:
	li 9,0
.L3:
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
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	mflr 0
	stw 0,36(1)
	stw 31,28(1)
	.cfi_offset 65, 4
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g@ha
	la 9,g@l(9)
	stw 9,8(31)
	lis 9,g@ha
	la 3,g@l(9)
	bl f
	nop
	addi 11,31,32
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
