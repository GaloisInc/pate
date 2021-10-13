	.file	"test-fun-reorder-args.original.c"
	.machine ppc
	.section	".text"
	.globl g
	.section	.sdata,"aw"
	.align 2
	.type	g, @object
	.size	g, 4
g:
	.long	-11
	.globl f
	.align 2
	.type	f, @object
	.size	f, 4
f:
	.long	-13
	.globl h
	.align 2
	.type	h, @object
	.size	h, 4
h:
	.long	-12
	.section	".text"
	.align 2
	.globl write_g
	.type	write_g, @function
write_g:
.LFB0:
	.cfi_startproc
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	stw 31,28(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	stw 3,8(31)
	stw 4,12(31)
	lwz 10,8(31)
	lwz 9,12(31)
	add 10,10,9
	lis 9,g@ha
	stw 10,g@l(9)
	nop
	addi 11,31,32
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	write_g,.-write_g
	.align 2
	.globl write_f
	.type	write_f, @function
write_f:
.LFB1:
	.cfi_startproc
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	stw 31,28(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	stw 3,8(31)
	lis 9,f@ha
	lwz 10,8(31)
	stw 10,f@l(9)
	nop
	addi 11,31,32
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE1:
	.size	write_f,.-write_f
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB2:
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
	lis 9,f@ha
	li 10,0
	stw 10,f@l(9)
	lis 9,g@ha
	li 10,0
	stw 10,g@l(9)
	li 9,1
	stw 9,8(31)
	lis 9,h@ha
	lwz 9,h@l(9)
	cmpwi 0,9,0
	ble 0,.L4
	li 4,2
	lwz 3,8(31)
	bl write_g
	b .L6
.L4:
	lwz 3,8(31)
	bl write_f
.L6:
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
.LFE2:
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 10.3.0-1ubuntu1) 10.3.0"
	.section	.note.GNU-stack,"",@progbits
