	.file	"test-fun-reorder.patched.c"
	.machine ppc
	.section	".text"
	.globl g
	.section	.sdata,"aw"
	.align 2
	.type	g, @object
	.size	g, 4
g:
	.long	-11
	.globl h
	.align 2
	.type	h, @object
	.size	h, 4
h:
	.long	-12
	.section	".text"
	.align 2
	.globl write_g1
	.type	write_g1, @function
write_g1:
.LFB0:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	stw 31,12(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g@ha
	li 10,1
	stw 10,g@l(9)
	nop
	addi 11,31,16
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	write_g1,.-write_g1
	.align 2
	.globl write_g2
	.type	write_g2, @function
write_g2:
.LFB1:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	stw 31,12(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g@ha
	li 10,2
	stw 10,g@l(9)
	nop
	addi 11,31,16
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE1:
	.size	write_g2,.-write_g2
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB2:
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
	lis 9,h@ha
	lwz 9,h@l(9)
	cmpwi 0,9,0
	bgt 0,.L4
	bl write_g2
	b .L6
.L4:
	bl write_g1
.L6:
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
.LFE2:
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 10.3.0-1ubuntu1) 10.3.0"
	.section	.note.GNU-stack,"",@progbits
