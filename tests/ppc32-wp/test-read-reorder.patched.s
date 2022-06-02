	.file	"test-read-reorder.patched.c"
	.machine ppc
	.section	".text"
	.globl g
	.section	.sdata,"aw"
	.align 2
	.type	g, @object
	.size	g, 4
g:
	.long	-11
	.globl b
	.section	".sbss","aw",@nobits
	.align 2
b:
	.zero	4
	.size	b, 4
	.type	b, @object
	.section	".text"
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB0:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	stw 31,12(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g@ha
	lwz 9,g@l(9)
	cmpwi 0,9,9
	bgt 0,.L2
	lis 9,g@ha
	lwz 9,g@l(9)
	cmpwi 0,9,0
	ble 0,.L2
	li 9,1
	b .L3
.L2:
	li 9,0
.L3:
	lis 10,b@ha
	stw 9,b@l(10)
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
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 10.3.0-1ubuntu1) 10.3.0"
	.section	.note.GNU-stack,"",@progbits
