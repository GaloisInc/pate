	.file	"test-stack-region-preserved.original.c"
	.section	".text"
	.comm	x,8,8
	.section	".toc","aw"
	.align 3
.LC0:
	.quad	x
	.section	".text"
	.align 2
	.globl _start
	.section	".opd","aw"
	.align 3
_start:
	.quad	.L._start,.TOC.@tocbase,0
	.previous
	.type	_start, @function
.L._start:
.LFB0:
	.cfi_startproc
	std 31,-8(1)
	stdu 1,-80(1)
	.cfi_def_cfa_offset 80
	.cfi_offset 31, -8
	mr 31,1
	.cfi_def_cfa_register 31
	li 9,1
	stw 9,48(31)
	addis 8,2,.LC0@toc@ha
	ld 9,.LC0@toc@l(8)
	addi 10,31,48
	std 10,0(9)
	ld 9,.LC0@toc@l(8)
	ld 9,0(9)
	li 10,1
	stw 10,0(9)
	nop
	addi 1,31,80
	.cfi_def_cfa 1, 0
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.cfi_endproc
.LFE0:
	.size	_start,.-.L._start
	.ident	"GCC: (Ubuntu 9.3.0-17ubuntu1~20.04) 9.3.0"
