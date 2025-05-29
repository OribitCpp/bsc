// RUN: %clang %s %S/asm_function.cbs --target=x86_64-unknown-linux-gnu -o %t.output
// RUN: %t.output
// expected-no-diagnostics

	.text
	.file	"test.c"
	.globl	_asmfunction1                   # -- Begin function _asmfunction1
	.p2align	4, 0x90
	.type	_asmfunction1,@function
_asmfunction1:                          # @_asmfunction1
	.cfi_startproc
# %bb.0:                                # %entry
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	_asmfunction1, .Lfunc_end0-_asmfunction1
	.cfi_endproc
                                        # -- End function
	.ident	"clang version 15.0.4"
	.section	".note.GNU-stack","",@progbits
	.addrsig

// void _asmfunction1(){
//	return;
// }