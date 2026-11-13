fmt.errorf:
  test %rdi,%rdi
  jne L_model_errorf_args
  xor %eax,%eax
  retq
L_model_errorf_args:
  mov $0x1,%eax
  retq
runtime.convT64:
  mov runtime.modelBumpPointer(%rip),%rcx
  lea 0x8(%rcx),%rdx
  mov %rdx,runtime.modelBumpPointer(%rip)
  mov %rax,(%rcx)
  mov %rcx,%rax
  retq
