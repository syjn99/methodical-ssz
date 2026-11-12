fmt.errorf:
  test %rdi,%rdi
  jne L_fverr_args
  xor %eax,%eax
  retq
L_fverr_args:
  mov $0x1,%eax
  retq
runtime.convT64:
  mov runtime.fvBump(%rip),%rcx
  lea 0x8(%rcx),%rdx
  mov %rdx,runtime.fvBump(%rip)
  mov %rax,(%rcx)
  mov %rcx,%rax
  retq
