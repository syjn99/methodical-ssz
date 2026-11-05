fmt.errorf:
  test %rdi,%rdi
  jne L_fverr_args
  xor %eax,%eax
  retq
L_fverr_args:
  mov $0x1,%eax
  retq
runtime.convT64:
  mov $0x1,%eax
  retq
