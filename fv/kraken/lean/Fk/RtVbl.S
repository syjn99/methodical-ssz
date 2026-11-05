ssz.ValidateBitlist:
  test %rbx,%rbx
  je L_fvbl_err
  cmp $0x101,%rbx
  ja L_fvbl_err
  movzbl -0x1(%rbx,%rax,1),%ecx
  test %ecx,%ecx
  je L_fvbl_err
  cmp $0x101,%rbx
  jne L_fvbl_ok
  cmp $0x1,%ecx
  jne L_fvbl_err
L_fvbl_ok:
  xor %eax,%eax
  retq
L_fvbl_err:
  mov runtime.fvBump(%rip),%rbx
  lea 0x10(%rbx),%rcx
  mov %rcx,runtime.fvBump(%rip)
  lea go_itab._errors.errorString_error(%rip),%rax
  retq
