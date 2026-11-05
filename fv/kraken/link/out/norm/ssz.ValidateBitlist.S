ssz.ValidateBitlist:
L_ssz.ValidateBitlist_0:
  cmp 0x10(%r14),%rsp
  jbe L_ssz.ValidateBitlist_1f9
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rax,0x60(%rsp)
  nop
  test %rbx,%rbx
  je L_ssz.ValidateBitlist_1a8
  mov %rdi,%rdx
  shr $0x3,%rdi
  lea 0x1(%rdi),%r8
  cmp %r8,%rbx
  jg L_ssz.ValidateBitlist_10a
  movzbl -0x1(%rbx,%rax,1),%r8d
  test %r8b,%r8b
  je L_ssz.ValidateBitlist_be
  lea (%r8,%r8,1),%r8d
  lea 0x1(%r8),%r8d
  bsr %r8d,%r8d
  lea (%r8,%rbx,8),%r8
  lea -0x9(%r8),%r8
  nop
  cmp %r8,%rdx
  jae L_ssz.ValidateBitlist_b4
  lea go_string._+5743(%rip),%rax
  mov $0xd,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_ssz.ValidateBitlist_ae
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+5743(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_ae:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_b4:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_be:
  lea go_string._+13272(%rip),%rax
  mov $0x15,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_104
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+13272(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_104:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_10a:
  mov %r8,0x28(%rsp)
  lea 0x30(%rsp),%rcx
  movups %xmm15,(%rcx)
  movups %xmm15,0x10(%rcx)
  mov %rbx,%rax
  callq runtime.convT64
  lea type__+49184(%rip),%rcx
  mov %rcx,0x30(%rsp)
  mov %rax,0x38(%rsp)
  mov 0x28(%rsp),%rax
  nop
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x40(%rsp)
  mov %rax,0x48(%rsp)
  lea go_string._+37115(%rip),%rax
  mov $0x2f,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_1a2
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x2f,0x8(%rax)
  lea go_string._+37115(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_1a2:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_1a8:
  lea go_string._+33605(%rip),%rax
  mov $0x2a,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_1f3
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x2a,0x8(%rax)
  lea go_string._+33605(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_1f3:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_1f9:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_ssz.ValidateBitlist_0
