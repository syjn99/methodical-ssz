ssz.ValidateBitvector:
L_ssz.ValidateBitvector_0:
  cmp 0x10(%r14),%rsp
  jbe L_ssz.ValidateBitvector_c0
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  mov %rdi,%rcx
  and $0x7,%ecx
  shr $0x3,%rdi
  test %rcx,%rcx
  setne %dl
  movzbl %dl,%edx
  add %rdi,%rdx
  cmp %rdx,%rbx
  jne L_ssz.ValidateBitvector_a6
  test %rcx,%rcx
  je L_ssz.ValidateBitvector_9c
  lea -0x1(%rbx),%rdx
  nopl (%rax,%rax,1)
  cmp %rdx,%rbx
  jbe L_ssz.ValidateBitvector_ba
  movzbl -0x1(%rbx,%rax,1),%edx
  shr %cl,%dl
  test %dl,%dl
  je L_ssz.ValidateBitvector_9c
  lea go_string._+27706(%rip),%rax
  mov $0x23,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitvector_96
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x23,0x8(%rax)
  lea go_string._+27706(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitvector_96:
  add $0x28,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitvector_9c:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x28,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitvector_a6:
  mov ssz.ErrBytesLength(%rip),%rax
  mov ssz.ErrBytesLength+8(%rip),%rbx
  add $0x28,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitvector_ba:
  callq runtime.panicBounds
  nop
L_ssz.ValidateBitvector_c0:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_ssz.ValidateBitvector_0
