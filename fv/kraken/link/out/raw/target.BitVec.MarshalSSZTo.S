target.BitVec.MarshalSSZTo:
L_target.BitVec.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.MarshalSSZTo_15a
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rax,0x60(%rsp)
  mov %rdi,0x78(%rsp)
  mov %rcx,0x70(%rsp)
  mov %rbx,0x68(%rsp)
  mov (%rax),%rdx
  mov 0x8(%rax),%rbx
  mov 0x10(%rax),%rcx
  mov %rdx,%rax
  mov $0x4,%edi
  callq ssz.ValidateBitvector
  data16 nop
  test %rax,%rax
  je L_target.BitVec.MarshalSSZTo_ba
  movups %xmm15,0x40(%rsp)
  je L_target.BitVec.MarshalSSZTo_51
  mov 0x8(%rax),%rax
L_target.BitVec.MarshalSSZTo_51:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+511(%rip),%rax
  mov $0x5,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.BitVec.MarshalSSZTo_a7
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+511(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.BitVec.MarshalSSZTo_a7:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_ba:
  mov 0x60(%rsp),%rdx
  mov (%rdx),%r8
  cmpq $0x1,0x8(%rdx)
  jne L_target.BitVec.MarshalSSZTo_13f
  mov 0x70(%rsp),%rdx
  lea 0x1(%rdx),%r9
  mov 0x78(%rsp),%rcx
  cmp %r9,%rcx
  jb L_target.BitVec.MarshalSSZTo_e3
  mov 0x68(%rsp),%rsi
  jmp L_target.BitVec.MarshalSSZTo_125
L_target.BitVec.MarshalSSZTo_e3:
  mov %r8,0x38(%rsp)
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  mov 0x68(%rsp),%rax
  mov %r9,%rbx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x70(%rsp),%rdx
  mov 0x38(%rsp),%r8
  mov %rax,%rsi
  mov %rbx,%r9
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
L_target.BitVec.MarshalSSZTo_125:
  movzbl (%r8),%r8d
  mov %r8b,(%rsi,%rdx,1)
  mov %rax,%rdi
  mov %rsi,%rax
  mov %rbx,%rsi
  mov %r9,%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_13f:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_15a:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitVec.MarshalSSZTo_0
