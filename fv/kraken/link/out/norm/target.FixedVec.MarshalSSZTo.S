target.FixedVec.MarshalSSZTo:
L_target.FixedVec.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.FixedVec.MarshalSSZTo_136
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  mov %rax,0x78(%rsp)
  test %al,(%rax)
  lea 0x20(%rcx),%rdx
  cmp %rdx,%rdi
  jae L_target.FixedVec.MarshalSSZTo_62
  mov %rcx,0x88(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
  mov 0x78(%rsp),%rax
L_target.FixedVec.MarshalSSZTo_62:
  mov %rbx,0x60(%rsp)
  mov %rdx,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rcx,1),%rdx
  mov %rax,%rbx
  mov $0x20,%ecx
  mov %rdx,%rax
  callq runtime.memmove
  mov 0x78(%rsp),%rdx
  cmpq $0x4,0x28(%rdx)
  jne L_target.FixedVec.MarshalSSZTo_ad
  mov 0x20(%rdx),%r8
  mov %r8,0x58(%rsp)
  mov 0x48(%rsp),%rdi
  mov 0x60(%rsp),%rbx
  mov 0x50(%rsp),%rdx
  xor %eax,%eax
  jmp L_target.FixedVec.MarshalSSZTo_d0
L_target.FixedVec.MarshalSSZTo_ad:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_target.FixedVec.MarshalSSZTo_c8:
  mov %r9,-0x8(%rdx,%rbx,1)
  inc %rax
L_target.FixedVec.MarshalSSZTo_d0:
  cmp $0x4,%rax
  jge L_target.FixedVec.MarshalSSZTo_123
  add $0x8,%rdx
  mov (%r8,%rax,8),%r9
  nop
  cmp %rdx,%rdi
  jae L_target.FixedVec.MarshalSSZTo_c8
  mov %rax,0x50(%rsp)
  mov %r9,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov 0x40(%rsp),%r9
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x50(%rsp),%rax
  jmp L_target.FixedVec.MarshalSSZTo_c8
L_target.FixedVec.MarshalSSZTo_123:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_target.FixedVec.MarshalSSZTo_136:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.FixedVec.MarshalSSZTo_0
