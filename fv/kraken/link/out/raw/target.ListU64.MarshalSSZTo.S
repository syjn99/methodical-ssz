target.ListU64.MarshalSSZTo:
L_target.ListU64.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.ListU64.MarshalSSZTo_102
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  nopl (%rax)
  cmp %rdx,%rdi
  jae L_target.ListU64.MarshalSSZTo_53
  mov %rax,0x70(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x70(%rsp),%rax
L_target.ListU64.MarshalSSZTo_53:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%r8
  nop
  cmp $0x10,%r8
  jg L_target.ListU64.MarshalSSZTo_77
  mov %r8,0x50(%rsp)
  mov (%rax),%r9
  mov %r9,0x58(%rsp)
  xor %eax,%eax
  jmp L_target.ListU64.MarshalSSZTo_9a
L_target.ListU64.MarshalSSZTo_77:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_target.ListU64.MarshalSSZTo_92:
  mov %r10,-0x8(%rdx,%rbx,1)
  inc %rax
L_target.ListU64.MarshalSSZTo_9a:
  cmp %r8,%rax
  jge L_target.ListU64.MarshalSSZTo_ef
  add $0x8,%rdx
  mov (%r9,%rax,8),%r10
  cmp %rdx,%rdi
  jae L_target.ListU64.MarshalSSZTo_92
  mov %rax,0x48(%rsp)
  mov %r10,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%r8
  mov 0x58(%rsp),%r9
  mov 0x40(%rsp),%r10
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x48(%rsp),%rax
  jmp L_target.ListU64.MarshalSSZTo_92
L_target.ListU64.MarshalSSZTo_ef:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_target.ListU64.MarshalSSZTo_102:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.ListU64.MarshalSSZTo_0
