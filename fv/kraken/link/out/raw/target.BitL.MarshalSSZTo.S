target.BitL.MarshalSSZTo:
L_target.BitL.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitL.MarshalSSZTo_105
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  nopl (%rax)
  cmp %rdx,%rdi
  jae L_target.BitL.MarshalSSZTo_53
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
L_target.BitL.MarshalSSZTo_53:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%rcx
  mov (%rax),%r8
  cmp $0x800,%rcx
  jg L_target.BitL.MarshalSSZTo_ea
  lea (%rdx,%rcx,1),%r9
  cmp %r9,%rdi
  jae L_target.BitL.MarshalSSZTo_b6
  mov %rdx,0x40(%rsp)
  mov %rcx,0x50(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  lea type__+48736(%rip),%rsi
  mov %rcx,%rdx
  mov %rdi,%rcx
  mov %rdx,%rdi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov 0x58(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov 0x50(%rsp),%rcx
  mov %rax,%rbx
L_target.BitL.MarshalSSZTo_b6:
  mov %rbx,0x58(%rsp)
  mov %r9,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  callq runtime.memmove
  mov 0x58(%rsp),%rax
  mov 0x50(%rsp),%rbx
  mov 0x48(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_ea:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_105:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitL.MarshalSSZTo_0
