target_prysm.Checkpoint.MarshalSSZTo:
L_target_prysm.Checkpoint.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.Checkpoint.MarshalSSZTo_101
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  cmp %rdx,%rdi
  jae L_target_prysm.Checkpoint.MarshalSSZTo_5d
  mov %rax,0x78(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x78(%rsp),%rax
L_target_prysm.Checkpoint.MarshalSSZTo_5d:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov 0x8(%rax),%r8
  cmpq $0x20,0x10(%rax)
  jne L_target_prysm.Checkpoint.MarshalSSZTo_e6
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_target_prysm.Checkpoint.MarshalSSZTo_ad
  mov %rdx,0x40(%rsp)
  mov %r8,0x60(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov 0x60(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov %rax,%rbx
L_target_prysm.Checkpoint.MarshalSSZTo_ad:
  mov %rbx,0x60(%rsp)
  mov %r9,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  mov 0x50(%rsp),%rbx
  mov 0x48(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.MarshalSSZTo_e6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.MarshalSSZTo_101:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.Checkpoint.MarshalSSZTo_0
