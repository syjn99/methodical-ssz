target.BitVec.MarshalSSZTo:
L_target.BitVec.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.MarshalSSZTo_96
  push %rbp
  mov %rsp,%rbp
  sub $0x30,%rsp
  mov %rbx,0x48(%rsp)
  mov (%rax),%rdx
  cmpq $0x1,0x8(%rax)
  nop
  jne L_target.BitVec.MarshalSSZTo_7b
  lea 0x1(%rcx),%r8
  cmp %r8,%rdi
  jae L_target.BitVec.MarshalSSZTo_62
  mov %rdx,0x28(%rsp)
  mov %rcx,0x50(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x50(%rsp),%rcx
  mov %rax,%rbx
L_target.BitVec.MarshalSSZTo_62:
  movzbl (%rdx),%edx
  mov %dl,(%rbx,%rcx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x30,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_7b:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x30,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_96:
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
