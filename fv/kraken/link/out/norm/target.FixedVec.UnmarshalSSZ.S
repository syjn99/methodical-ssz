target.FixedVec.UnmarshalSSZ:
L_target.FixedVec.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.FixedVec.UnmarshalSSZ_ec
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rbx,0x30(%rsp)
  cmp $0x40,%rcx
  jne L_target.FixedVec.UnmarshalSSZ_87
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  test %al,(%rax)
  cmp %rax,%rbx
  je L_target.FixedVec.UnmarshalSSZ_38
  mov $0x20,%ecx
  callq runtime.memmove
L_target.FixedVec.UnmarshalSSZ_38:
  lea type__+48128(%rip),%rax
  mov $0x4,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  movq $0x4,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.FixedVec.UnmarshalSSZ_7a
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.FixedVec.UnmarshalSSZ_7a:
  mov %rax,0x20(%rdx)
  mov 0x30(%rsp),%rcx
  xor %eax,%eax
  jmp L_target.FixedVec.UnmarshalSSZ_a6
L_target.FixedVec.UnmarshalSSZ_87:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.FixedVec.UnmarshalSSZ_9b:
  mov 0x20(%rdx),%rdi
  mov %r9,(%rdi,%rsi,8)
  mov %r8,%rax
L_target.FixedVec.UnmarshalSSZ_a6:
  cmp $0x4,%rax
  jge L_target.FixedVec.UnmarshalSSZ_d6
  mov %rax,%rsi
  shl $0x3,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x3,%rdi
  nop
  cmp %rax,%rdi
  jb L_target.FixedVec.UnmarshalSSZ_e6
  mov 0x28(%rdx),%rdi
  nop
  mov 0x20(%rcx,%rsi,8),%r9
  cmp %rdi,%rsi
  jb L_target.FixedVec.UnmarshalSSZ_9b
  jmp L_target.FixedVec.UnmarshalSSZ_e1
L_target.FixedVec.UnmarshalSSZ_d6:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x18,%rsp
  pop %rbp
  nop
  retq
L_target.FixedVec.UnmarshalSSZ_e1:
  callq runtime.panicBounds
L_target.FixedVec.UnmarshalSSZ_e6:
  callq runtime.panicBounds
  nop
L_target.FixedVec.UnmarshalSSZ_ec:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.FixedVec.UnmarshalSSZ_0
