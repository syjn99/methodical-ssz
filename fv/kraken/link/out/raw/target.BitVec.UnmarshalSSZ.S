target.BitVec.UnmarshalSSZ:
L_target.BitVec.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.UnmarshalSSZ_cd
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rbx,0x30(%rsp)
  nopw (%rax,%rax,1)
  cmp $0x1,%rcx
  jne L_target.BitVec.UnmarshalSSZ_b9
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x1,%ecx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_74
  mov (%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_74:
  mov %rax,(%rdx)
  mov 0x30(%rsp),%rcx
  movzbl (%rcx),%ecx
  mov %cl,(%rax)
  movq $0x1,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_ac
  mov (%rdx),%rcx
  nopl (%rax)
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_ac:
  mov %rax,(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_b9:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_cd:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitVec.UnmarshalSSZ_0
