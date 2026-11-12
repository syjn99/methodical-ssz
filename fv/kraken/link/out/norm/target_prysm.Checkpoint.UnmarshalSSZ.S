target_prysm.Checkpoint.UnmarshalSSZ:
L_target_prysm.Checkpoint.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.Checkpoint.UnmarshalSSZ_f3
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x28,%rcx
  jne L_target_prysm.Checkpoint.UnmarshalSSZ_df
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  mov (%rbx),%rdx
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.Checkpoint.UnmarshalSSZ_7b
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.Checkpoint.UnmarshalSSZ_7b:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.Checkpoint.UnmarshalSSZ_bc
  mov 0x18(%rsp),%rsi
  jmp L_target_prysm.Checkpoint.UnmarshalSSZ_d1
L_target_prysm.Checkpoint.UnmarshalSSZ_bc:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.Checkpoint.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.UnmarshalSSZ_df:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.UnmarshalSSZ_f3:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.Checkpoint.UnmarshalSSZ_0
