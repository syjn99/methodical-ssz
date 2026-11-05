target_prysm.AttestationData.UnmarshalSSZ:
L_target_prysm.AttestationData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.AttestationData.UnmarshalSSZ_2cb
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rbx,0x40(%rsp)
  nop
  cmp $0x80,%rcx
  jne L_target_prysm.AttestationData.UnmarshalSSZ_2b7
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  mov (%rbx),%rdx
  mov %rdx,(%rax)
  mov 0x8(%rbx),%rdx
  mov %rdx,0x8(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x38(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_86
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_86:
  mov %rax,0x20(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x10,%rbx
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x38(%rsp),%rdx
  movq $0x20,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_ca
  mov 0x20(%rsp),%rbx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_df
L_target_prysm.AttestationData.UnmarshalSSZ_ca:
  mov 0x10(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rbx
  mov %rbx,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_df:
  mov %rbx,0x10(%rdx)
  lea type__+100288(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_ff
  mov 0x38(%rsp),%rdx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_114
L_target_prysm.AttestationData.UnmarshalSSZ_ff:
  mov 0x38(%rsp),%rdx
  mov 0x28(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_114:
  mov %rax,0x18(%rsp)
  mov %rax,0x28(%rdx)
  mov 0x40(%rsp),%rdx
  mov 0x30(%rdx),%rdx
  nop
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x18(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_16c
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_16c:
  mov %rax,0x20(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x38,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x18(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_1ad
  mov 0x20(%rsp),%rbx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_1c2
L_target_prysm.AttestationData.UnmarshalSSZ_1ad:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rbx
  mov %rbx,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_1c2:
  mov %rbx,0x8(%rdx)
  lea type__+100288(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_1e2
  mov 0x38(%rsp),%rdx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_1f7
L_target_prysm.AttestationData.UnmarshalSSZ_1e2:
  mov 0x38(%rsp),%rdx
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_1f7:
  mov %rax,0x18(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x40(%rsp),%rdx
  mov 0x58(%rdx),%rdx
  nop
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x18(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_253
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_253:
  mov %rax,0x20(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x60,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x18(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_294
  mov 0x20(%rsp),%rsi
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_2a9
L_target_prysm.AttestationData.UnmarshalSSZ_294:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_2a9:
  mov %rsi,0x8(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x28,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.UnmarshalSSZ_2b7:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x28,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.UnmarshalSSZ_2cb:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  nop
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.AttestationData.UnmarshalSSZ_0
