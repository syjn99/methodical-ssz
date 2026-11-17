github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_199
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x54,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_185
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x14(%rsi),%rdi
  mov %rdi,0x20(%rdx)
  mov 0x1c(%rsi),%rsi
  mov %rsi,0x28(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x30,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_121
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_121:
  mov %rax,0x18(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x24,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x38(%rdx)
  movq $0x30,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_162
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_177
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_162:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_177:
  mov %rsi,0x30(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_185:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_199:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_0
