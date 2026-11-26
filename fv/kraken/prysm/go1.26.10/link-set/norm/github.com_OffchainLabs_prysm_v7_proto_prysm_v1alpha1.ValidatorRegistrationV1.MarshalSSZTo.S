github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1f3
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1d5
  mov %rax,0x98(%rsp)
  lea 0x14(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_88
  mov %rdx,0x80(%rsp)
  mov %rcx,0xa8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_88:
  mov %rbx,0x78(%rsp)
  mov %r8,0x58(%rsp)
  mov %rdi,0x60(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  mov 0x60(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_ce
  mov 0x78(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_f6
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_ce:
  mov %rsi,0x50(%rsp)
  mov 0x78(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x50(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_f6:
  mov %rsi,-0x8(%rbx,%rax,1)
  add $0x8,%rbx
  mov 0x28(%rdx),%r8
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_12b
  mov %r8,0x48(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x48(%rsp),%r8
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_12b:
  mov %r8,-0x8(%rbx,%rax,1)
  mov 0x30(%rdx),%r8
  cmpq $0x30,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1b7
  lea 0x30(%rbx),%rdx
  nop
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_176
  mov %rbx,0x40(%rsp)
  mov %r8,0x80(%rsp)
  mov %rdx,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_176:
  mov %rdx,0x70(%rsp)
  mov %rcx,0x68(%rsp)
  mov %rax,0x80(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  mov 0x70(%rsp),%rbx
  mov 0x68(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1b7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1d5:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1f3:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_0
