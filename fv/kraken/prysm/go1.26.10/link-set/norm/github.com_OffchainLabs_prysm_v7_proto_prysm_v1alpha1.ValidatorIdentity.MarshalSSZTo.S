github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_1aa
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov %rax,0xa0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x60(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x60(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_88
  mov %rcx,0xb0(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_88:
  mov 0x60(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x30,0x18(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_18c
  lea 0x30(%rdx),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_ec
  mov %rdx,0x28(%rsp)
  mov %r8,0x88(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov 0x88(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_ec:
  mov %rbx,0x80(%rsp)
  mov %r9,0x30(%rsp)
  mov %rdi,0x38(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xa0(%rsp),%rsi
  mov 0x28(%rsi),%rsi
  nop
  nop
  nop
  lea 0x40(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x40(%rsp)
  mov 0x38(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_14f
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_173
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_14f:
  mov 0x80(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_173:
  mov 0x40(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_18c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_1aa:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_0
