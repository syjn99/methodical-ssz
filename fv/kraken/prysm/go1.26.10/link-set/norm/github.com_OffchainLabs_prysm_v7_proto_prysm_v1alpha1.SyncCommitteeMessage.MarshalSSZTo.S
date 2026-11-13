github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_243
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  mov %rax,0xb8(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_88
  mov %rcx,0xc8(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xc8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xb8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_88:
  mov 0x78(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x20,0x18(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_225
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_ec
  mov %rdx,0x30(%rsp)
  mov %r8,0xa0(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov 0xa0(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_ec:
  mov %rdi,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rbx,0x98(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xb8(%rsp),%rsi
  mov 0x28(%rsi),%rdi
  nop
  nop
  nop
  lea 0x58(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x58(%rsp)
  mov 0x40(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_14f
  mov 0x98(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_17b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_14f:
  mov 0x98(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_17b:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x30(%rsi),%rbx
  cmpq $0x60,0x38(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_207
  lea 0x60(%rdx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_1c9
  mov %rbx,0xa0(%rsp)
  mov %rdx,0x28(%rsp)
  mov %r8,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rbx,%r8
  mov 0xa0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_1c9:
  mov %rax,0xa0(%rsp)
  mov %rcx,0x50(%rsp)
  mov %r8,0x48(%rsp)
  add %rdx,%rax
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0xa0(%rsp),%rax
  mov 0x48(%rsp),%rbx
  mov 0x50(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_207:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_225:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_243:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_0
