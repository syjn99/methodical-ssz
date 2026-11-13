github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_101
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_e6
  mov %rax,0x78(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_74
  mov %rcx,0x88(%rsp)
  mov %rdx,0x60(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_74:
  mov %rbx,0x58(%rsp)
  mov %r8,0x48(%rsp)
  mov %rdi,0x50(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  add $0x8,%rbx
  mov 0x78(%rsp),%rdx
  mov 0x20(%rdx),%rdx
  mov 0x50(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_b7
  mov 0x58(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_d7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_b7:
  mov %rdx,0x40(%rsp)
  mov 0x58(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_d7:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_e6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_101:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_0
