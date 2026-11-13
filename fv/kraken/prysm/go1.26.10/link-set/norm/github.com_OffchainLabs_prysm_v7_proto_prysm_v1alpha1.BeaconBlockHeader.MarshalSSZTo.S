github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_0:
  lea -0x20(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2ff
  push %rbp
  mov %rsp,%rbp
  sub $0x98,%rsp
  mov %rbx,0xb0(%rsp)
  mov %rax,0xa8(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x68(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x68(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_88
  mov %rcx,0xb8(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xb8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_88:
  mov 0x68(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x48(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x48(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_e9
  mov %rdx,0x30(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
  mov 0xa8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_e9:
  mov 0x48(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x20,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2e1
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_14c
  mov %rdx,0x90(%rsp)
  mov %r8,0x28(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rdx
  mov 0x28(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_14c:
  mov %rbx,0x90(%rsp)
  mov %r9,0x40(%rsp)
  mov %rdi,0x38(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xa8(%rsp),%rdx
  mov 0x30(%rdx),%rbx
  cmpq $0x20,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2c2
  mov 0x40(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x38(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1a3
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1d7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1a3:
  mov %rbx,0x88(%rsp)
  mov 0x90(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%r9
  mov 0x88(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1d7:
  mov %rcx,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rax,0x90(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xa8(%rsp),%rdx
  mov 0x48(%rdx),%rbx
  cmpq $0x20,0x50(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2a4
  mov 0x38(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x40(%rsp),%rcx
  nop
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_22f
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_263
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_22f:
  mov %rbx,0x88(%rsp)
  mov 0x90(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%rdx
  mov %rbx,%r8
  mov 0x88(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_263:
  mov %rcx,0x40(%rsp)
  mov %r8,0x38(%rsp)
  mov %rax,0x90(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x90(%rsp),%rax
  mov 0x38(%rsp),%rbx
  mov 0x40(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2a4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2c2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2e1:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2ff:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_0
