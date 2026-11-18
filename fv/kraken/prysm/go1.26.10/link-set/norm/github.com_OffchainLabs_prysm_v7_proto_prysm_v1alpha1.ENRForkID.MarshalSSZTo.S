github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_177
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_15c
  mov %rax,0x70(%rsp)
  lea 0x4(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_76
  mov %rcx,0x80(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x80(%rsp),%rcx
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_76:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x4,0x28(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_141
  lea 0x4(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_cf
  mov %r8,0x50(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov 0x50(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_cf:
  mov (%rdx),%edx
  mov %edx,(%rbx,%r8,1)
  lea 0x8(%r9),%rdx
  mov 0x38(%rax),%r8
  nop
  nop
  nop
  lea 0x30(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r8,0x30(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_125
  mov %r9,0x28(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%r9
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_125:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%r9,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_141:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_15c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_177:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_0
