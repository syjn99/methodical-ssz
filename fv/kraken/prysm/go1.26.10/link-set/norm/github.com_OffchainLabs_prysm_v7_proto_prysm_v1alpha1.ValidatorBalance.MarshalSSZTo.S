github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_d6
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x48(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x48(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_7b
  mov %rax,0x78(%rsp)
  mov %rcx,0x88(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
  mov 0x78(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_7b:
  mov 0x48(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_be
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_be:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_d6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_0
