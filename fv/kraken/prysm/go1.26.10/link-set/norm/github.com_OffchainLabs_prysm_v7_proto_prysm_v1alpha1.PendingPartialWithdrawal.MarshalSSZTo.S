github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_147
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
  lea 0x70(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x70(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_88
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_88:
  mov 0x70(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_d3
  mov %r8,0x48(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_d3:
  mov %r8,-0x8(%rdx,%rbx,1)
  lea 0x8(%rdx),%r8
  mov 0x18(%rax),%r9
  nop
  nop
  nop
  lea 0x50(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x50(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_128
  mov %rdx,0x40(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_128:
  mov 0x50(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_147:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_0
