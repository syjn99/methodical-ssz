github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_4a
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov (%rax),%rdx
  mov %rdx,0x40(%rsp)
  lea runtime.zerobase(%rip),%rax
  mov $0x8,%ebx
  xor %ecx,%ecx
  mov %rbx,%rdi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rdx,(%rax)
  mov $0x8,%ebx
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_4a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_0
