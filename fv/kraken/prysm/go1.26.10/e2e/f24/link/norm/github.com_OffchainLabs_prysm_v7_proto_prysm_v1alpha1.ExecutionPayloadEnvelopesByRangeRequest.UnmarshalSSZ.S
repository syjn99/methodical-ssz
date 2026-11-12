github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_e1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_cc
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+29259(%rip),%rax
  mov $0xd,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29259(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rcx
  mov 0x48(%rsp),%rdx
  mov %rcx,0x10(%rdx)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_cc:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_0
