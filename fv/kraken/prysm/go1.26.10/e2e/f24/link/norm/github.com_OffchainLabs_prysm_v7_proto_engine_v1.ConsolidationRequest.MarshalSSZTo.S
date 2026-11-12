github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_20d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1f2
  mov %rax,0x60(%rsp)
  lea 0x14(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_6b:
  mov %rbx,0x48(%rsp)
  mov %r8,0x38(%rsp)
  mov %rdi,0x30(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x30,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1d7
  mov 0x38(%rsp),%r8
  lea 0x30(%r8),%r9
  mov 0x30(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r9,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %r9,0x38(%rsp)
  mov %rcx,0x30(%rsp)
  add %r8,%rax
  mov $0x30,%ecx
  nop
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x38(%rdx),%rbx
  cmpq $0x30,0x40(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1bc
  mov 0x38(%rsp),%rdx
  lea 0x30(%rdx),%r8
  mov 0x30(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_133
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_15e
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_133:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_15e:
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rax,0x48(%rsp)
  add %rdx,%rax
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1a3
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1b2
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1a3:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1b2:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1bc:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1d7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1f2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_20d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_0
