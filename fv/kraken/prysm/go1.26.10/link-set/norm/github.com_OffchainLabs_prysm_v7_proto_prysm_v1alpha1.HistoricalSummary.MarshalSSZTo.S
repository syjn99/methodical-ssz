github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_17d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_162
  mov %rax,0x60(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_6b:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x48(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_147
  mov 0x30(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x38(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_12e
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_13d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_12e:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_13d:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_147:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_162:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_17d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_0
