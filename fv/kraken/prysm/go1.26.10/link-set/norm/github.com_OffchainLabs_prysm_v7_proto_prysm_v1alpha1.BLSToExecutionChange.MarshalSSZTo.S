github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1c2
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  mov %rax,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x30(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x30(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_80
  mov %rcx,0x90(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x90(%rsp),%rcx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_80:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x30,0x18(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1a7
  lea 0x30(%rdx),%r9
  nop
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_dc
  mov %r8,0x68(%rsp)
  mov %rdx,0x28(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov 0x68(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_dc:
  mov %rdi,0x58(%rsp)
  mov %r9,0x50(%rsp)
  mov %rbx,0x68(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  mov 0x28(%rdx),%rbx
  cmpq $0x14,0x30(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_18c
  mov 0x50(%rsp),%rdx
  lea 0x14(%rdx),%r8
  mov 0x58(%rsp),%rcx
  nop
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_12c
  mov 0x68(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_157
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_12c:
  mov %rbx,0x60(%rsp)
  mov 0x68(%rsp),%rax
  mov %r8,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
  mov %rbx,%r8
  mov 0x60(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_157:
  mov %r8,0x58(%rsp)
  mov %rax,0x68(%rsp)
  mov %rcx,0x50(%rsp)
  add %rdx,%rax
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rax
  mov 0x58(%rsp),%rbx
  mov 0x50(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_18c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1a7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1c2:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_0
