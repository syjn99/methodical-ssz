github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_196
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_178
  mov %rax,0xa0(%rsp)
  lea 0x14(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_88
  mov %rcx,0xb0(%rsp)
  mov %rdx,0x88(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x88(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_88:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x80(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xa0(%rsp),%rsi
  mov 0x20(%rsi),%rdi
  nop
  nop
  nop
  lea 0x60(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x60(%rsp)
  mov 0x38(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_ef
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_11b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_ef:
  mov 0x80(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_11b:
  mov 0x60(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x28(%rsi),%r8
  nop
  nop
  nop
  lea 0x40(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x40(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_162
  mov %rdx,0x28(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_162:
  mov 0x40(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_178:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_196:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_0
