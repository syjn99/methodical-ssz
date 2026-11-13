github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_20b
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov %rax,0xa0(%rsp)
  mov %rcx,0xb0(%rsp)
  mov %rdi,%rdx
  sub %rcx,%rdi
  nop
  cmp $0x28,%rdi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_e5
  lea 0x28(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  movups %xmm15,0x18(%r8)
  lea 0x28(%rcx),%r9
  cmp %r9,%rdx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_98
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdx,%rcx
  mov $0x28,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  lea 0x28(%rsp),%r8
  mov %rcx,%rdx
  mov %rax,%rbx
  mov 0xb0(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_98:
  mov %rdx,0x80(%rsp)
  mov %rbx,0x88(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %r8,%rbx
  mov $0x28,%ecx
  callq runtime.memmove
  mov 0xb0(%rsp),%rbx
  mov 0x80(%rsp),%rdx
  cmp %rdx,%rbx
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_205
  mov 0xa0(%rsp),%rax
  mov %rbx,%rcx
  mov 0x88(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_e5:
  lea 0x8(%rcx),%r8
  mov 0x8(%rax),%r9
  nop
  nop
  nop
  lea 0x58(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x58(%rsp)
  cmp %r8,%rdx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_13e
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdx,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rcx,%rdx
  mov %rbx,%r8
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_13e:
  mov 0x58(%rsp),%r9
  mov %r9,(%rbx,%rcx,1)
  mov 0x10(%rax),%r9
  cmpq $0x20,0x18(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_1e7
  lea 0x20(%r8),%r10
  cmp %r10,%rdx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_19c
  mov %r9,0x88(%rsp)
  mov %r8,0x50(%rsp)
  mov %rbx,%rax
  mov %r10,%rbx
  mov %rdx,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%r8
  mov 0x88(%rsp),%r9
  mov %rcx,%rdx
  mov %rbx,%r10
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_19c:
  mov %rdx,0x80(%rsp)
  mov %r10,0x78(%rsp)
  mov %rbx,0x88(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %r9,%rbx
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x88(%rsp),%rax
  mov 0x78(%rsp),%rbx
  mov 0x80(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_1e7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_205:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_20b:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_0
