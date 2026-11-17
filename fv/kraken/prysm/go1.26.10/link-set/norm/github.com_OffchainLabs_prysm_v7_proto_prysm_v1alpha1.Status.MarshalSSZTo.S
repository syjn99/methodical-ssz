github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_0:
  lea -0x38(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2c6
  push %rbp
  mov %rsp,%rbp
  sub $0xb0,%rsp
  mov %rbx,0xc8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2a8
  mov %rax,0xc0(%rsp)
  lea 0x4(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_90
  mov %rcx,0xd0(%rsp)
  mov %rdx,0xa8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xd0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xc0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_90:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x20,0x28(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_28a
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_ec
  mov %rdx,0xa8(%rsp)
  mov %r8,0x50(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%rdx
  mov 0x50(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_ec:
  mov %rdi,0x48(%rsp)
  mov %r9,0x38(%rsp)
  mov %rbx,0xa0(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xc0(%rsp),%rsi
  mov 0x38(%rsi),%rdi
  nop
  nop
  nop
  lea 0x78(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x78(%rsp)
  mov 0x48(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_14f
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_17b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_14f:
  mov 0xa0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_17b:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x40(%rsi),%rbx
  cmpq $0x20,0x48(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_26c
  lea 0x20(%rdx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_1cd
  mov %rdx,0x28(%rsp)
  mov %rbx,0xa8(%rsp)
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rbx,%r8
  mov 0xa8(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_1cd:
  mov %r8,0x30(%rsp)
  mov %rcx,0x40(%rsp)
  mov %rax,0x98(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xc0(%rsp),%rsi
  mov 0x58(%rsi),%rsi
  nop
  nop
  nop
  lea 0x58(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x58(%rsp)
  mov 0x40(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_22f
  mov 0x98(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_253
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_22f:
  mov 0x98(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_253:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_26c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_28a:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2a8:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2c6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_0
