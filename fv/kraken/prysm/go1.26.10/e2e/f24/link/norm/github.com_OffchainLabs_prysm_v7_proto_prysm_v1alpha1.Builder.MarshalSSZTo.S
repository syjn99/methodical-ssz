github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_0:
  lea -0x58(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_319
  push %rbp
  mov %rsp,%rbp
  sub $0xd0,%rsp
  mov %rbx,0xe8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2fb
  mov %rax,0xe0(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_88
  mov %rcx,0xf0(%rsp)
  mov %rdx,0xc8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_88:
  mov %rdi,0x50(%rsp)
  mov %r8,0x48(%rsp)
  mov %rbx,0xc8(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xe0(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  cmpq $0x1,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2dd
  mov 0x48(%rsp),%rbx
  lea 0x1(%rbx),%r8
  mov 0x50(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_e3
  mov 0xc8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_11f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_e3:
  mov %rsi,0xc0(%rsp)
  mov 0xc8(%rsp),%rax
  mov %r8,%rbx
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rdx
  mov 0xc0(%rsp),%rsi
  mov %rbx,%r8
  mov 0x48(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_11f:
  movzbl (%rsi),%r9d
  mov %r9b,(%rax,%rbx,1)
  mov 0x38(%rdx),%rbx
  cmpq $0x14,0x40(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2bf
  lea 0x14(%r8),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_175
  mov %rbx,0xc8(%rsp)
  mov %r8,0x50(%rsp)
  mov %r9,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x50(%rsp),%r8
  mov %rbx,%r9
  mov 0xc8(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_175:
  mov %rcx,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rax,0xb8(%rsp)
  add %r8,%rax
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe0(%rsp),%rsi
  mov 0x50(%rsi),%rdi
  nop
  nop
  nop
  lea 0x98(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x98(%rsp)
  mov 0x40(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_1d9
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_205
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_1d9:
  mov 0xb8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_205:
  mov 0x98(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x58(%rsi),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_257
  mov %rdx,0x30(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov 0xe0(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_257:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  lea 0x8(%rbx),%rdx
  mov 0x60(%rsi),%r8
  nop
  nop
  nop
  lea 0x58(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x58(%rsp)
  nop
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2a6
  mov %rbx,0x28(%rsp)
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x28(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2a6:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2bf:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2dd:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2fb:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_319:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_0
