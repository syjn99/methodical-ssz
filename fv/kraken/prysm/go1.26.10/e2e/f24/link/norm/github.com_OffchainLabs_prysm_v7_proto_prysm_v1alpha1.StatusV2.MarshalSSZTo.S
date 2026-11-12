github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_0:
  lea -0x60(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_321
  push %rbp
  mov %rsp,%rbp
  sub $0xd8,%rsp
  mov %rbx,0xf0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_302
  mov %rax,0xe8(%rsp)
  lea 0x4(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_90
  mov %rcx,0xf8(%rsp)
  mov %rdx,0xd0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xe8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_90:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x20,0x28(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2e4
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_ec
  mov %rdx,0xd0(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov 0x58(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_ec:
  mov %rdi,0x50(%rsp)
  mov %r9,0x40(%rsp)
  mov %rbx,0xc8(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe8(%rsp),%rsi
  mov 0x38(%rsi),%rdi
  nop
  nop
  nop
  lea 0xa0(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0xa0(%rsp)
  mov 0x50(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_154
  mov 0xc8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_180
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_154:
  mov 0xc8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_180:
  mov 0xa0(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x40(%rsi),%rbx
  cmpq $0x20,0x48(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2c6
  lea 0x20(%rdx),%r8
  nop
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_1d6
  mov %rdx,0x30(%rsp)
  mov %rbx,0xd0(%rsp)
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0xd0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_1d6:
  mov %rcx,0x48(%rsp)
  mov %r8,0x38(%rsp)
  mov %rax,0xc0(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe8(%rsp),%rsi
  mov 0x58(%rsi),%rdi
  nop
  nop
  nop
  lea 0x80(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x80(%rsp)
  mov 0x48(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_23a
  mov 0xc0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_266
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_23a:
  mov 0xc0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_266:
  mov 0x80(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x60(%rsi),%r8
  nop
  nop
  nop
  lea 0x60(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x60(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2b0
  mov %rdx,0x28(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2b0:
  mov 0x60(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2c6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2e4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_302:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_321:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_0
