github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_0:
  lea -0x58(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_281
  push %rbp
  mov %rsp,%rbp
  sub $0xd0,%rsp
  mov %rbx,0xe8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_262
  mov %rax,0xe0(%rsp)
  lea 0x20(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_88
  mov %rdx,0xc8(%rsp)
  mov %rcx,0xf0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_88:
  mov %rdi,0x60(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,0xb8(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe0(%rsp),%rsi
  mov 0x20(%rsi),%rdi
  nop
  nop
  nop
  lea 0x98(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x98(%rsp)
  mov 0x60(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_f0
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_11c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_f0:
  mov 0xb8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x58(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_11c:
  mov 0x98(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x28(%rsi),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_172
  mov %rdx,0x48(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov 0xe0(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_172:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  mov 0x30(%rsi),%rdx
  cmpq $0x14,0x38(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_244
  lea 0x14(%rbx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_1c4
  mov %rbx,0x40(%rsp)
  mov %rdx,0xc8(%rsp)
  mov %r8,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_1c4:
  mov %r8,0x68(%rsp)
  mov %rax,0xc0(%rsp)
  mov %rcx,0x70(%rsp)
  add %rbx,%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov 0xe0(%rsp),%rdx
  mov 0x48(%rdx),%rdx
  mov 0x70(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_20f
  mov 0xc0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_232
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_20f:
  mov %rdx,0x50(%rsp)
  mov 0xc0(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_232:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_244:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_262:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_281:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_0
