github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_0:
  lea -0x48(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2e1
  push %rbp
  mov %rsp,%rbp
  sub $0xc0,%rsp
  mov %rbx,0xd8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2c2
  mov %rax,0xd0(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_88
  mov %rcx,0xe0(%rsp)
  mov %rdx,0xb8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xe0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_88:
  mov %rdi,0x98(%rsp)
  mov %r8,0x90(%rsp)
  mov %rbx,0xb8(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xd0(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2a4
  mov 0x90(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x98(%rsp),%rcx
  nop
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_ef
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_126
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_ef:
  mov %rbx,0xb0(%rsp)
  mov 0xb8(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%r8
  mov %rbx,%r9
  mov 0xb0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_126:
  mov %rcx,0x68(%rsp)
  mov %r9,0x60(%rsp)
  mov %rax,0xa8(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xd0(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x68(%rsp),%rcx
  nop
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_16f
  mov 0xa8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_19a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_16f:
  mov %rsi,0x48(%rsp)
  mov 0xa8(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_19a:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_286
  lea 0x60(%rbx),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_1e8
  mov %rbx,0x40(%rsp)
  mov %r8,0xb8(%rsp)
  mov %r9,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_1e8:
  mov %r9,0x50(%rsp)
  mov %rax,0xa0(%rsp)
  mov %rcx,0x58(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xd0(%rsp),%rsi
  mov 0x58(%rsi),%rsi
  nop
  nop
  nop
  lea 0x70(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x70(%rsp)
  mov 0x58(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_249
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_26d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_249:
  mov 0xa0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x50(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_26d:
  mov 0x70(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_286:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2a4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2c2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_0
