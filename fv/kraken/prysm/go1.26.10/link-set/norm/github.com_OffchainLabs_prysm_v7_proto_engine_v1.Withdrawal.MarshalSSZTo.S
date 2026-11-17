github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_0:
  lea -0x28(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1cb
  push %rbp
  mov %rsp,%rbp
  sub $0xa0,%rsp
  mov %rbx,0xb8(%rsp)
  mov %rax,0xb0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_6c
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
  mov 0xb0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_6c:
  mov %r8,-0x8(%rdx,%rbx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x70(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x70(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_c9
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
  mov 0xb0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_c9:
  mov 0x70(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x14,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1ad
  lea 0x14(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_12c
  mov %r8,0x40(%rsp)
  mov %rdx,0x98(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x40(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_12c:
  mov %rbx,0x90(%rsp)
  mov %r9,0x60(%rsp)
  mov %rdi,0x68(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb0(%rsp),%rdx
  mov 0x30(%rdx),%rdx
  mov 0x68(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_178
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_19b
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_178:
  mov %rdx,0x50(%rsp)
  mov 0x90(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_19b:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xa0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1ad:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1cb:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_0
