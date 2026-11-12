github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2bf
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2a1
  mov %rax,0xb8(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_88
  mov %rdx,0xa0(%rsp)
  mov %rcx,0xc8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xc8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_88:
  mov %rbx,0xa0(%rsp)
  mov %r8,0x80(%rsp)
  mov %rdi,0x78(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xb8(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_282
  mov 0x80(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x78(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_e6
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_11d
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_e6:
  mov %rbx,0x98(%rsp)
  mov 0xa0(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%r9
  mov 0x98(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_11d:
  mov %rax,0x90(%rsp)
  mov %r9,0x60(%rsp)
  mov %rcx,0x70(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb8(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x70(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_165
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_192
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_165:
  mov %rsi,0x50(%rsp)
  mov 0x90(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0xb8(%rsp),%rdx
  mov 0x50(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_192:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_264
  lea 0x60(%rbx),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_1e0
  mov %rbx,0x40(%rsp)
  mov %r8,0xa0(%rsp)
  mov %r9,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_1e0:
  mov %rcx,0x68(%rsp)
  mov %r9,0x58(%rsp)
  mov %rax,0x88(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  nop
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb8(%rsp),%rdx
  mov 0x58(%rdx),%rdx
  mov 0x68(%rsp),%rcx
  nop
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_22f
  mov 0x88(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_252
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_22f:
  mov %rdx,0x48(%rsp)
  mov 0x88(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_252:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_264:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_282:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2a1:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2bf:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_0
