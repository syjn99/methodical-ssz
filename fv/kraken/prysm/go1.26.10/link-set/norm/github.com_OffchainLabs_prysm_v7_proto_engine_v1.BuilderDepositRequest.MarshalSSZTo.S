github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_261
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_243
  mov %rax,0x98(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_88
  mov %rcx,0xa8(%rsp)
  mov %rdx,0x80(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_88:
  mov %rbx,0x80(%rsp)
  mov %r8,0x68(%rsp)
  mov %rdi,0x60(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x98(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_225
  mov 0x68(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x60(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_e3
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_112
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_e3:
  mov %rbx,0x78(%rsp)
  mov 0x80(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x68(%rsp),%r8
  mov %rbx,%r9
  mov 0x78(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_112:
  mov %rax,0x70(%rsp)
  mov %r9,0x50(%rsp)
  mov %rcx,0x58(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x58(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_154
  mov 0x70(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_17c
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_154:
  mov %rsi,0x48(%rsp)
  mov 0x70(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_17c:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_207
  lea 0x60(%rbx),%rdx
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_1c6
  mov %r8,0x80(%rsp)
  mov %rbx,0x40(%rsp)
  mov %rdx,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_1c6:
  mov %rax,0x80(%rsp)
  mov %rdx,0x68(%rsp)
  mov %rcx,0x60(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  mov 0x68(%rsp),%rbx
  mov 0x60(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_207:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_225:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_243:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_261:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_0
