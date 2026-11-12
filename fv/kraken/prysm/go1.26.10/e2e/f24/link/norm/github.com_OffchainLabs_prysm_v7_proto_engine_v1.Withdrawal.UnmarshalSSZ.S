github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_19e
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x2c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_18a
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  lea 0x8(%rbx),%rdx
  add $-0x8,%rdi
  lea 0x10(%rax),%rsi
  mov (%rbx),%r8
  mov %r8,0x8(%rax)
  mov %rsi,%rax
  mov %rdx,%rbx
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c7
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_68
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_68:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c1:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c7:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  nop
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x14,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_113
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_113:
  mov %rax,0x38(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x10,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  movq $0x14,0x20(%rdx)
  movq $0x14,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_154
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_154:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_169:
  mov %rsi,0x18(%rdx)
  mov 0x68(%rsp),%rcx
  mov 0x24(%rcx),%rcx
  mov %rcx,0x30(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_18a:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_19e:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_0
