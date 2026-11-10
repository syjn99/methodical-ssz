github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_cc
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x8,%rcx
  je L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb
  lea 0x28(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  lea type__+387520(%rip),%rdx
  mov %rdx,0x28(%rsp)
  lea runtime.gcbits._+1432(%rip),%rdx
  mov %rdx,0x30(%rsp)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x38(%rsp)
  mov %rax,0x40(%rsp)
  lea go_string._+110057(%rip),%rax
  mov $0x28,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_b5
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x28,0x8(%rax)
  lea go_string._+110057(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_b5:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb:
  mov (%rbx),%rcx
  nop
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_cc:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_0
