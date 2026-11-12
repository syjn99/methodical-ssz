github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2d7
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x4c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2c3
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_7d:
  mov %rax,0x38(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x78(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x20,0x10(%rax)
  movq $0x20,0x18(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_ba
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_ba:
  mov 0x8(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rax)
  mov 0x78(%rsp),%rbx
  add $0x20,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x20,%rdi
  add $0x20,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_167
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_109
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_109:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+37066(%rip),%rax
  mov $0x10,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x10,0x8(%rax)
  lea go_string._+37066(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_161:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_167:
  mov 0x78(%rsp),%rbx
  add $0x28,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x28,%rdi
  mov 0x70(%rsp),%rax
  add $0x28,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1fc
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1a0
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1a0:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1f6
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1f6:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1fc:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x14,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_24c
  mov 0x30(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_24c:
  mov %rax,0x38(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x30,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x14,0x38(%rdx)
  movq $0x14,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_28d
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2a2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_28d:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2a2:
  mov %rsi,0x30(%rdx)
  mov 0x78(%rsp),%rcx
  mov 0x44(%rcx),%rcx
  mov %rcx,0x48(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2c3:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2d7:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_0
