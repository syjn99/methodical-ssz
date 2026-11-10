github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_359
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x70,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_345
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_5d
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_5d:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b3:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9:
  mov 0x78(%rsp),%rbx
  add $0x8,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x70(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_f6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_f6:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+40193(%rip),%rax
  mov $0x11,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_14e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x11,0x8(%rax)
  lea go_string._+40193(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_14e:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_19f
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_19f:
  mov %rax,0x38(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x10,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1e2
  mov 0x38(%rsp),%rdi
  nop
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1f7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1e2:
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1f7:
  mov %rdi,0x18(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_23c
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_23c:
  mov %rax,0x38(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_27d
  mov 0x38(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_292
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_27d:
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_292:
  mov %rdi,0x30(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x50(%rdx)
  movq $0x20,0x58(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_2d7
  mov 0x48(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_2d7:
  mov %rax,0x38(%rsp)
  mov %rax,0x48(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x50,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x50(%rdx)
  movq $0x20,0x58(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_318
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_331
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_318:
  mov 0x48(%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_331:
  mov %rsi,0x48(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_345:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_359:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_0
