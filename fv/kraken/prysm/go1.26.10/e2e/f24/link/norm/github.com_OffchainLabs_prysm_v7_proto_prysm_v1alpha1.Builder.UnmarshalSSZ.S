github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3c7
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x5d,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3b3
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_7d:
  mov %rax,0x58(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x78(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_ba
  mov 0x58(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_ba:
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_d1:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x1,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x1,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_116
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_116:
  mov %rax,0x20(%rdx)
  mov 0x78(%rsp),%rsi
  movzbl 0x30(%rsi),%edi
  mov %dil,(%rax)
  movq $0x1,0x28(%rdx)
  movq $0x1,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_14f
  mov 0x20(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_14f:
  mov %rax,0x20(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x40(%rdx)
  movq $0x14,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_194
  mov 0x38(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_194:
  mov %rax,0x58(%rsp)
  mov %rax,0x38(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x31,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x14,0x40(%rax)
  movq $0x14,0x48(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1d5
  mov 0x58(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1ea
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1d5:
  mov 0x38(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1ea:
  mov %rsi,0x38(%rax)
  mov 0x78(%rsp),%rbx
  add $0x45,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x45,%rdi
  add $0x50,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Gwei.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_27e
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_222
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_222:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+23990(%rip),%rax
  mov $0xb,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_278
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xb,0x8(%rax)
  lea go_string._+23990(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_278:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_27e:
  mov 0x78(%rsp),%rbx
  add $0x4d,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x4d,%rdi
  mov 0x70(%rsp),%rax
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_314
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_2b7
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_2b7:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+37050(%rip),%rax
  mov $0x10,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_30e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x10,0x8(%rax)
  lea go_string._+37050(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_30e:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_314:
  mov 0x78(%rsp),%rbx
  add $0x55,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x55,%rdi
  mov 0x70(%rsp),%rax
  add $0x60,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  nop
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3ad
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_351
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_351:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+52923(%rip),%rax
  mov $0x15,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3a7
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+52923(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3a7:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3ad:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3b3:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3c7:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_0
