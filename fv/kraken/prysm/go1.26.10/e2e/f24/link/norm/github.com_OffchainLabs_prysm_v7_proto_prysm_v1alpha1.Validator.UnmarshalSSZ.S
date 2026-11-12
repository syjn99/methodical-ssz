github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_455
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  nop
  cmp $0x79,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_441
  mov %rax,0x80(%rsp)
  mov %rdi,0x98(%rsp)
  mov %rbx,0x88(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_86
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_86:
  mov %rax,0x68(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x88(%rsp),%rbx
  mov $0x30,%ecx
  nop
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_cd
  mov 0x68(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_e2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_cd:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x68(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_e2:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_12c
  mov 0x20(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_12c:
  mov %rax,0x68(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  movq $0x20,0x28(%rax)
  movq $0x20,0x30(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_173
  mov 0x68(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_188
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_173:
  mov 0x20(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x68(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_188:
  mov %rsi,0x20(%rax)
  mov 0x88(%rsp),%rbx
  mov 0x50(%rbx),%rdx
  mov %rdx,0x38(%rax)
  movzbl 0x58(%rbx),%edx
  cmp $0x1,%dl
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_42d
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b1
  movb $0x1,0x40(%rax)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b5
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b1:
  movb $0x0,0x40(%rax)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b5:
  add $0x59,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x59,%rdi
  add $0x48,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_247
  movups %xmm15,0x58(%rsp)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1e6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1e6:
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  lea go_string._+79927(%rip),%rax
  mov $0x1e,%ebx
  lea 0x58(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_241
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x1e,0x8(%rax)
  lea go_string._+79927(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_241:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_247:
  mov 0x88(%rsp),%rbx
  add $0x61,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x61,%rdi
  mov 0x80(%rsp),%rax
  add $0x50,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e7
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_286
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_286:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+46529(%rip),%rax
  mov $0x13,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x13,0x8(%rax)
  lea go_string._+46529(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e1:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e7:
  mov 0x88(%rsp),%rbx
  add $0x69,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x69,%rdi
  mov 0x80(%rsp),%rax
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_387
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_326
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_326:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+29272(%rip),%rax
  mov $0xd,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_381
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29272(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_381:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_387:
  mov 0x88(%rsp),%rbx
  add $0x71,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x71,%rdi
  mov 0x80(%rsp),%rax
  add $0x60,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_427
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_3c6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_3c6:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+52923(%rip),%rax
  mov $0x15,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_421
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+52923(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_421:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_427:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_42d:
  mov ssz.ErrInvalidSerialization(%rip),%rax
  mov ssz.ErrInvalidSerialization+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_441:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_455:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_0
