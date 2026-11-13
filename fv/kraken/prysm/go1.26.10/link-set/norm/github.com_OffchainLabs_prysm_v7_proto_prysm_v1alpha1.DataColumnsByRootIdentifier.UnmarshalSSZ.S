github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_372
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  cmp $0x24,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2f9
  mov 0x20(%rbx),%edx
  nop
  nop
  cmp $0x24,%rdx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2e2
  mov %rax,0x98(%rsp)
  mov %rdi,0xb0(%rsp)
  mov %rcx,0xa8(%rsp)
  mov %rbx,0xa0(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x98(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  mov 0xb0(%rsp),%rsi
  add $-0x24,%rsi
  mov %rsi,0x28(%rsp)
  neg %rsi
  sar $0x3f,%rsi
  and $0x24,%esi
  mov 0xa0(%rsp),%rbx
  add %rbx,%rsi
  mov %rsi,0x38(%rsp)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_cc
  mov 0x8(%rdx),%r8
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_cc:
  mov %rax,0x40(%rsp)
  mov %rax,0x8(%rdx)
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x98(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_109
  mov 0x40(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_109:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x40(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_11e:
  mov %rdi,0x8(%rdx)
  mov 0xa8(%rsp),%rcx
  add $-0x24,%rcx
  test $0x7,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_242
  shr $0x3,%rcx
  nop
  cmp $0x80,%rcx
  jg L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1a5
  mov %rcx,0x30(%rsp)
  lea type__+387456(%rip),%rax
  mov %rcx,%rbx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  mov 0x98(%rsp),%rsi
  mov %rdx,0x28(%rsi)
  mov %rdx,0x30(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_18c
  mov 0x20(%rsi),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_18c:
  mov %rax,0x20(%rsi)
  mov 0x28(%rsp),%rcx
  mov 0x38(%rsp),%rdi
  xor %eax,%eax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_320
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1a5:
  lea 0x48(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x48(%rsp)
  mov %rax,0x50(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1dc
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1dc:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0x58(%rsp)
  mov %rdx,0x60(%rsp)
  lea go_string._+151877(%rip),%rax
  mov $0x3f,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_239
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x3f,0x8(%rax)
  lea go_string._+151877(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_239:
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_242:
  lea 0x68(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x68(%rsp)
  mov %rax,0x70(%rsp)
  mov ssz.ErrIncorrectListSize(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_279
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_279:
  mov ssz.ErrIncorrectListSize+8(%rip),%rdx
  mov %rcx,0x78(%rsp)
  mov %rdx,0x80(%rsp)
  lea go_string._+164572(%rip),%rax
  mov $0x4a,%ebx
  lea 0x68(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2d9
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x4a,0x8(%rax)
  lea go_string._+164572(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2d9:
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2e2:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2f9:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_310:
  mov 0x20(%rsi),%r8
  mov %r11,(%r8,%r10,8)
  mov %r9,%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_320:
  cmp %rdx,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_355
  lea 0x1(%rax),%r8
  mov %r8,%r9
  shl $0x3,%r8
  cmp %rcx,%r8
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_36c
  mov %rax,%r10
  shl $0x3,%rax
  nop
  cmp %rax,%r8
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_367
  mov 0x28(%rsi),%r8
  nop
  mov (%rdi,%r10,8),%r11
  cmp %r8,%r10
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_310
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_362
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_355:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_362:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_367:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_36c:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_372:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_0
