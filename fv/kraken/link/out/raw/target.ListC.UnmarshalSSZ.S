target.ListC.UnmarshalSSZ:
L_target.ListC.UnmarshalSSZ_0:
  lea -0x60(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target.ListC.UnmarshalSSZ_6b5
  push %rbp
  mov %rsp,%rbp
  sub $0xd8,%rsp
  mov %rbx,0xf0(%rsp)
  cmp $0x4,%rcx
  jb L_target.ListC.UnmarshalSSZ_385
  mov (%rbx),%edx
  nop
  nop
  cmp $0x4,%rdx
  jne L_target.ListC.UnmarshalSSZ_36e
  lea -0x4(%rdi),%rdx
  mov %rdx,%r8
  neg %rdx
  sar $0x3f,%rdx
  and $0x4,%edx
  lea (%rbx,%rdx,1),%r9
  mov %rcx,%r10
  add $-0x4,%rcx
  nopw (%rax,%rax,1)
  nop
  cmp $0x3,%rcx
  jle L_target.ListC.UnmarshalSSZ_2f0
  mov (%rbx,%rdx,1),%ebx
  nop
  nop
  test %rbx,%rbx
  je L_target.ListC.UnmarshalSSZ_2a1
  nopl (%rax,%rax,1)
  test $0x3,%rbx
  jne L_target.ListC.UnmarshalSSZ_221
  mov %rbx,%rdx
  shr $0x2,%rdx
  cmp $0x4,%rdx
  ja L_target.ListC.UnmarshalSSZ_172
  data16 nop
  cmp %rbx,%rcx
  jae L_target.ListC.UnmarshalSSZ_f7
  lea go_string._+41960(%rip),%rax
  mov $0x3f,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nopl (%rax)
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_ee
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x3f,0x8(%rax)
  lea go_string._+41960(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_ee:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_f7:
  mov %rax,0xe8(%rsp)
  mov %rcx,0x30(%rsp)
  mov %r8,0x50(%rsp)
  mov %r9,0x60(%rsp)
  mov %rdx,0x38(%rsp)
  mov %rbx,0x48(%rsp)
  mov %rdi,0x100(%rsp)
  lea type__+114368(%rip),%rax
  mov %rdx,%rbx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x38(%rsp),%rdx
  mov 0xe8(%rsp),%rsi
  mov %rdx,0x8(%rsi)
  mov %rdx,0x10(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.ListC.UnmarshalSSZ_15f
  mov (%rsi),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.ListC.UnmarshalSSZ_15f:
  mov %rax,(%rsi)
  xor %eax,%eax
  mov 0x48(%rsp),%rcx
  xor %ebx,%ebx
  xor %edi,%edi
  jmpq L_target.ListC.UnmarshalSSZ_3c4
L_target.ListC.UnmarshalSSZ_172:
  lea 0xa8(%rsp),%rcx
  movups %xmm15,(%rcx)
  movups %xmm15,0x10(%rcx)
  mov %rdx,%rax
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0xa8(%rsp)
  mov %rax,0xb0(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  test %rcx,%rcx
  je L_target.ListC.UnmarshalSSZ_1b2
  mov 0x8(%rcx),%rcx
L_target.ListC.UnmarshalSSZ_1b2:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0xb8(%rsp)
  mov %rdx,0xc0(%rsp)
  lea go_string._+40930(%rip),%rax
  mov $0x3b,%ebx
  lea 0xa8(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_218
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x3b,0x8(%rax)
  lea go_string._+40930(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_218:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_221:
  movups %xmm15,0xc8(%rsp)
  mov %rbx,%rax
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0xc8(%rsp)
  mov %rax,0xd0(%rsp)
  lea go_string._+44011(%rip),%rax
  mov $0x72,%ebx
  lea 0xc8(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_298
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x72,0x8(%rax)
  lea go_string._+44011(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_298:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_2a1:
  lea go_string._+39330(%rip),%rax
  mov $0x35,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_2e7
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x35,0x8(%rax)
  lea go_string._+39330(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_2e7:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_2f0:
  add $-0x4,%r10
  jne L_target.ListC.UnmarshalSSZ_31f
  movups %xmm15,0x8(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.ListC.UnmarshalSSZ_30f
  mov (%rax),%rcx
  callq runtime.gcWriteBarrier1
  mov %rcx,(%r11)
L_target.ListC.UnmarshalSSZ_30f:
  lea runtime.noptrbss(%rip),%rcx
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ecx,%ecx
  jmp L_target.ListC.UnmarshalSSZ_39c
L_target.ListC.UnmarshalSSZ_31f:
  lea go_string._+41960(%rip),%rax
  mov $0x3f,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_365
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x3f,0x8(%rax)
  lea go_string._+41960(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_365:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_36e:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_385:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_39c:
  mov %rcx,%rbx
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_3a8:
  mov %r8,(%rdx,%rsi,8)
  mov 0x38(%rsp),%rdx
  mov %rcx,%rsi
  mov 0x28(%rsp),%rcx
  mov %rbx,%rdi
  mov %rax,%rbx
  mov 0x48(%rsp),%rax
L_target.ListC.UnmarshalSSZ_3c4:
  cmp %rdx,%rax
  jae L_target.ListC.UnmarshalSSZ_691
  mov %rax,0x40(%rsp)
  mov %rcx,0x28(%rsp)
  lea type__+83104(%rip),%rax
  data16 nop
  callq runtime.newobject
  mov 0x40(%rsp),%rcx
  lea 0x1(%rcx),%rdx
  mov 0x38(%rsp),%rbx
  cmp %rdx,%rbx
  je L_target.ListC.UnmarshalSSZ_437
  lea 0x2(%rcx),%rsi
  shl $0x2,%rsi
  mov 0x50(%rsp),%r8
  cmp %r8,%rsi
  ja L_target.ListC.UnmarshalSSZ_6af
  mov %rdx,%r9
  shl $0x2,%rdx
  cmp %rdx,%rsi
  jb L_target.ListC.UnmarshalSSZ_6aa
  mov 0x60(%rsp),%rdx
  mov 0x4(%rdx,%rcx,4),%esi
  nop
  mov 0x30(%rsp),%r10
  cmp %rsi,%r10
  jae L_target.ListC.UnmarshalSSZ_44c
  jmpq L_target.ListC.UnmarshalSSZ_4f9
L_target.ListC.UnmarshalSSZ_437:
  mov 0x50(%rsp),%r8
  mov %rdx,%r9
  mov 0x30(%rsp),%r10
  mov %r10,%rsi
  mov 0x60(%rsp),%rdx
L_target.ListC.UnmarshalSSZ_44c:
  mov 0x28(%rsp),%r11
  cmp %r11,%rsi
  jb L_target.ListC.UnmarshalSSZ_5ea
  nopw (%rax,%rax,1)
  cmp %r8,%rsi
  ja L_target.ListC.UnmarshalSSZ_6a5
  mov %rax,0x58(%rsp)
  mov %r9,0x48(%rsp)
  mov %rsi,0x28(%rsp)
  mov 0x100(%rsp),%rdi
  mov %rdi,%r8
  sub %r11,%r8
  mov %rsi,%rcx
  sub %r11,%rcx
  lea -0x4(%r8),%rdi
  mov %rdi,%rsi
  neg %rsi
  sar $0x3f,%rsi
  and %rsi,%r11
  lea (%r11,%rdx,1),%rbx
  callq target.ListU64.UnmarshalSSZ
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_57c
  mov 0xe8(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  mov 0x40(%rsp),%rsi
  cmp %rdx,%rsi
  jae L_target.ListC.UnmarshalSSZ_69c
  mov (%rcx),%rdx
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.ListC.UnmarshalSSZ_4df
  mov 0x58(%rsp),%r8
  jmpq L_target.ListC.UnmarshalSSZ_3a8
L_target.ListC.UnmarshalSSZ_4df:
  mov (%rdx,%rsi,8),%rdi
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%r8
  mov %r8,(%r11)
  mov %rdi,0x8(%r11)
  jmpq L_target.ListC.UnmarshalSSZ_3a8
L_target.ListC.UnmarshalSSZ_4f9:
  movups %xmm15,0x98(%rsp)
  mov %rsi,%rax
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x98(%rsp)
  mov %rax,0xa0(%rsp)
  lea go_string._+41466(%rip),%rax
  mov $0x3d,%ebx
  lea 0x98(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nopl (%rax)
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_573
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x3d,0x8(%rax)
  lea go_string._+41466(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_573:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_57c:
  movups %xmm15,0x68(%rsp)
  je L_target.ListC.UnmarshalSSZ_588
  mov 0x8(%rax),%rax
L_target.ListC.UnmarshalSSZ_588:
  mov %rax,0x68(%rsp)
  mov %rbx,0x70(%rsp)
  lea go_string._+2153(%rip),%rax
  mov $0x9,%ebx
  lea 0x68(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_5e1
  nop
  lea type__+82848(%rip),%rax
  nopl (%rax)
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+2153(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_5e1:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_5ea:
  lea 0x78(%rsp),%rcx
  movups %xmm15,(%rcx)
  movups %xmm15,0x10(%rcx)
  mov %rsi,%rax
  nopl (%rax,%rax,1)
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x78(%rsp)
  mov %rax,0x80(%rsp)
  mov 0x28(%rsp),%rax
  data16 nop
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x88(%rsp)
  mov %rax,0x90(%rsp)
  lea go_string._+42539(%rip),%rax
  mov $0x43,%ebx
  lea 0x78(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.UnmarshalSSZ_688
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x43,0x8(%rax)
  lea go_string._+42539(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.UnmarshalSSZ_688:
  add $0xd8,%rsp
  pop %rbp
  retq
L_target.ListC.UnmarshalSSZ_691:
  mov %rbx,%rax
  mov %rdi,%rcx
  jmpq L_target.ListC.UnmarshalSSZ_39c
L_target.ListC.UnmarshalSSZ_69c:
  nopl (%rax)
  callq runtime.panicBounds
L_target.ListC.UnmarshalSSZ_6a5:
  callq runtime.panicBounds
L_target.ListC.UnmarshalSSZ_6aa:
  callq runtime.panicBounds
L_target.ListC.UnmarshalSSZ_6af:
  callq runtime.panicBounds
  nop
L_target.ListC.UnmarshalSSZ_6b5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.ListC.UnmarshalSSZ_0
