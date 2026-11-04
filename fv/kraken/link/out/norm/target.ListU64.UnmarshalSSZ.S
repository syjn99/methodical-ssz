target.ListU64.UnmarshalSSZ:
L_target.ListU64.UnmarshalSSZ_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target.ListU64.UnmarshalSSZ_290
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  nop
  cmp $0x4,%rcx
  jb L_target.ListU64.UnmarshalSSZ_221
  mov (%rbx),%edx
  nop
  nop
  cmp $0x4,%rdx
  jne L_target.ListU64.UnmarshalSSZ_20c
  lea -0x4(%rdi),%rdx
  mov %rdx,%rsi
  neg %rdx
  sar $0x3f,%rdx
  and $0x4,%edx
  add $-0x4,%rcx
  add %rbx,%rdx
  test $0x7,%rcx
  jne L_target.ListU64.UnmarshalSSZ_16c
  shr $0x3,%rcx
  cmp $0x10,%rcx
  jg L_target.ListU64.UnmarshalSSZ_ce
  mov %rax,0x90(%rsp)
  mov %rsi,0x30(%rsp)
  mov %rdx,0x38(%rsp)
  mov %rcx,0x28(%rsp)
  lea type__+48128(%rip),%rax
  mov %rcx,%rbx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  mov 0x90(%rsp),%rsi
  mov %rdx,0x8(%rsi)
  mov %rdx,0x10(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.ListU64.UnmarshalSSZ_ba
  mov (%rsi),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.ListU64.UnmarshalSSZ_ba:
  mov %rax,(%rsi)
  mov 0x30(%rsp),%rcx
  mov 0x38(%rsp),%rdi
  xor %eax,%eax
  jmpq L_target.ListU64.UnmarshalSSZ_240
L_target.ListU64.UnmarshalSSZ_ce:
  lea 0x40(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  nop
  callq runtime.convT64
  lea type__+48192(%rip),%rcx
  mov %rcx,0x40(%rsp)
  mov %rax,0x48(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  nop
  test %rcx,%rcx
  je L_target.ListU64.UnmarshalSSZ_109
  mov 0x8(%rcx),%rcx
L_target.ListU64.UnmarshalSSZ_109:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0x50(%rsp)
  mov %rdx,0x58(%rsp)
  lea go_string._+40018(%rip),%rax
  mov $0x38,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListU64.UnmarshalSSZ_166
  nop
  lea type__+81728(%rip),%rax
  callq runtime.newobject
  movq $0x38,0x8(%rax)
  lea go_string._+40018(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListU64.UnmarshalSSZ_166:
  sub $-0x80,%rsp
  pop %rbp
  retq
L_target.ListU64.UnmarshalSSZ_16c:
  lea 0x60(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  nop
  callq runtime.convT64
  lea type__+48192(%rip),%rcx
  mov %rcx,0x60(%rsp)
  mov %rax,0x68(%rsp)
  mov ssz.ErrIncorrectListSize(%rip),%rcx
  nop
  test %rcx,%rcx
  je L_target.ListU64.UnmarshalSSZ_1a9
  mov 0x8(%rcx),%rcx
L_target.ListU64.UnmarshalSSZ_1a9:
  mov ssz.ErrIncorrectListSize+8(%rip),%rdx
  mov %rcx,0x70(%rsp)
  mov %rdx,0x78(%rsp)
  lea go_string._+42124(%rip),%rax
  mov $0x44,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListU64.UnmarshalSSZ_206
  nop
  lea type__+81728(%rip),%rax
  callq runtime.newobject
  movq $0x44,0x8(%rax)
  lea go_string._+42124(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListU64.UnmarshalSSZ_206:
  sub $-0x80,%rsp
  pop %rbp
  retq
L_target.ListU64.UnmarshalSSZ_20c:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  sub $-0x80,%rsp
  pop %rbp
  nop
  retq
L_target.ListU64.UnmarshalSSZ_221:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_target.ListU64.UnmarshalSSZ_235:
  mov (%rsi),%r8
  mov %r11,(%r8,%r10,8)
  mov %r9,%rax
  nop
L_target.ListU64.UnmarshalSSZ_240:
  cmp %rdx,%rax
  jge L_target.ListU64.UnmarshalSSZ_275
  lea 0x1(%rax),%r8
  mov %r8,%r9
  shl $0x3,%r8
  cmp %rcx,%r8
  ja L_target.ListU64.UnmarshalSSZ_28a
  mov %rax,%r10
  shl $0x3,%rax
  nop
  cmp %rax,%r8
  jb L_target.ListU64.UnmarshalSSZ_285
  mov 0x8(%rsi),%r8
  nop
  mov (%rdi,%r10,8),%r11
  cmp %r8,%r10
  jb L_target.ListU64.UnmarshalSSZ_235
  jmp L_target.ListU64.UnmarshalSSZ_27f
L_target.ListU64.UnmarshalSSZ_275:
  xor %eax,%eax
  xor %ebx,%ebx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_target.ListU64.UnmarshalSSZ_27f:
  nop
  callq runtime.panicBounds
L_target.ListU64.UnmarshalSSZ_285:
  callq runtime.panicBounds
L_target.ListU64.UnmarshalSSZ_28a:
  callq runtime.panicBounds
  nop
L_target.ListU64.UnmarshalSSZ_290:
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
  jmpq L_target.ListU64.UnmarshalSSZ_0
