target.Scalars.SizeSSZ:
  mov $0x10,%eax
  retq
target.Scalars.MarshalSSZTo:
L_target.Scalars.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.Scalars.MarshalSSZTo_1ac
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov %rax,0x60(%rsp)
  lea 0x1(%rcx),%rdx
  movzbl (%rax),%r8d
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_5c
  mov %r8b,0x41(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  movzbl 0x41(%rsp),%r8d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0x60(%rsp),%rax
L_target.Scalars.MarshalSSZTo_5c:
  mov %r8b,-0x1(%rdx,%rbx,1)
  add $0x2,%rdx
  movzwl 0x2(%rax),%r8d
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_a3
  mov %r8w,0x42(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x2,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  movzwl 0x42(%rsp),%r8d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0x60(%rsp),%rax
L_target.Scalars.MarshalSSZTo_a3:
  mov %r8w,-0x2(%rdx,%rbx,1)
  add $0x4,%rdx
  mov 0x4(%rax),%r8d
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_e8
  mov %r8d,0x44(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov 0x44(%rsp),%r8d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0x60(%rsp),%rax
L_target.Scalars.MarshalSSZTo_e8:
  mov %r8d,-0x4(%rdx,%rbx,1)
  add $0x8,%rdx
  mov 0x8(%rax),%r8
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_12c
  mov %r8,0x48(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x60(%rsp),%rax
L_target.Scalars.MarshalSSZTo_12c:
  mov %r8,-0x8(%rdx,%rbx,1)
  cmpb $0x0,0x10(%rax)
  je L_target.Scalars.MarshalSSZTo_169
  inc %rdx
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_162
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
L_target.Scalars.MarshalSSZTo_162:
  movb $0x1,-0x1(%rdx,%rbx,1)
  jmp L_target.Scalars.MarshalSSZTo_199
L_target.Scalars.MarshalSSZTo_169:
  inc %rdx
  cmp %rdx,%rdi
  jae L_target.Scalars.MarshalSSZTo_194
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
L_target.Scalars.MarshalSSZTo_194:
  movb $0x0,-0x1(%rdx,%rbx,1)
L_target.Scalars.MarshalSSZTo_199:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_target.Scalars.MarshalSSZTo_1ac:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.Scalars.MarshalSSZTo_0
target.Scalars.UnmarshalSSZ:
  mov %rbx,0x10(%rsp)
  cmp $0x10,%rcx
  jne L_target.Scalars.UnmarshalSSZ_50
  movzbl (%rbx),%ecx
  mov %cl,(%rax)
  movzwl 0x1(%rbx),%ecx
  mov %cx,0x2(%rax)
  mov 0x3(%rbx),%ecx
  mov %ecx,0x4(%rax)
  mov 0x7(%rbx),%rcx
  mov %rcx,0x8(%rax)
  movzbl 0xf(%rbx),%ecx
  cmp $0x1,%cl
  ja L_target.Scalars.UnmarshalSSZ_41
  jne L_target.Scalars.UnmarshalSSZ_37
  movb $0x1,0x10(%rax)
  jmp L_target.Scalars.UnmarshalSSZ_3b
L_target.Scalars.UnmarshalSSZ_37:
  movb $0x0,0x10(%rax)
L_target.Scalars.UnmarshalSSZ_3b:
  xor %eax,%eax
  xor %ebx,%ebx
  nop
  retq
L_target.Scalars.UnmarshalSSZ_41:
  mov ssz.ErrInvalidSerialization(%rip),%rax
  mov ssz.ErrInvalidSerialization+8(%rip),%rbx
  retq
L_target.Scalars.UnmarshalSSZ_50:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  retq
target.FixedVec.SizeSSZ:
  mov $0x40,%eax
  retq
target.FixedVec.MarshalSSZTo:
L_target.FixedVec.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.FixedVec.MarshalSSZTo_136
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  mov %rax,0x78(%rsp)
  test %al,(%rax)
  lea 0x20(%rcx),%rdx
  cmp %rdx,%rdi
  jae L_target.FixedVec.MarshalSSZTo_62
  mov %rcx,0x88(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
  mov 0x78(%rsp),%rax
L_target.FixedVec.MarshalSSZTo_62:
  mov %rbx,0x60(%rsp)
  mov %rdx,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rcx,1),%rdx
  mov %rax,%rbx
  mov $0x20,%ecx
  mov %rdx,%rax
  callq runtime.memmove
  mov 0x78(%rsp),%rdx
  cmpq $0x4,0x28(%rdx)
  jne L_target.FixedVec.MarshalSSZTo_ad
  mov 0x20(%rdx),%r8
  mov %r8,0x58(%rsp)
  mov 0x48(%rsp),%rdi
  mov 0x60(%rsp),%rbx
  mov 0x50(%rsp),%rdx
  xor %eax,%eax
  jmp L_target.FixedVec.MarshalSSZTo_d0
L_target.FixedVec.MarshalSSZTo_ad:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_target.FixedVec.MarshalSSZTo_c8:
  mov %r9,-0x8(%rdx,%rbx,1)
  inc %rax
L_target.FixedVec.MarshalSSZTo_d0:
  cmp $0x4,%rax
  jge L_target.FixedVec.MarshalSSZTo_123
  add $0x8,%rdx
  mov (%r8,%rax,8),%r9
  nop
  cmp %rdx,%rdi
  jae L_target.FixedVec.MarshalSSZTo_c8
  mov %rax,0x50(%rsp)
  mov %r9,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov 0x40(%rsp),%r9
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x50(%rsp),%rax
  jmp L_target.FixedVec.MarshalSSZTo_c8
L_target.FixedVec.MarshalSSZTo_123:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_target.FixedVec.MarshalSSZTo_136:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.FixedVec.MarshalSSZTo_0
target.FixedVec.UnmarshalSSZ:
L_target.FixedVec.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.FixedVec.UnmarshalSSZ_ec
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rbx,0x30(%rsp)
  cmp $0x40,%rcx
  jne L_target.FixedVec.UnmarshalSSZ_87
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  test %al,(%rax)
  cmp %rax,%rbx
  je L_target.FixedVec.UnmarshalSSZ_38
  mov $0x20,%ecx
  callq runtime.memmove
L_target.FixedVec.UnmarshalSSZ_38:
  lea type__+48128(%rip),%rax
  mov $0x4,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  movq $0x4,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.FixedVec.UnmarshalSSZ_7a
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.FixedVec.UnmarshalSSZ_7a:
  mov %rax,0x20(%rdx)
  mov 0x30(%rsp),%rcx
  xor %eax,%eax
  jmp L_target.FixedVec.UnmarshalSSZ_a6
L_target.FixedVec.UnmarshalSSZ_87:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.FixedVec.UnmarshalSSZ_9b:
  mov 0x20(%rdx),%rdi
  mov %r9,(%rdi,%rsi,8)
  mov %r8,%rax
L_target.FixedVec.UnmarshalSSZ_a6:
  cmp $0x4,%rax
  jge L_target.FixedVec.UnmarshalSSZ_d6
  mov %rax,%rsi
  shl $0x3,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x3,%rdi
  nop
  cmp %rax,%rdi
  jb L_target.FixedVec.UnmarshalSSZ_e6
  mov 0x28(%rdx),%rdi
  nop
  mov 0x20(%rcx,%rsi,8),%r9
  cmp %rdi,%rsi
  jb L_target.FixedVec.UnmarshalSSZ_9b
  jmp L_target.FixedVec.UnmarshalSSZ_e1
L_target.FixedVec.UnmarshalSSZ_d6:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x18,%rsp
  pop %rbp
  nop
  retq
L_target.FixedVec.UnmarshalSSZ_e1:
  callq runtime.panicBounds
L_target.FixedVec.UnmarshalSSZ_e6:
  callq runtime.panicBounds
  nop
L_target.FixedVec.UnmarshalSSZ_ec:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.FixedVec.UnmarshalSSZ_0
target.ListU64.SizeSSZ:
  mov 0x8(%rax),%rax
  shl $0x3,%rax
  add $0x4,%rax
  retq
target.ListU64.MarshalSSZTo:
L_target.ListU64.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.ListU64.MarshalSSZTo_102
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  nop
  cmp %rdx,%rdi
  jae L_target.ListU64.MarshalSSZTo_53
  mov %rax,0x70(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+47744(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x70(%rsp),%rax
L_target.ListU64.MarshalSSZTo_53:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%r8
  nop
  cmp $0x10,%r8
  jg L_target.ListU64.MarshalSSZTo_77
  mov %r8,0x50(%rsp)
  mov (%rax),%r9
  mov %r9,0x58(%rsp)
  xor %eax,%eax
  jmp L_target.ListU64.MarshalSSZTo_9a
L_target.ListU64.MarshalSSZTo_77:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_target.ListU64.MarshalSSZTo_92:
  mov %r10,-0x8(%rdx,%rbx,1)
  inc %rax
L_target.ListU64.MarshalSSZTo_9a:
  cmp %r8,%rax
  jge L_target.ListU64.MarshalSSZTo_ef
  add $0x8,%rdx
  mov (%r9,%rax,8),%r10
  cmp %rdx,%rdi
  jae L_target.ListU64.MarshalSSZTo_92
  mov %rax,0x48(%rsp)
  mov %r10,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+47744(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%r8
  mov 0x58(%rsp),%r9
  mov 0x40(%rsp),%r10
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x48(%rsp),%rax
  jmp L_target.ListU64.MarshalSSZTo_92
L_target.ListU64.MarshalSSZTo_ef:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_target.ListU64.MarshalSSZTo_102:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.ListU64.MarshalSSZTo_0
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
