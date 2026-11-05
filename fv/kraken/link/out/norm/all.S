ssz.ValidateBitlist:
L_ssz.ValidateBitlist_0:
  cmp 0x10(%r14),%rsp
  jbe L_ssz.ValidateBitlist_1f9
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rax,0x60(%rsp)
  nop
  test %rbx,%rbx
  je L_ssz.ValidateBitlist_1a8
  mov %rdi,%rdx
  shr $0x3,%rdi
  lea 0x1(%rdi),%r8
  cmp %r8,%rbx
  jg L_ssz.ValidateBitlist_10a
  movzbl -0x1(%rbx,%rax,1),%r8d
  test %r8b,%r8b
  je L_ssz.ValidateBitlist_be
  lea (%r8,%r8,1),%r8d
  lea 0x1(%r8),%r8d
  bsr %r8d,%r8d
  lea (%r8,%rbx,8),%r8
  lea -0x9(%r8),%r8
  nop
  cmp %r8,%rdx
  jae L_ssz.ValidateBitlist_b4
  lea go_string._+5738(%rip),%rax
  mov $0xd,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_ssz.ValidateBitlist_ae
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+5738(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_ae:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_b4:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_be:
  lea go_string._+13267(%rip),%rax
  mov $0x15,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_104
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+13267(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_104:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_10a:
  mov %r8,0x28(%rsp)
  lea 0x30(%rsp),%rcx
  movups %xmm15,(%rcx)
  movups %xmm15,0x10(%rcx)
  mov %rbx,%rax
  callq runtime.convT64
  lea type__+49184(%rip),%rcx
  mov %rcx,0x30(%rsp)
  mov %rax,0x38(%rsp)
  mov 0x28(%rsp),%rax
  nop
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x40(%rsp)
  mov %rax,0x48(%rsp)
  lea go_string._+37075(%rip),%rax
  mov $0x2f,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_1a2
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x2f,0x8(%rax)
  lea go_string._+37075(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_1a2:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_1a8:
  lea go_string._+33565(%rip),%rax
  mov $0x2a,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_ssz.ValidateBitlist_1f3
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x2a,0x8(%rax)
  lea go_string._+33565(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_ssz.ValidateBitlist_1f3:
  add $0x50,%rsp
  pop %rbp
  retq
L_ssz.ValidateBitlist_1f9:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_ssz.ValidateBitlist_0
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+49120(%rip),%rax
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
  lea type__+48736(%rip),%rsi
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
  lea type__+48736(%rip),%rsi
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
  lea type__+49120(%rip),%rax
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
  lea type__+49184(%rip),%rcx
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
  lea go_string._+40250(%rip),%rax
  mov $0x38,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListU64.UnmarshalSSZ_166
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x38,0x8(%rax)
  lea go_string._+40250(%rip),%rcx
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
  lea type__+49184(%rip),%rcx
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
  lea go_string._+42606(%rip),%rax
  mov $0x44,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListU64.UnmarshalSSZ_206
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x44,0x8(%rax)
  lea go_string._+42606(%rip),%rcx
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
target.BitVec.SizeSSZ:
  mov $0x1,%eax
  retq
target.BitVec.MarshalSSZTo:
L_target.BitVec.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.MarshalSSZTo_96
  push %rbp
  mov %rsp,%rbp
  sub $0x30,%rsp
  mov %rbx,0x48(%rsp)
  mov (%rax),%rdx
  cmpq $0x1,0x8(%rax)
  nop
  jne L_target.BitVec.MarshalSSZTo_7b
  lea 0x1(%rcx),%r8
  cmp %r8,%rdi
  jae L_target.BitVec.MarshalSSZTo_62
  mov %rdx,0x28(%rsp)
  mov %rcx,0x50(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x50(%rsp),%rcx
  mov %rax,%rbx
L_target.BitVec.MarshalSSZTo_62:
  movzbl (%rdx),%edx
  mov %dl,(%rbx,%rcx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x30,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_7b:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x30,%rsp
  pop %rbp
  retq
L_target.BitVec.MarshalSSZTo_96:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitVec.MarshalSSZTo_0
target.BitVec.UnmarshalSSZ:
L_target.BitVec.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.UnmarshalSSZ_cd
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rbx,0x30(%rsp)
  nop
  cmp $0x1,%rcx
  jne L_target.BitVec.UnmarshalSSZ_b9
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x1,%ecx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_74
  mov (%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_74:
  mov %rax,(%rdx)
  mov 0x30(%rsp),%rcx
  movzbl (%rcx),%ecx
  mov %cl,(%rax)
  movq $0x1,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_ac
  mov (%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_ac:
  mov %rax,(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_b9:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x18,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_cd:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitVec.UnmarshalSSZ_0
target.Nested.SizeSSZ:
L_target.Nested.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.Nested.SizeSSZ_69
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x10(%rax)
  jne L_target.Nested.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+83104(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_target.Nested.SizeSSZ_4c
L_target.Nested.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_target.Nested.SizeSSZ_4c:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
L_target.Nested.SizeSSZ_53:
  mov 0x10(%rax),%rcx
  mov 0x8(%rcx),%rax
  shl $0x3,%rax
  add $0x20,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_target.Nested.SizeSSZ_69:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_target.Nested.SizeSSZ_0
target.Nested.MarshalSSZTo:
L_target.Nested.MarshalSSZTo_0:
  lea -0x50(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target.Nested.MarshalSSZTo_4e9
  push %rbp
  mov %rsp,%rbp
  sub $0xc8,%rsp
  mov %rbx,0xe0(%rsp)
  mov %rax,0xd8(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_6b
  mov %r8,0x60(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_6b:
  mov %r8,-0x8(%rdx,%rbx,1)
  cmpq $0x0,0x8(%rax)
  jne L_target.Nested.MarshalSSZTo_d9
  mov %rbx,0x90(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rdi,0x50(%rsp)
  lea type__+135104(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.MarshalSSZTo_a8
  mov 0xd8(%rsp),%rdx
  jmp L_target.Nested.MarshalSSZTo_c0
L_target.Nested.MarshalSSZTo_a8:
  mov 0xd8(%rsp),%rdx
  mov 0x8(%rdx),%r8
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_target.Nested.MarshalSSZTo_c0:
  mov %rax,0x8(%rdx)
  mov %rdx,%rax
  mov 0x48(%rsp),%rdx
  mov 0x90(%rsp),%rbx
  mov 0x50(%rsp),%rdi
L_target.Nested.MarshalSSZTo_d9:
  mov 0x8(%rax),%r8
  mov %r8,0xa8(%rsp)
  inc %rdx
  movzbl (%r8),%r9d
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_12f
  mov %r9b,0x41(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%r8
  movzbl 0x41(%rsp),%r9d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_12f:
  mov %r9b,-0x1(%rdx,%rbx,1)
  add $0x2,%rdx
  movzwl 0x2(%r8),%r9d
  nop
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_184
  mov %r9w,0x42(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x2,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%r8
  movzwl 0x42(%rsp),%r9d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_184:
  mov %r9w,-0x2(%rdx,%rbx,1)
  add $0x4,%rdx
  mov 0x4(%r8),%r9d
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_1d4
  mov %r9d,0x44(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%r8
  mov 0x44(%rsp),%r9d
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_1d4:
  mov %r9d,-0x4(%rdx,%rbx,1)
  add $0x8,%rdx
  mov 0x8(%r8),%r9
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_223
  mov %r9,0x58(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%r8
  mov 0x58(%rsp),%r9
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_223:
  mov %r9,-0x8(%rdx,%rbx,1)
  cmpb $0x0,0x10(%r8)
  je L_target.Nested.MarshalSSZTo_269
  inc %rdx
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_262
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_262:
  movb $0x1,-0x1(%rdx,%rbx,1)
  jmp L_target.Nested.MarshalSSZTo_2a1
L_target.Nested.MarshalSSZTo_269:
  inc %rdx
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_29c
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x1,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_29c:
  movb $0x0,-0x1(%rdx,%rbx,1)
L_target.Nested.MarshalSSZTo_2a1:
  cmpq $0x0,0x10(%rax)
  jne L_target.Nested.MarshalSSZTo_30a
  mov %rbx,0x98(%rsp)
  mov %rdx,0x70(%rsp)
  mov %rdi,0x78(%rsp)
  lea type__+83104(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.MarshalSSZTo_2d9
  mov 0xd8(%rsp),%rdx
  jmp L_target.Nested.MarshalSSZTo_2f1
L_target.Nested.MarshalSSZTo_2d9:
  mov 0xd8(%rsp),%rdx
  mov 0x10(%rdx),%r8
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_target.Nested.MarshalSSZTo_2f1:
  mov %rax,0x10(%rdx)
  mov %rdx,%rax
  mov 0x70(%rsp),%rdx
  mov 0x98(%rsp),%rbx
  mov 0x78(%rsp),%rdi
L_target.Nested.MarshalSSZTo_30a:
  add $0x4,%rdx
  nop
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_33f
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0xd8(%rsp),%rax
L_target.Nested.MarshalSSZTo_33f:
  movl $0x1c,-0x4(%rdx,%rbx,1)
  mov 0x10(%rax),%r8
  test %al,(%r8)
  add $0x4,%rdx
  nop
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_38b
  mov %r8,0xa0(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
L_target.Nested.MarshalSSZTo_38b:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%r8),%r9
  cmp $0x10,%r9
  jg L_target.Nested.MarshalSSZTo_3b7
  mov %r9,0x88(%rsp)
  mov (%r8),%r8
  mov %r8,0xb0(%rsp)
  xor %eax,%eax
  jmpq L_target.Nested.MarshalSSZTo_478
L_target.Nested.MarshalSSZTo_3b7:
  mov ssz.ErrListTooBig(%rip),%rdx
  mov ssz.ErrListTooBig+8(%rip),%r8
  xor %eax,%eax
  xor %ecx,%ecx
  xor %ebx,%ebx
L_target.Nested.MarshalSSZTo_3cb:
  test %rdx,%rdx
  je L_target.Nested.MarshalSSZTo_458
  movups %xmm15,0xb8(%rsp)
  je L_target.Nested.MarshalSSZTo_3e3
  mov 0x8(%rdx),%rdx
L_target.Nested.MarshalSSZTo_3e3:
  mov %rdx,0xb8(%rsp)
  mov %r8,0xc0(%rsp)
  lea go_string._+516(%rip),%rax
  mov $0x5,%ebx
  lea 0xb8(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.Nested.MarshalSSZTo_442
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+516(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.Nested.MarshalSSZTo_442:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xc8,%rsp
  pop %rbp
  retq
L_target.Nested.MarshalSSZTo_458:
  mov %rdx,%rdi
  mov %r8,%rsi
  mov %rax,%rdx
  mov %rbx,%rax
  mov %rdx,%rbx
  add $0xc8,%rsp
  pop %rbp
  retq
L_target.Nested.MarshalSSZTo_470:
  mov %r10,-0x8(%rdx,%rbx,1)
  inc %rax
L_target.Nested.MarshalSSZTo_478:
  cmp %r9,%rax
  jge L_target.Nested.MarshalSSZTo_4d9
  add $0x8,%rdx
  mov (%r8,%rax,8),%r10
  cmp %rdx,%rdi
  jae L_target.Nested.MarshalSSZTo_470
  mov %rax,0x80(%rsp)
  mov %r10,0x68(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xb0(%rsp),%r8
  mov 0x88(%rsp),%r9
  mov 0x68(%rsp),%r10
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x80(%rsp),%rax
  jmp L_target.Nested.MarshalSSZTo_470
L_target.Nested.MarshalSSZTo_4d9:
  xor %r8d,%r8d
  mov %rdx,%rax
  mov %rdi,%rcx
  xor %edx,%edx
  jmpq L_target.Nested.MarshalSSZTo_3cb
L_target.Nested.MarshalSSZTo_4e9:
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
  jmpq L_target.Nested.MarshalSSZTo_0
target.Nested.UnmarshalSSZ:
L_target.Nested.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.Nested.UnmarshalSSZ_227
  push %rbp
  mov %rsp,%rbp
  sub $0x58,%rsp
  mov %rbx,0x70(%rsp)
  nop
  cmp $0x1c,%rcx
  jb L_target.Nested.UnmarshalSSZ_213
  mov 0x18(%rbx),%edx
  nop
  nop
  cmp $0x1c,%rdx
  jne L_target.Nested.UnmarshalSSZ_1ff
  mov %rax,0x68(%rsp)
  mov %rdi,0x80(%rsp)
  mov %rcx,0x78(%rsp)
  mov %rbx,0x70(%rsp)
  lea -0x1c(%rdi),%rcx
  mov %rcx,0x28(%rsp)
  neg %rcx
  sar $0x3f,%rcx
  and $0x1c,%ecx
  mov (%rbx),%rdx
  add %rbx,%rcx
  mov %rcx,0x30(%rsp)
  mov %rdx,(%rax)
  lea type__+135104(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.UnmarshalSSZ_8d
  mov 0x68(%rsp),%rdx
  jmp L_target.Nested.UnmarshalSSZ_a2
L_target.Nested.UnmarshalSSZ_8d:
  mov 0x68(%rsp),%rdx
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target.Nested.UnmarshalSSZ_a2:
  mov %rax,0x8(%rdx)
  mov 0x70(%rsp),%rbx
  add $0x8,%rbx
  mov 0x80(%rsp),%rdi
  add $-0x8,%rdi
  mov $0x10,%ecx
  callq target.Scalars.UnmarshalSSZ
  test %rax,%rax
  je L_target.Nested.UnmarshalSSZ_134
  movups %xmm15,0x48(%rsp)
  je L_target.Nested.UnmarshalSSZ_d6
  mov 0x8(%rax),%rax
L_target.Nested.UnmarshalSSZ_d6:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+511(%rip),%rax
  mov $0x5,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_target.Nested.UnmarshalSSZ_12e
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+511(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.Nested.UnmarshalSSZ_12e:
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_134:
  lea type__+83104(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.UnmarshalSSZ_155
  mov 0x68(%rsp),%rdx
  jmp L_target.Nested.UnmarshalSSZ_16c
L_target.Nested.UnmarshalSSZ_155:
  mov 0x68(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target.Nested.UnmarshalSSZ_16c:
  mov %rax,0x10(%rdx)
  mov 0x78(%rsp),%rcx
  add $-0x1c,%rcx
  mov 0x30(%rsp),%rbx
  mov 0x28(%rsp),%rdi
  callq target.ListU64.UnmarshalSSZ
  test %rax,%rax
  je L_target.Nested.UnmarshalSSZ_1f9
  movups %xmm15,0x38(%rsp)
  je L_target.Nested.UnmarshalSSZ_199
  mov 0x8(%rax),%rax
L_target.Nested.UnmarshalSSZ_199:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+516(%rip),%rax
  mov $0x5,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_target.Nested.UnmarshalSSZ_1f3
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+516(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.Nested.UnmarshalSSZ_1f3:
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_1f9:
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_1ff:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_213:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_227:
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
  jmpq L_target.Nested.UnmarshalSSZ_0
target.ListC.SizeSSZ:
  mov (%rax),%rcx
  mov 0x8(%rax),%rdx
  xor %eax,%eax
  mov $0x4,%ebx
  jmp L_target.ListC.SizeSSZ_23
L_target.ListC.SizeSSZ_10:
  mov (%rcx,%rax,8),%rsi
  mov 0x8(%rsi),%rsi
  lea (%rbx,%rsi,8),%rbx
  lea 0x8(%rbx),%rbx
  inc %rax
L_target.ListC.SizeSSZ_23:
  cmp %rdx,%rax
  jl L_target.ListC.SizeSSZ_10
  mov %rbx,%rax
  retq
target.ListC.MarshalSSZTo:
L_target.ListC.MarshalSSZTo_0:
  lea -0x28(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target.ListC.MarshalSSZTo_32c
  push %rbp
  mov %rsp,%rbp
  sub $0xa0,%rsp
  mov %rbx,0xb8(%rsp)
  mov %rax,0xb0(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  cmp %rdx,%rdi
  jae L_target.ListC.MarshalSSZTo_5f
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xb0(%rsp),%rax
L_target.ListC.MarshalSSZTo_5f:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%r8
  mov (%rax),%r9
  xor %ecx,%ecx
  jmp L_target.ListC.MarshalSSZTo_80
L_target.ListC.MarshalSSZTo_72:
  mov (%r9,%rcx,8),%r10
  test %al,(%r10)
  nop
  inc %rcx
  nop
L_target.ListC.MarshalSSZTo_80:
  cmp %r8,%rcx
  jl L_target.ListC.MarshalSSZTo_72
  cmp $0x4,%r8
  jg L_target.ListC.MarshalSSZTo_a3
  mov %r9,0x98(%rsp)
  mov %r8,0x68(%rsp)
  mov %r8,%r10
  shl $0x2,%r8
  xor %ecx,%ecx
  jmp L_target.ListC.MarshalSSZTo_d5
L_target.ListC.MarshalSSZTo_a3:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa0,%rsp
  pop %rbp
  retq
L_target.ListC.MarshalSSZTo_c1:
  mov %r8d,-0x4(%rdx,%rbx,1)
  mov 0x8(%r11),%r11
  lea (%r8,%r11,8),%r8
  lea 0x4(%r8),%r8
  inc %rcx
L_target.ListC.MarshalSSZTo_d5:
  cmp %r10,%rcx
  jge L_target.ListC.MarshalSSZTo_145
  add $0x4,%rdx
  mov (%r9,%rcx,8),%r11
  nop
  cmp %rdx,%rdi
  jae L_target.ListC.MarshalSSZTo_c1
  mov %rcx,0x60(%rsp)
  mov %r11,0x78(%rsp)
  mov %r8,0x48(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%r8
  mov 0x98(%rsp),%r9
  mov 0x68(%rsp),%r10
  mov 0x78(%rsp),%r11
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xb0(%rsp),%rax
  mov 0x60(%rsp),%rcx
  nop
  jmpq L_target.ListC.MarshalSSZTo_c1
L_target.ListC.MarshalSSZTo_145:
  mov (%rax),%r8
  mov %r8,0x98(%rsp)
  mov 0x8(%rax),%r9
  mov %r9,0x68(%rsp)
  xor %eax,%eax
  xor %ecx,%ecx
  xor %esi,%esi
  nop
  jmp L_target.ListC.MarshalSSZTo_171
L_target.ListC.MarshalSSZTo_162:
  inc %rax
  mov %r10,%rsi
  mov %rdx,%r11
  mov %rcx,%rdx
  mov %r11,%rcx
L_target.ListC.MarshalSSZTo_171:
  cmp %r9,%rax
  jge L_target.ListC.MarshalSSZTo_290
  mov %rax,0x60(%rsp)
  add $0x4,%rdx
  mov (%r8,%rax,8),%r10
  nop
  cmp %rdx,%rdi
  jae L_target.ListC.MarshalSSZTo_1cc
  mov %r10,0x70(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%r8
  mov 0x68(%rsp),%r9
  mov 0x70(%rsp),%r10
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x60(%rsp),%rax
L_target.ListC.MarshalSSZTo_1cc:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%r10),%r11
  cmp $0x10,%r11
  jle L_target.ListC.MarshalSSZTo_1f7
  mov ssz.ErrListTooBig(%rip),%rdx
  mov ssz.ErrListTooBig+8(%rip),%r10
  xor %edi,%edi
  xor %ecx,%ecx
  xor %ebx,%ebx
  jmpq L_target.ListC.MarshalSSZTo_285
L_target.ListC.MarshalSSZTo_1f7:
  mov %r11,0x58(%rsp)
  mov (%r10),%r10
  mov %r10,0x90(%rsp)
  xor %ecx,%ecx
  jmp L_target.ListC.MarshalSSZTo_213
L_target.ListC.MarshalSSZTo_20b:
  mov %r12,-0x8(%rdx,%rbx,1)
  inc %rcx
L_target.ListC.MarshalSSZTo_213:
  cmp %r11,%rcx
  jge L_target.ListC.MarshalSSZTo_27d
  add $0x8,%rdx
  mov (%r10,%rcx,8),%r12
  cmp %rdx,%rdi
  jae L_target.ListC.MarshalSSZTo_20b
  mov %rcx,0x50(%rsp)
  mov %r12,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%r8
  mov 0x68(%rsp),%r9
  mov 0x90(%rsp),%r10
  mov 0x58(%rsp),%r11
  mov 0x40(%rsp),%r12
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x60(%rsp),%rax
  mov 0x50(%rsp),%rcx
  jmp L_target.ListC.MarshalSSZTo_20b
L_target.ListC.MarshalSSZTo_27d:
  xor %r10d,%r10d
  mov %rdx,%rcx
  xor %edx,%edx
L_target.ListC.MarshalSSZTo_285:
  test %rdx,%rdx
  je L_target.ListC.MarshalSSZTo_162
  jmp L_target.ListC.MarshalSSZTo_2a8
L_target.ListC.MarshalSSZTo_290:
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rcx,%rdx
  mov %rdi,%rcx
  mov %rdx,%rdi
  add $0xa0,%rsp
  pop %rbp
  retq
L_target.ListC.MarshalSSZTo_2a8:
  movups %xmm15,0x80(%rsp)
  je L_target.ListC.MarshalSSZTo_2b7
  mov 0x8(%rdx),%rdx
L_target.ListC.MarshalSSZTo_2b7:
  mov %rdx,0x80(%rsp)
  mov %r10,0x88(%rsp)
  lea go_string._+2153(%rip),%rax
  mov $0x9,%ebx
  lea 0x80(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.ListC.MarshalSSZTo_316
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+2153(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.ListC.MarshalSSZTo_316:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xa0,%rsp
  pop %rbp
  retq
L_target.ListC.MarshalSSZTo_32c:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.ListC.MarshalSSZTo_0
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
  nop
  nop
  cmp $0x3,%rcx
  jle L_target.ListC.UnmarshalSSZ_2f0
  mov (%rbx,%rdx,1),%ebx
  nop
  nop
  test %rbx,%rbx
  je L_target.ListC.UnmarshalSSZ_2a1
  nop
  test $0x3,%rbx
  jne L_target.ListC.UnmarshalSSZ_221
  mov %rbx,%rdx
  shr $0x2,%rdx
  cmp $0x4,%rdx
  ja L_target.ListC.UnmarshalSSZ_172
  nop
  cmp %rbx,%rcx
  jae L_target.ListC.UnmarshalSSZ_f7
  lea go_string._+41960(%rip),%rax
  mov $0x3f,%ebx
  xor %ecx,%ecx
  xor %edi,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
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
  nop
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
  nop
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
  nop
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
  nop
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
  nop
  callq runtime.convT64
  lea type__+49120(%rip),%rcx
  mov %rcx,0x78(%rsp)
  mov %rax,0x80(%rsp)
  mov 0x28(%rsp),%rax
  nop
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
  nop
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
target.BitL.SizeSSZ:
  mov 0x8(%rax),%rax
  add $0x4,%rax
  retq
target.BitL.MarshalSSZTo:
L_target.BitL.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitL.MarshalSSZTo_105
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  nop
  cmp %rdx,%rdi
  jae L_target.BitL.MarshalSSZTo_53
  mov %rax,0x70(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x70(%rsp),%rax
L_target.BitL.MarshalSSZTo_53:
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%rcx
  mov (%rax),%r8
  cmp $0x800,%rcx
  jg L_target.BitL.MarshalSSZTo_ea
  lea (%rdx,%rcx,1),%r9
  cmp %r9,%rdi
  jae L_target.BitL.MarshalSSZTo_b6
  mov %rdx,0x40(%rsp)
  mov %rcx,0x50(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  lea type__+48736(%rip),%rsi
  mov %rcx,%rdx
  mov %rdi,%rcx
  mov %rdx,%rdi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov 0x58(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov 0x50(%rsp),%rcx
  mov %rax,%rbx
L_target.BitL.MarshalSSZTo_b6:
  mov %rbx,0x58(%rsp)
  mov %r9,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  callq runtime.memmove
  mov 0x58(%rsp),%rax
  mov 0x50(%rsp),%rbx
  mov 0x48(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_ea:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_105:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitL.MarshalSSZTo_0
target.BitL.UnmarshalSSZ:
L_target.BitL.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitL.UnmarshalSSZ_1de
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  nop
  cmp $0x4,%rcx
  jb L_target.BitL.UnmarshalSSZ_1ca
  mov (%rbx),%edx
  nop
  nop
  cmp $0x4,%rdx
  jne L_target.BitL.UnmarshalSSZ_1b6
  mov %rax,0x80(%rsp)
  mov %rcx,0x90(%rsp)
  lea -0x4(%rdi),%rdx
  mov %rdx,%rsi
  neg %rdx
  sar $0x3f,%rdx
  and $0x4,%edx
  lea (%rbx,%rdx,1),%rax
  mov %rax,0x48(%rsp)
  add $-0x4,%rcx
  mov %rcx,0x28(%rsp)
  mov %rcx,%rbx
  mov %rsi,%rcx
  mov $0x800,%edi
  callq ssz.ValidateBitlist
  nop
  test %rax,%rax
  je L_target.BitL.UnmarshalSSZ_f4
  movups %xmm15,0x60(%rsp)
  test %rax,%rax
  je L_target.BitL.UnmarshalSSZ_94
  mov 0x8(%rax),%rax
L_target.BitL.UnmarshalSSZ_94:
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  lea go_string._+521(%rip),%rax
  mov $0x5,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_target.BitL.UnmarshalSSZ_ee
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+521(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.BitL.UnmarshalSSZ_ee:
  add $0x70,%rsp
  pop %rbp
  retq
L_target.BitL.UnmarshalSSZ_f4:
  mov %rbx,0x50(%rsp)
  mov %rax,0x30(%rsp)
  mov 0x90(%rsp),%rdx
  add $-0x4,%rdx
  jne L_target.BitL.UnmarshalSSZ_119
  lea runtime.noptrbss(%rip),%rcx
  xor %edx,%edx
  xor %esi,%esi
  jmp L_target.BitL.UnmarshalSSZ_13f
L_target.BitL.UnmarshalSSZ_119:
  lea runtime.noptrbss(%rip),%rax
  mov 0x28(%rsp),%rbx
  xor %ecx,%ecx
  mov %rbx,%rdi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rcx,%rsi
  mov %rax,%rcx
L_target.BitL.UnmarshalSSZ_13f:
  mov %rcx,0x58(%rsp)
  mov %rdx,0x40(%rsp)
  mov %rsi,0x38(%rsp)
  mov %rcx,%rax
  mov 0x48(%rsp),%rbx
  mov 0x28(%rsp),%rcx
  nop
  callq runtime.memmove
  mov 0x40(%rsp),%rdx
  mov 0x80(%rsp),%rsi
  mov %rdx,0x8(%rsi)
  mov 0x38(%rsp),%rdx
  mov %rdx,0x10(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.BitL.UnmarshalSSZ_18f
  mov 0x58(%rsp),%rdx
  jmp L_target.BitL.UnmarshalSSZ_1a3
L_target.BitL.UnmarshalSSZ_18f:
  mov (%rsi),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rdx
  mov %rdx,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitL.UnmarshalSSZ_1a3:
  mov %rdx,(%rsi)
  mov 0x30(%rsp),%rax
  mov 0x50(%rsp),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_target.BitL.UnmarshalSSZ_1b6:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_target.BitL.UnmarshalSSZ_1ca:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_target.BitL.UnmarshalSSZ_1de:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.BitL.UnmarshalSSZ_0
target_prysm.Checkpoint.SizeSSZ:
  mov $0x28,%eax
  retq
target_prysm.Checkpoint.MarshalSSZTo:
L_target_prysm.Checkpoint.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.Checkpoint.MarshalSSZTo_101
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  cmp %rdx,%rdi
  jae L_target_prysm.Checkpoint.MarshalSSZTo_5d
  mov %rax,0x78(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0x78(%rsp),%rax
L_target_prysm.Checkpoint.MarshalSSZTo_5d:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov 0x8(%rax),%r8
  cmpq $0x20,0x10(%rax)
  jne L_target_prysm.Checkpoint.MarshalSSZTo_e6
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_target_prysm.Checkpoint.MarshalSSZTo_ad
  mov %rdx,0x40(%rsp)
  mov %r8,0x60(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov 0x60(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov %rax,%rbx
L_target_prysm.Checkpoint.MarshalSSZTo_ad:
  mov %rbx,0x60(%rsp)
  mov %r9,0x50(%rsp)
  mov %rdi,0x48(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  mov 0x50(%rsp),%rbx
  mov 0x48(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.MarshalSSZTo_e6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.MarshalSSZTo_101:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.Checkpoint.MarshalSSZTo_0
target_prysm.Checkpoint.UnmarshalSSZ:
L_target_prysm.Checkpoint.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.Checkpoint.UnmarshalSSZ_f3
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x28,%rcx
  jne L_target_prysm.Checkpoint.UnmarshalSSZ_df
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  mov (%rbx),%rdx
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.Checkpoint.UnmarshalSSZ_7b
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.Checkpoint.UnmarshalSSZ_7b:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.Checkpoint.UnmarshalSSZ_bc
  mov 0x18(%rsp),%rsi
  jmp L_target_prysm.Checkpoint.UnmarshalSSZ_d1
L_target_prysm.Checkpoint.UnmarshalSSZ_bc:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.Checkpoint.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.UnmarshalSSZ_df:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_target_prysm.Checkpoint.UnmarshalSSZ_f3:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.Checkpoint.UnmarshalSSZ_0
target_prysm.AttestationData.SizeSSZ:
  mov $0x80,%eax
  retq
target_prysm.AttestationData.MarshalSSZTo:
L_target_prysm.AttestationData.MarshalSSZTo_0:
  lea -0x68(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target_prysm.AttestationData.MarshalSSZTo_545
  push %rbp
  mov %rsp,%rbp
  sub $0xe0,%rsp
  mov %rbx,0xf8(%rsp)
  mov %rax,0xf0(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  cmp %rdx,%rdi
  jae L_target_prysm.AttestationData.MarshalSSZTo_71
  mov %r8,0x88(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x88(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0xf0(%rsp),%rax
L_target_prysm.AttestationData.MarshalSSZTo_71:
  mov %r8,-0x8(%rdx,%rbx,1)
  add $0x8,%rdx
  mov 0x8(%rax),%r8
  nop
  cmp %rdx,%rdi
  jae L_target_prysm.AttestationData.MarshalSSZTo_c0
  mov %r8,0x80(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xf0(%rsp),%rax
L_target_prysm.AttestationData.MarshalSSZTo_c0:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov 0x10(%rax),%r8
  cmpq $0x20,0x18(%rax)
  jne L_target_prysm.AttestationData.MarshalSSZTo_527
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_target_prysm.AttestationData.MarshalSSZTo_11b
  mov %rdx,0x48(%rsp)
  mov %r8,0xc8(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov 0xc8(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_target_prysm.AttestationData.MarshalSSZTo_11b:
  mov %rbx,0xa0(%rsp)
  mov %r9,0x60(%rsp)
  mov %rdi,0x70(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xf0(%rsp),%rdx
  cmpq $0x0,0x28(%rdx)
  jne L_target_prysm.AttestationData.MarshalSSZTo_188
  lea type__+100288(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.MarshalSSZTo_16c
  mov 0xf0(%rsp),%rdx
  jmp L_target_prysm.AttestationData.MarshalSSZTo_184
L_target_prysm.AttestationData.MarshalSSZTo_16c:
  mov 0xf0(%rsp),%rdx
  mov 0x28(%rdx),%r8
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_target_prysm.AttestationData.MarshalSSZTo_184:
  mov %rax,0x28(%rdx)
L_target_prysm.AttestationData.MarshalSSZTo_188:
  mov 0x28(%rdx),%r8
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov (%r8),%r9
  mov 0x70(%rsp),%rcx
  nop
  cmp %rbx,%rcx
  jb L_target_prysm.AttestationData.MarshalSSZTo_1af
  mov 0xa0(%rsp),%rax
  jmp L_target_prysm.AttestationData.MarshalSSZTo_1ea
L_target_prysm.AttestationData.MarshalSSZTo_1af:
  mov %r8,0xb0(%rsp)
  mov %r9,0x78(%rsp)
  mov 0xa0(%rsp),%rax
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xf0(%rsp),%rdx
  mov 0xb0(%rsp),%r8
  mov 0x78(%rsp),%r9
L_target_prysm.AttestationData.MarshalSSZTo_1ea:
  mov %r9,-0x8(%rbx,%rax,1)
  mov 0x8(%r8),%r9
  cmpq $0x20,0x10(%r8)
  je L_target_prysm.AttestationData.MarshalSSZTo_210
  mov ssz.ErrBytesLength(%rip),%r8
  mov ssz.ErrBytesLength+8(%rip),%r9
  xor %eax,%eax
  xor %ecx,%ecx
  xor %ebx,%ebx
  jmp L_target_prysm.AttestationData.MarshalSSZTo_28c
L_target_prysm.AttestationData.MarshalSSZTo_210:
  lea 0x20(%rbx),%r8
  cmp %r8,%rcx
  jae L_target_prysm.AttestationData.MarshalSSZTo_24a
  mov %rbx,0x60(%rsp)
  mov %r9,0xc8(%rsp)
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%r9
  mov %rbx,%r8
  mov 0x60(%rsp),%rbx
L_target_prysm.AttestationData.MarshalSSZTo_24a:
  mov %r8,0x60(%rsp)
  mov %rcx,0x70(%rsp)
  mov %rax,0xa0(%rsp)
  add %rbx,%rax
  mov %r9,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xf0(%rsp),%rdx
  xor %r8d,%r8d
  mov 0x70(%rsp),%rax
  mov 0xa0(%rsp),%rcx
  mov 0x60(%rsp),%rbx
  xor %r9d,%r9d
L_target_prysm.AttestationData.MarshalSSZTo_28c:
  test %r8,%r8
  je L_target_prysm.AttestationData.MarshalSSZTo_31b
  movups %xmm15,0xb8(%rsp)
  nop
  je L_target_prysm.AttestationData.MarshalSSZTo_2a6
  mov 0x8(%r8),%r8
L_target_prysm.AttestationData.MarshalSSZTo_2a6:
  mov %r8,0xb8(%rsp)
  mov %r9,0xc0(%rsp)
  lea go_string._+3146(%rip),%rax
  mov $0xa,%ebx
  lea 0xb8(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target_prysm.AttestationData.MarshalSSZTo_305
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+3146(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target_prysm.AttestationData.MarshalSSZTo_305:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xe0,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.MarshalSSZTo_31b:
  cmpq $0x0,0x30(%rdx)
  jne L_target_prysm.AttestationData.MarshalSSZTo_386
  mov %rcx,0x90(%rsp)
  mov %rax,0x50(%rsp)
  mov %rbx,0x40(%rsp)
  lea type__+100288(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.MarshalSSZTo_358
  mov 0xf0(%rsp),%rdx
  jmp L_target_prysm.AttestationData.MarshalSSZTo_370
L_target_prysm.AttestationData.MarshalSSZTo_358:
  mov 0xf0(%rsp),%rdx
  mov 0x30(%rdx),%r8
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_target_prysm.AttestationData.MarshalSSZTo_370:
  mov %rax,0x30(%rdx)
  mov 0x50(%rsp),%rax
  mov 0x90(%rsp),%rcx
  mov 0x40(%rsp),%rbx
L_target_prysm.AttestationData.MarshalSSZTo_386:
  mov 0x30(%rdx),%rdx
  add $0x8,%rbx
  mov (%rdx),%r8
  cmp %rbx,%rax
  jae L_target_prysm.AttestationData.MarshalSSZTo_3d3
  mov %rdx,0xa8(%rsp)
  mov %r8,0x78(%rsp)
  mov $0x8,%edi
  lea type__+48736(%rip),%rsi
  mov %rax,%rdx
  mov %rcx,%rax
  mov %rdx,%rcx
  callq runtime.growslice
  mov 0xa8(%rsp),%rdx
  mov 0x78(%rsp),%r8
  mov %rcx,%rsi
  mov %rax,%rcx
  mov %rsi,%rax
L_target_prysm.AttestationData.MarshalSSZTo_3d3:
  mov %r8,-0x8(%rbx,%rcx,1)
  mov 0x8(%rdx),%r8
  cmpq $0x20,0x10(%rdx)
  je L_target_prysm.AttestationData.MarshalSSZTo_3fc
  mov ssz.ErrBytesLength(%rip),%rdx
  mov ssz.ErrBytesLength+8(%rip),%r8
  xor %eax,%eax
  xor %ecx,%ecx
  xor %ebx,%ebx
  jmpq L_target_prysm.AttestationData.MarshalSSZTo_482
L_target_prysm.AttestationData.MarshalSSZTo_3fc:
  lea 0x20(%rbx),%rdx
  cmp %rdx,%rax
  jae L_target_prysm.AttestationData.MarshalSSZTo_448
  mov %rbx,0x58(%rsp)
  mov %r8,0xc8(%rsp)
  mov %rdx,%rbx
  mov $0x20,%edi
  lea type__+48736(%rip),%rsi
  mov %rax,%rdx
  mov %rcx,%rax
  mov %rdx,%rcx
  callq runtime.growslice
  mov 0xc8(%rsp),%r8
  mov %rbx,%rdx
  mov 0x58(%rsp),%rbx
  mov %rcx,%rsi
  mov %rax,%rcx
  mov %rsi,%rax
L_target_prysm.AttestationData.MarshalSSZTo_448:
  mov %rcx,0x98(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rax,0x68(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  xor %edx,%edx
  xor %r8d,%r8d
  mov 0x58(%rsp),%rax
  mov 0x68(%rsp),%rcx
  mov 0x98(%rsp),%rbx
L_target_prysm.AttestationData.MarshalSSZTo_482:
  test %rdx,%rdx
  je L_target_prysm.AttestationData.MarshalSSZTo_50f
  movups %xmm15,0xd0(%rsp)
  je L_target_prysm.AttestationData.MarshalSSZTo_49a
  mov 0x8(%rdx),%rdx
L_target_prysm.AttestationData.MarshalSSZTo_49a:
  mov %rdx,0xd0(%rsp)
  mov %r8,0xd8(%rsp)
  lea go_string._+3156(%rip),%rax
  mov $0xa,%ebx
  lea 0xd0(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target_prysm.AttestationData.MarshalSSZTo_4f9
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+3156(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target_prysm.AttestationData.MarshalSSZTo_4f9:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xe0,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.MarshalSSZTo_50f:
  mov %rdx,%rdi
  mov %r8,%rsi
  mov %rax,%rdx
  mov %rbx,%rax
  mov %rdx,%rbx
  add $0xe0,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.MarshalSSZTo_527:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xe0,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.MarshalSSZTo_545:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target_prysm.AttestationData.MarshalSSZTo_0
target_prysm.AttestationData.UnmarshalSSZ:
L_target_prysm.AttestationData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target_prysm.AttestationData.UnmarshalSSZ_2cb
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rbx,0x40(%rsp)
  nop
  cmp $0x80,%rcx
  jne L_target_prysm.AttestationData.UnmarshalSSZ_2b7
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  mov (%rbx),%rdx
  mov %rdx,(%rax)
  mov 0x8(%rbx),%rdx
  mov %rdx,0x8(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x38(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_86
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_86:
  mov %rax,0x20(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x10,%rbx
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x38(%rsp),%rdx
  movq $0x20,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_ca
  mov 0x20(%rsp),%rbx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_df
L_target_prysm.AttestationData.UnmarshalSSZ_ca:
  mov 0x10(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rbx
  mov %rbx,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_df:
  mov %rbx,0x10(%rdx)
  lea type__+100288(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_ff
  mov 0x38(%rsp),%rdx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_114
L_target_prysm.AttestationData.UnmarshalSSZ_ff:
  mov 0x38(%rsp),%rdx
  mov 0x28(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_114:
  mov %rax,0x18(%rsp)
  mov %rax,0x28(%rdx)
  mov 0x40(%rsp),%rdx
  mov 0x30(%rdx),%rdx
  nop
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x18(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_16c
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_16c:
  mov %rax,0x20(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x38,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x18(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_1ad
  mov 0x20(%rsp),%rbx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_1c2
L_target_prysm.AttestationData.UnmarshalSSZ_1ad:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rbx
  mov %rbx,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_1c2:
  mov %rbx,0x8(%rdx)
  lea type__+100288(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_1e2
  mov 0x38(%rsp),%rdx
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_1f7
L_target_prysm.AttestationData.UnmarshalSSZ_1e2:
  mov 0x38(%rsp),%rdx
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_1f7:
  mov %rax,0x18(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x40(%rsp),%rdx
  mov 0x58(%rdx),%rdx
  nop
  mov %rdx,(%rax)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x18(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target_prysm.AttestationData.UnmarshalSSZ_253
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_253:
  mov %rax,0x20(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x40(%rsp),%rbx
  add $0x60,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x18(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target_prysm.AttestationData.UnmarshalSSZ_294
  mov 0x20(%rsp),%rsi
  jmp L_target_prysm.AttestationData.UnmarshalSSZ_2a9
L_target_prysm.AttestationData.UnmarshalSSZ_294:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x20(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_target_prysm.AttestationData.UnmarshalSSZ_2a9:
  mov %rsi,0x8(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x28,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.UnmarshalSSZ_2b7:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x28,%rsp
  pop %rbp
  retq
L_target_prysm.AttestationData.UnmarshalSSZ_2cb:
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
  jmpq L_target_prysm.AttestationData.UnmarshalSSZ_0
