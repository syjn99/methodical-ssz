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
  lea go_string._+521(%rip),%rax
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
  lea go_string._+521(%rip),%rcx
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
