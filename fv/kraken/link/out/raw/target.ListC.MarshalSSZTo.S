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
  nopl (%rax)
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
  data16 nop
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
