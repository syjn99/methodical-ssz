target.BitL.MarshalSSZTo:
L_target.BitL.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_target.BitL.MarshalSSZTo_1bf
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov %rax,0xa0(%rsp)
  lea 0x4(%rcx),%rdx
  nop
  cmp %rdx,%rdi
  jae L_target.BitL.MarshalSSZTo_5f
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rax,%rbx
  mov %rcx,%rdi
  mov 0xa0(%rsp),%rax
L_target.BitL.MarshalSSZTo_5f:
  mov %rbx,0x68(%rsp)
  mov %rdx,0x40(%rsp)
  mov %rdi,0x48(%rsp)
  movl $0x4,-0x4(%rdx,%rbx,1)
  mov 0x8(%rax),%rbx
  mov 0x10(%rax),%rcx
  mov (%rax),%rax
  mov $0x800,%edi
  callq ssz.ValidateBitlist
  test %rax,%rax
  je L_target.BitL.MarshalSSZTo_118
  movups %xmm15,0x80(%rsp)
  je L_target.BitL.MarshalSSZTo_a3
  mov 0x8(%rax),%rax
L_target.BitL.MarshalSSZTo_a3:
  mov %rax,0x80(%rsp)
  mov %rbx,0x88(%rsp)
  lea go_string._+526(%rip),%rax
  mov $0x5,%ebx
  lea 0x80(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_target.BitL.MarshalSSZTo_102
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+526(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.BitL.MarshalSSZTo_102:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0x90,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_118:
  mov %rbx,0x70(%rsp)
  mov %rax,0x50(%rsp)
  mov 0xa0(%rsp),%rdx
  mov 0x8(%rdx),%rdi
  mov 0x40(%rsp),%r8
  lea (%r8,%rdi,1),%r9
  mov (%rdx),%rdx
  mov 0x48(%rsp),%rcx
  nop
  cmp %r9,%rcx
  jb L_target.BitL.MarshalSSZTo_14c
  mov 0x68(%rsp),%rsi
  jmp L_target.BitL.MarshalSSZTo_17f
L_target.BitL.MarshalSSZTo_14c:
  mov %rdi,0x60(%rsp)
  mov %rdx,0x78(%rsp)
  mov 0x68(%rsp),%rax
  mov %r9,%rbx
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov 0x78(%rsp),%rdx
  mov 0x60(%rsp),%rdi
  mov 0x40(%rsp),%r8
  mov %rax,%rsi
  mov %rbx,%r9
L_target.BitL.MarshalSSZTo_17f:
  mov %rsi,0x78(%rsp)
  mov %r9,0x60(%rsp)
  mov %rcx,0x58(%rsp)
  lea (%rsi,%r8,1),%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  callq runtime.memmove
  mov 0x78(%rsp),%rax
  mov 0x60(%rsp),%rbx
  mov 0x58(%rsp),%rcx
  mov 0x50(%rsp),%rdi
  mov 0x70(%rsp),%rsi
  add $0x90,%rsp
  pop %rbp
  retq
L_target.BitL.MarshalSSZTo_1bf:
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
