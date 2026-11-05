target.Nested.UnmarshalSSZ:
L_target.Nested.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.Nested.UnmarshalSSZ_227
  push %rbp
  mov %rsp,%rbp
  sub $0x58,%rsp
  mov %rbx,0x70(%rsp)
  nopw (%rax,%rax,1)
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
  lea go_string._+516(%rip),%rax
  mov $0x5,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  data16 nop
  test %rax,%rax
  jne L_target.Nested.UnmarshalSSZ_12e
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+516(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.Nested.UnmarshalSSZ_12e:
  add $0x58,%rsp
  pop %rbp
  retq
L_target.Nested.UnmarshalSSZ_134:
  lea type__+83104(%rip),%rax
  nopl (%rax,%rax,1)
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_target.Nested.UnmarshalSSZ_155
  mov 0x68(%rsp),%rdx
  jmp L_target.Nested.UnmarshalSSZ_16c
L_target.Nested.UnmarshalSSZ_155:
  mov 0x68(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  data16 nop
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
  lea go_string._+521(%rip),%rax
  mov $0x5,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nopl (%rax)
  callq fmt.errorf
  test %rax,%rax
  jne L_target.Nested.UnmarshalSSZ_1f3
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+521(%rip),%rcx
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
  nopl (%rax,%rax,1)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_target.Nested.UnmarshalSSZ_0
