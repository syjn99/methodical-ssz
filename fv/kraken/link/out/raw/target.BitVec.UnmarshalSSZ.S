target.BitVec.UnmarshalSSZ:
L_target.BitVec.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_target.BitVec.UnmarshalSSZ_15f
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nopw (%rax,%rax,1)
  cmp $0x1,%rcx
  jne L_target.BitVec.UnmarshalSSZ_14b
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  mov %rbx,%rax
  mov $0x1,%ebx
  mov %rdi,%rcx
  mov $0x4,%edi
  callq ssz.ValidateBitvector
  test %rax,%rax
  je L_target.BitVec.UnmarshalSSZ_b9
  movups %xmm15,0x38(%rsp)
  je L_target.BitVec.UnmarshalSSZ_5a
  mov 0x8(%rax),%rax
L_target.BitVec.UnmarshalSSZ_5a:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+511(%rip),%rax
  mov $0x5,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nopl (%rax)
  callq fmt.errorf
  test %rax,%rax
  jne L_target.BitVec.UnmarshalSSZ_b3
  nop
  lea type__+82848(%rip),%rax
  callq runtime.newobject
  movq $0x5,0x8(%rax)
  lea go_string._+511(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_target.BitVec.UnmarshalSSZ_b3:
  add $0x48,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_b9:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+48736(%rip),%rax
  xor %ebx,%ebx
  mov $0x1,%ecx
  callq runtime.makeslice
  mov 0x58(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_103
  mov (%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_103:
  mov %rax,(%rdx)
  mov 0x60(%rsp),%rcx
  movzbl (%rcx),%ecx
  mov %cl,(%rax)
  movq $0x1,0x8(%rdx)
  movq $0x1,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_target.BitVec.UnmarshalSSZ_138
  mov (%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_target.BitVec.UnmarshalSSZ_138:
  mov %rax,(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x48,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_14b:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x48,%rsp
  pop %rbp
  retq
L_target.BitVec.UnmarshalSSZ_15f:
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
