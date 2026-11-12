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
  lea go_string._+526(%rip),%rax
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
  lea go_string._+526(%rip),%rcx
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
  lea runtime.zerobase(%rip),%rcx
  xor %edx,%edx
  xor %esi,%esi
  jmp L_target.BitL.UnmarshalSSZ_13f
L_target.BitL.UnmarshalSSZ_119:
  lea runtime.zerobase(%rip),%rax
  mov 0x28(%rsp),%rbx
  xor %ecx,%ecx
  mov %rbx,%rdi
  lea type__+48736(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdx
  mov %rbx,%rsi
  mov %rax,%rcx
L_target.BitL.UnmarshalSSZ_13f:
  mov %rdx,0x40(%rsp)
  mov %rsi,0x38(%rsp)
  mov %rcx,0x58(%rsp)
  mov %rcx,%rax
  mov 0x48(%rsp),%rbx
  mov 0x28(%rsp),%rcx
  nop
  callq runtime.memmove
  mov 0x38(%rsp),%rdx
  mov 0x80(%rsp),%rsi
  mov %rdx,0x8(%rsi)
  mov 0x40(%rsp),%rdx
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
