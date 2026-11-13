github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_246
  push %rbp
  mov %rsp,%rbp
  sub $0x58,%rsp
  mov %rbx,0x70(%rsp)
  nop
  cmp $0x4d8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_85
  mov %rax,0x68(%rsp)
  mov %rdi,0x80(%rsp)
  mov %rbx,0x70(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x21,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x68(%rsp),%rdx
  movq $0x21,0x10(%rdx)
  movq $0x21,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_7d:
  mov %rax,0x8(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_a2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_85:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99:
  mov %r9,(%rdi,%rsi,8)
  mov 0x28(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_a2:
  cmp $0x21,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_166
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23f
  mov %rsi,0x38(%rsp)
  mov %rax,0x30(%rsp)
  mov %r8,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x40(%rsp)
  mov 0x30(%rsp),%rdx
  mov 0x70(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  mov 0x38(%rsp),%rdi
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23a
  lea (%rdi,%rdi,2),%rsi
  mov 0x8(%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_14c
  mov 0x40(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_14c:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x40(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_166:
  lea type__+1421952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_182
  mov 0x68(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_197
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_182:
  mov 0x68(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_197:
  mov %rax,0x20(%rdx)
  mov 0x70(%rsp),%rbx
  add $0x420,%rbx
  mov 0x80(%rsp),%rdi
  add $-0x420,%rdi
  mov $0xb8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_234
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_1d6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_1d6:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+15010(%rip),%rax
  mov $0x8,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_22e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+15010(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_22e:
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_234:
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23a:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23f:
  nop
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_246:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_0
