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
  data16 nop
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
  nopl (%rax)
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
  data16 nop
  je L_target_prysm.AttestationData.MarshalSSZTo_2a6
  mov 0x8(%r8),%r8
L_target_prysm.AttestationData.MarshalSSZTo_2a6:
  mov %r8,0xb8(%rsp)
  mov %r9,0xc0(%rsp)
  lea go_string._+3151(%rip),%rax
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
  lea go_string._+3151(%rip),%rcx
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
  nopl (%rax,%rax,1)
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
  lea go_string._+3161(%rip),%rax
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
  lea go_string._+3161(%rip),%rcx
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
