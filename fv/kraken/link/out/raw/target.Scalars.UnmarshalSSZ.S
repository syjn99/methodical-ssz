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
