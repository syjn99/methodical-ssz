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
