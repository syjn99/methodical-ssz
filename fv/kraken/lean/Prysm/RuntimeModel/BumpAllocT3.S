runtime.makeslice:
  lea type__+387456(%rip),%rsi
  cmp %rsi,%rax
  je L_lvBumpT3_8
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
L_lvBumpT3_8:
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rcx,8),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
