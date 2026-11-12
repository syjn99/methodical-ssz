runtime.makeslice:
  lea type__+337600(%rip),%rsi
  cmp %rsi,%rax
  je L_lvBumpT_24
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
L_lvBumpT_24:
  mov runtime.fvBump(%rip),%rdx
  lea (%rcx,%rcx,2),%rsi
  lea (%rdx,%rsi,8),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
