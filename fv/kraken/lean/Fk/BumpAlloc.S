runtime.makeslice:
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rbx,8),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
