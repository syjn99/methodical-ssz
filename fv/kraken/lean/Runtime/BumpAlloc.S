runtime.makeslice:
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rcx,8),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
