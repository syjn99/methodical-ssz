runtime.makeslice:
  mov runtime.fvBump(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
