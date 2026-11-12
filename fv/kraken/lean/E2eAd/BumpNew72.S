runtime.newobject:
  mov runtime.fvBump(%rip),%rdx
  lea 0x48(%rdx),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
