runtime.makeslice:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
