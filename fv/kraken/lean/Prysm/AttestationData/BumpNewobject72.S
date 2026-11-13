runtime.newobject:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x48(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
