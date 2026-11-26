runtime.newobject:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x10(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
