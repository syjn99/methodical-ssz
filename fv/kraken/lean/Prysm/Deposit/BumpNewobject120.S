runtime.newobject:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x78(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
