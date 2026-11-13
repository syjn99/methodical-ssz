runtime.newobject:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x18(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
