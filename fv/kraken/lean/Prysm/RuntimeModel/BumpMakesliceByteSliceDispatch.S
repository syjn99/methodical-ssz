runtime.makeslice:
  lea type__+337600(%rip),%rsi
  cmp %rsi,%rax
  je L_model_bump_byte_slice
  mov runtime.modelBumpPointer(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
L_model_bump_byte_slice:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea (%rcx,%rcx,2),%rsi
  lea (%rdx,%rsi,8),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
