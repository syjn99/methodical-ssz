runtime.makeslice:
  lea type__+387456(%rip),%rsi
  cmp %rsi,%rax
  je L_model_bump_uint64_columns
  mov runtime.modelBumpPointer(%rip),%rdx
  lea (%rdx,%rcx,1),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
L_model_bump_uint64_columns:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea (%rdx,%rcx,8),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
