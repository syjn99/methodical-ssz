runtime.newobject:
  lea type__+1464512(%rip),%rsi
  cmp %rsi,%rax
  je L_model_newobject_struct
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x48(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
L_model_newobject_struct:
  mov runtime.modelBumpPointer(%rip),%rdx
  lea 0x60(%rdx),%rsi
  mov %rsi,runtime.modelBumpPointer(%rip)
  mov %rdx,%rax
  retq
