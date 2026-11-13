runtime.memmove:
  mov %rax,%rdi
  mov %rbx,%rsi
  mov %rcx,%rdx
  jmp L_model_copy
runtime.growslice:
  mov %rbx,%rdx
  sub %rdi,%rdx
  mov %rax,%rsi
  mov runtime.modelBumpPointer(%rip),%rdi
  lea 0xc0(%rbx,%rbx,1),%rcx
  lea (%rdi,%rcx,1),%r8
  mov %r8,runtime.modelBumpPointer(%rip)
  mov %rdi,%rax
  jmp L_model_copy
L_model_copy:
  mov $0x0,%r10
L_model_copy_loop:
  cmp %rdx,%r10
  je L_model_copy_done
  movzbl (%rsi,%r10,1),%r11d
  mov %r11b,(%rdi,%r10,1)
  add $0x1,%r10
  jmp L_model_copy_loop
L_model_copy_done:
  retq
