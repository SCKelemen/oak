bench_tiled = {
  bind x0, w1 = a
  clobber x9, x10, x11, x12, x13, x14, x15, x19, x20, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, x2
  frame 176
  sub sp, sp, #176
  stp x19, x20, [sp]
  mov x19, x0
  mov w20, w1
head_1:
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #144]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #148]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #152]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #156]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #160]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #164]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #168]
  mov w9, wzr
  fmov s16, w9
  str s16, [sp, #172]
  mov w2, wzr
loop_4:
  cmp w20, #8
  b.lo done_5
  mov w9, w20
  sub w9, w9, #8
  cmp w2, w9
  b.hi done_5
  ldr s16, [sp, #144]
  ldr s17, [x19, w2, uxtw #2]
  ldr s18, [x19, w2, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #144]
  ldr s16, [sp, #148]
  add w9, w2, #1
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #1
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #148]
  ldr s16, [sp, #152]
  add w9, w2, #2
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #2
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #152]
  ldr s16, [sp, #156]
  add w9, w2, #3
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #3
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #156]
  ldr s16, [sp, #160]
  add w9, w2, #4
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #4
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #160]
  ldr s16, [sp, #164]
  add w9, w2, #5
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #5
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #164]
  ldr s16, [sp, #168]
  add w9, w2, #6
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #6
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #168]
  ldr s16, [sp, #172]
  add w9, w2, #7
  ldr s17, [x19, w9, uxtw #2]
  add w9, w2, #7
  ldr s18, [x19, w9, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #172]
  add w2, w2, #8
  b loop_4
done_5:
loop_6:
  cmp w2, w20
  b.hs done_7
  ldr s16, [sp, #144]
  ldr s17, [x19, w2, uxtw #2]
  ldr s18, [x19, w2, uxtw #2]
  fmul s17, s17, s18
  fadd s16, s16, s17
  str s16, [sp, #144]
  add w2, w2, #1
  b loop_6
done_7:
  ldr s16, [sp, #144]
  ldr s17, [sp, #148]
  fadd s16, s16, s17
  ldr s17, [sp, #152]
  ldr s18, [sp, #156]
  fadd s17, s17, s18
  fadd s16, s16, s17
  ldr s17, [sp, #160]
  ldr s18, [sp, #164]
  fadd s17, s17, s18
  ldr s18, [sp, #168]
  ldr s19, [sp, #172]
  fadd s18, s18, s19
  fadd s17, s17, s18
  fadd s16, s16, s17
  fmov s0, s16
ret_2:
  ldp x19, x20, [sp]
  add sp, sp, #176
  ret
}
