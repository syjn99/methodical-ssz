import Codec.SegmentAddress
import Prysm.AttestationData.EncodeSourceCall

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segment 5: the Target encoder and the return

    if a.Target == nil { a.Target = new(Checkpoint) }   // not taken
    if dst, err = a.Target.MarshalSSZTo(dst); err != nil { return nil, ssz.ErrMarshalSSZ… }
    return dst, nil

Directive indices of `Prysm.AttestationData.Code.marshalSSZTo` follow.
147: `L_264`.
148: reload the receiver (rsp + 8).
149–150: `cmpq $0x0,0x38(%rdx); jne L_2d2` (taken).
171: `L_2d2`.
172–176: the arguments rax = `Target`, rbx = `dst.ptr`, rcx = `len + 88` and rdi = `cap`.
They come from the result registers of the Source call.
177: `callq Checkpoint.MarshalSSZTo`, through `Prysm.Checkpoint.Encode.fast_path_function_spec S`.
178–179: `test %rdi,%rdi; je L_377` (nil error, taken).
212: `L_377`.
213–216: the epilogue and `retq`.
The function returns the registers of the Target call, `(dst.ptr, len + 128, cap, nil)`.
-/

open Machine Runtime Prysm.AttestationData.Code

namespace Prysm.AttestationData

/-- `contains` on an append, for the label checks of directives 171 and 212.
One check on such a long prefix exceeds the default recursion depth.
So the proofs check the prefix in two parts. -/
theorem Encode.contains_append_false {α : Type} [DecidableEq α] (l1 l2 : List α) (d : α)
    (h1 : @List.contains _ instBEqOfDecidableEq l1 d = false) (h2 : @List.contains _ instBEqOfDecidableEq l2 d = false) :
    @List.contains _ instBEqOfDecidableEq (l1 ++ l2) d = false := by
  induction l1 with
  | nil => simpa using h2
  | cons a t ih =>
    simp only [List.cons_append, List.contains_cons, Bool.or_eq_false_iff] at h1 ⊢
    exact ⟨h1.1, ih h1.2⟩

variable [Host]

/-- The label `L_2d2` (directive 171) of the encoder. -/
theorem Encode.label_2d2 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2d2" = Host.addrOf (k + 171) :=
  Machine.label_at' hk hf (j := 171)
    (by
      rw [show (171 : Nat) = 171 + 0 from rfl, ← List.getElem?_drop]
      simp only [marshalSSZTo, List.drop_succ_cons, List.drop_zero, List.getElem?_cons_zero])
    (by
      rw [show (171 : Nat) = 85 + 86 from rfl, List.take_add]
      apply Encode.contains_append_false
      · simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]
        decide
      · simp only [marshalSSZTo, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
          List.contains_cons, List.contains_nil]
        decide)

/-- The label `L_377` (directive 212) of the encoder. -/
theorem Encode.label_377 (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k) :
    label "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_377" = Host.addrOf (k + 212) :=
  Machine.label_at' hk hf (j := 212)
    (by
      rw [show (212 : Nat) = 212 + 0 from rfl, ← List.getElem?_drop]
      simp only [marshalSSZTo, List.drop_succ_cons, List.drop_zero, List.getElem?_cons_zero])
    (by
      rw [show (212 : Nat) = 106 + 106 from rfl, List.take_add]
      apply Encode.contains_append_false
      · simp only [marshalSSZTo, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]
        decide
      · simp only [marshalSSZTo, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
          List.contains_cons, List.contains_nil]
        decide)

/-- Segment 5 of the encoder fast path: from `L_264` (directive 147) to the return, through the Target encoder. -/
theorem Encode.target_call (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (S : Nat) (hcp : Prysm.Checkpoint.Encode.fast_path_function_spec S)
    (x rcv pt p d cap : BitVec 64) (hpt : pt ≠ 0) (ra rb0 guard : UInt64) (s : MachineData)
    (cst e8 cC ctl root pre d0 d1 rslot fp s2 l16 l24 l32 t40 t30 rs scratch : List UInt8)
    (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (hroot : root.length = 32) (hpre : pre.length = s.regs.rbx.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (hrslot : rslot.length = 8) (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hrs : rs.length = 8) (hsc : scratch.length = S)
    (hrsp : s.regs.rsp = { toBitVec := x - 184 }) (hrax : s.regs.rax.toBitVec = d) (hrcx : s.regs.rcx.toBitVec = cap)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (x + 0)) ⋆ Eq ((Int.toBytes 8 rb0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (x + 8)) ⋆ Eq ((Int.toBytes 8 pt.toInt).At (rcv + 56))
      ⋆ Eq (rslot.At (x - 192)) ⋆ Eq (fp.At (x - 200)) ⋆ Eq (s2.At (x - 176))
      ⋆ Eq (l16.At (x - 208)) ⋆ Eq (l24.At (x - 216)) ⋆ Eq (l32.At (x - 224)) ⋆ Eq (t30.At (x - 240))
      ⋆ Eq (t40.At (x - 256)) ⋆ Eq (rs.At (x - 312)) ⋆ Eq (scratch.At (x - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At pt) ⋆ Eq (e8.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC.At (pt + 32)) ⋆ Eq (ctl.At (pt + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At d) ⋆ Eq (d0.At (d + s.regs.rbx.toBitVec)) ⋆ Eq (d1.At (d + s.regs.rbx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat + 312 < x.toNat)
    (hcap : s.regs.rbx.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toBitVec = d
        ∧ st.data.regs.rbx.toNat = s.regs.rbx.toNat + 40 ∧ st.data.regs.rcx.toBitVec = cap
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = { toBitVec := x + 8 } ∧ st.data.regs.rbp = rb0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At (x + 0)) ⋆ Eq ((Int.toBytes 8 rb0.toBitVec.toInt).At (x - 8))
          ⋆ Eq ((Int.toBytes 8 rcv.toInt).At (x + 8)) ⋆ Eq ((Int.toBytes 8 pt.toInt).At (rcv + 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (x - 192))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (x - 200))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 176))
          ⋆ Eq ((Int.toBytes 8 d.toInt).At (x - 208)) ⋆ Eq ((Int.toBytes 8 cap.toInt).At (x - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rbx.toBitVec + 40).toInt).At (x - 224)) ⋆ Eq (u.At (x - 240))
          ⋆ Eq (e8.At (x - 256)) ⋆ Eq (t.At (x - 248))
          ⋆ Eq (rs'.At (x - 312)) ⋆ Eq (scr.At (x - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At pt) ⋆ Eq (e8.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC.At (pt + 32)) ⋆ Eq (ctl.At (pt + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At d) ⋆ Eq (e8.At (d + s.regs.rbx.toBitVec)) ⋆ Eq (root.At (d + s.regs.rbx.toBitVec + 8)) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 147)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hrsp hrax hrcx hpre hcap ⊢
  subst rsp hrax hrcx
  step_directive hk marshalSSZTo 147
  step_directive hk marshalSSZTo 148
  apply load_step_at _ _ (x + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 149
  apply load_step_at _ _ (rcv + 56) _ _ (Int.toBytes 8 pt.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 150
  split
  case isFalse h => exfalso; apply h; simp [CondCode.interp, StatusFlags.from_result]; exact hpt
  simp only [Effects.All]
  rw [Encode.label_2d2 k hk hf]
  step_directive hk marshalSSZTo 171
  step_directive hk marshalSSZTo 172
  apply load_step_at _ _ (rcv + 56) _ _ (Int.toBytes 8 pt.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 173
  step_directive hk marshalSSZTo 174
  step_directive hk marshalSSZTo 175
  step_directive hk marshalSSZTo 176
  step_directive hk marshalSSZTo 177
  apply store_step_at _ _ (x - 192) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrslot)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  rw [show x - 184 - 8#64 = x - 192 by segment_addr]
  refine eventually_trans _ _ _ _ (hcp _ (Host.addrOf (k + 177 + 1)) guard p cst e8 cC ctl root pre d0 d1 fp s2
    l16 l24 l32 t40 t30 rs scratch _ hcst he8 hcC hctl hroot hd0 hd1 hpre hfp h2 hl16 hl24 hl32 ht40 ht30 hrs hsc
    (Encode.call_guard x _ hguard).1 (Encode.call_guard x _ hguard).2 hcap hcap63
    (by
      dsimp only
      rw [show x - 192 - 8 = x - 200 by segment_addr, show x - 192 + 16 = x - 176 by segment_addr,
        show x - 192 - 16 = x - 208 by segment_addr, show x - 192 - 24 = x - 216 by segment_addr,
        show x - 192 - 32 = x - 224 by segment_addr, show x - 192 - 48 = x - 240 by segment_addr,
        show x - 192 - 64 = x - 256 by segment_addr, show x - 192 - 120 = x - 312 by segment_addr]
      ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrcx5, hrdi5, hrsi5, hrsp5, hrbp5, hr145, t, u, scr, rs', ht, hu, hscr, hrs',
    Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrcx5 hrdi5 hrsi5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrcx5 hrdi5 hrsi5 hrsp5 hrbp5 hr145 Hm5
  rw [Encode.root_ret] at hrsp5
  subst rax5 rcx5 rdi5 rsi5 rsp5 rbp5 r145
  step_directive hk marshalSSZTo 178
  intro _
  step_directive hk marshalSSZTo 179
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [Encode.label_377 k hk hf]
  step_directive hk marshalSSZTo 212
  step_directive hk marshalSSZTo 213
  step_directive hk marshalSSZTo 214
  apply load_step_at _ _ (x - 8) _ _ (Int.toBytes 8 rb0.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hk marshalSSZTo 215
  step_directive hk marshalSSZTo 216
  apply load_step_at _ _ (x + 0) _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, t, u, scr, rs', ht, hu, hscr, hrs', ?hmem⟩
  case hmem =>
    rw [show k + 177 + 1 = k + 178 from rfl,
      show x - 192 - 8 = x - 200 by segment_addr, show x - 192 + 16 = x - 176 by segment_addr,
      show x - 192 - 16 = x - 208 by segment_addr, show x - 192 - 24 = x - 216 by segment_addr,
      show x - 192 - 32 = x - 224 by segment_addr, show x - 192 - 48 = x - 240 by segment_addr,
      show x - 192 - 64 = x - 256 by segment_addr, show x - 192 - 56 = x - 248 by segment_addr,
      show x - 192 - 120 = x - 312 by segment_addr] at Hm5
    simp only [Std.ExtHashMap.sep_emp] at Hm5
    exact cast (congrFun (by ac_rfl) _) Hm5
  all_goals first
    | exact trivial
    | exact hrbx5
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; segment_addr)

end Prysm.AttestationData
