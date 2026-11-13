import Prysm.AttestationData.DecodeAcceptBlockRoot
import Prysm.Checkpoint.FunctionSpecsAsNestedField
import Runtime.NewobjectContract

/-!
# `(*v1alpha1.AttestationData).UnmarshalSSZ`, accept path, segment 3

    a.Source = new(Checkpoint)                      // always: the old pointer is overwritten
    if err = a.Source.UnmarshalSSZ(buf[48:88]); err != nil { return fmt.Errorf("Source: %w", err) }

Directive indices of `Prysm.AttestationData.Code.unmarshalSSZ`: 120 `L_208`, 121 store `Root.ptr` (rbx) through
rdx = receiver, 122–123 `lea type:Checkpoint; callq runtime.newobject`, 124–126 writeBarrier
test (`jne`, not taken), 127–128 reload the receiver, `jmp L_244`, 135 `L_244`, 136 store
`Source`, 137–142 arguments (rbx = buf + 48, rdi = cap − 48, rcx = 40) and `callq
Checkpoint.UnmarshalSSZ`, 143–144 `test %rax,%rax; je L_2d9`, 172 `L_2d9` (end).

The Checkpoint callee is used only through `Prysm.Checkpoint.Decode.accept_function_spec Heap S` (hypothesis of this segment;
`Decode.accept` discharges it by `Prysm.Checkpoint.Decode.accept_function_spec_holds`). The callee frame lives in the
`S + 96` stack bytes below the return slot rsp0 − 128 (`Decode.frame`): its scratch (S), return
slot, argument area (24), two untouched 16-byte gaps, three locals and its saved rbp.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- scratch (S) · rslot · mm (24) · gA (16) · l30 · l28 · l20 · gB (16) · fp: the `S + 96`
bytes below the callees' return slot, in the slots of the Checkpoint decoder's frame. -/
def Decode.frame (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8) : List UInt8 :=
  scratch ++ (rslot ++ (mm ++ (gA ++ (l30 ++ (l28 ++ (l20 ++ (gB ++ fp)))))))

theorem Decode.frame_length (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8) (S : Nat)
    (h0 : scratch.length = S) (h1 : rslot.length = 8) (h2 : mm.length = 24) (h3 : gA.length = 16)
    (h4 : l30.length = 8) (h5 : l28.length = 8) (h6 : l20.length = 8) (h7 : gB.length = 16) (h8 : fp.length = 8) :
    (Decode.frame scratch rslot mm gA l30 l28 l20 gB fp).length = S + 96 := by
  simp only [Decode.frame, List.length_append, *]; try omega

theorem Decode.frame_sep (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (scratch rslot mm gA l30 l28 l20 gB fp : List UInt8)
    (h0 : scratch.length = S) (h1 : rslot.length = 8) (h2 : mm.length = 24) (h3 : gA.length = 16)
    (h4 : l30.length = 8) (h5 : l28.length = 8) (h6 : l20.length = 8) (h7 : gB.length = 16) (h8 : fp.length = 8) :
    Eq ((Decode.frame scratch rslot mm gA l30 l28 l20 gB fp).At (x - 224 - BitVec.ofNat 64 S)) =
      Eq (scratch.At (x - 224 - BitVec.ofNat 64 S)) ⋆ Eq (rslot.At (x - 224)) ⋆ Eq (mm.At (x - 216))
      ⋆ Eq (gA.At (x - 192)) ⋆ Eq (l30.At (x - 176)) ⋆ Eq (l28.At (x - 168)) ⋆ Eq (l20.At (x - 160))
      ⋆ Eq (gB.At (x - 152)) ⋆ Eq (fp.At (x - 136)) := by
  simp only [Decode.frame]
  rw [at_app _ _ (b := x - 224) (by rw [h0]; bv_omega) (by simp [*]; omega),
    at_app _ _ (b := x - 216) (by rw [h1]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 192) (by rw [h2]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 176) (by rw [h3]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 168) (by rw [h4]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 160) (by rw [h5]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 152) (by rw [h6]; bv_omega) (by simp [*]),
    at_app _ _ (b := x - 136) (by rw [h7]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- Any block of `S + 96` bytes is an `Decode.frame` (slices by nested `drop`). -/
theorem Decode.frame_slices (stk : List UInt8) (S : Nat) :
    let t0 := stk.drop S; let t1 := t0.drop 8; let t2 := t1.drop 24; let t3 := t2.drop 16
    let t4 := t3.drop 8; let t5 := t4.drop 8; let t6 := t5.drop 8; let t7 := t6.drop 16
    stk = Decode.frame (stk.take S) (t0.take 8) (t1.take 24) (t2.take 16) (t3.take 8) (t4.take 8) (t5.take 8)
      (t6.take 16) t7 := by
  intro t0 t1 t2 t3 t4 t5 t6 t7
  simp only [Decode.frame, t0, t1, t2, t3, t4, t5, t6, t7, List.take_append_drop]

theorem Decode.frame_lens (stk : List UInt8) (S : Nat) (h : stk.length = S + 96) :
    (stk.take S).length = S ∧ ((stk.drop S).take 8).length = 8 ∧ (((stk.drop S).drop 8).take 24).length = 24
      ∧ ((((stk.drop S).drop 8).drop 24).take 16).length = 16
      ∧ (((((stk.drop S).drop 8).drop 24).drop 16).take 8).length = 8
      ∧ ((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).take 8).length = 8
      ∧ (((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).take 8).length = 8
      ∧ ((((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).drop 8).take 16).length = 16
      ∧ ((((((((stk.drop S).drop 8).drop 24).drop 16).drop 8).drop 8).drop 8).drop 16).length = 8 := by
  simp only [List.length_take, List.length_drop, h]; omega

/-- The 24-byte argument area as its three words (the Checkpoint spec names them). -/
theorem Decode.accept_mm3 (x : BitVec 64) (mm : List UInt8) (h : mm.length = 24) :
    Eq (mm.At (x - 216)) = Eq ((mm.take 8).At (x - 216)) ⋆ Eq (((mm.drop 8).take 8).At (x - 208))
      ⋆ Eq ((mm.drop 16).At (x - 200)) := by
  have e : mm = mm.take 8 ++ (((mm.drop 8).take 8) ++ mm.drop 16) := by
    conv => lhs; rw [← List.take_append_drop 8 mm, ← List.take_append_drop 8 (mm.drop 8)]
    simp only [List.drop_drop]
  conv => lhs; rw [e]
  rw [at_app _ _ (b := x - 208) (by simp [h]; bv_omega) (by simp [h]),
    at_app _ _ (b := x - 200) (by simp [h]; bv_omega) (by simp [h])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- A fresh 72-byte Checkpoint object as the receiver chunks of `Prysm.Checkpoint.Decode.accept_function_spec`. -/
theorem Decode.accept_obj72 (p : BitVec 64) :
    Eq ((List.replicate 72 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24))
      ⋆ Eq ((List.replicate 8 0).At (p + 32)) ⋆ Eq ((List.replicate 32 0).At (p + 40)) := by
  rw [show List.replicate 72 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ List.replicate 32 0)))) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 32) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 40) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Decode.accept_guard96 (x : BitVec 64) (g : Nat) (h : g + 224 < x.toNat) : g + 96 < (x - 128).toNat := by bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Segment 3: from `L_208` (directive 120) to `L_2d9` (directive 172): `Root.ptr`, a new
Source object (`NewobjectC`), and the Source decoder through `Prysm.Checkpoint.Decode.accept_function_spec`. -/
theorem Decode.source (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (rsp0 r140 guard : UInt64) (rcv bf pb : BitVec 64) (se sroot : List UInt8) (hse : se.length = 8)
    (hsroot : sroot.length = 32)
    (s4 q0 q1 rslot lo aP aS : List UInt8)
    (h4 : s4.length = 8) (hq0 : q0.length = 8) (hq1 : q1.length = 8) (hrs : rslot.length = 8)
    (haP : aP.length = 8) (haS : aS.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 104 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (hrdx : s.regs.rdx.toBitVec = rcv) (hrbx : s.regs.rbx.toBitVec = pb)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq (s4.At (rsp0.toBitVec + 32))
      ⋆ Eq (q0.At (rsp0.toBitVec - 120)) ⋆ Eq (q1.At (rsp0.toBitVec - 112))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 128)) ⋆ Eq (lo.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (aP.At (rcv + 24)) ⋆ Eq (aS.At (rcv + 48))
      ⋆ Eq (se.At (bf + 48)) ⋆ Eq (sroot.At (bf + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 224 < rsp0.toNat)
    (hno : NewobjectC Heap ElfData.AttestationData.adCpType_addr 72 (S + 96)) (hcp : Prysm.Checkpoint.Decode.accept_function_spec Heap S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 172) ∧ st.data.regs.rsp = { toBitVec := rsp0.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 } ∧ st.data.regs.r14 = r140 ∧
        ∃ (ps p1 : BitVec 64) (lo' : List UInt8), lo'.length = S + 96 ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq (s4.At (rsp0.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (bf + 48).toInt).At (rsp0.toBitVec - 112))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 143)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 72 - 32)
          ⋆ Eq ((Int.toBytes 8 pb.toInt).At (rcv + 24)) ⋆ Eq ((Int.toBytes 8 ps.toInt).At (rcv + 48))
          ⋆ Eq ((List.replicate 8 0).At ps) ⋆ Eq (se.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32)) ⋆ Eq ((List.replicate 32 0).At (ps + 40))
          ⋆ Eq (sroot.At p1)
          ⋆ Eq (se.At (bf + 48)) ⋆ Eq (sroot.At (bf + 56))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 120)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrdx hrbx h_mem ⊢
  subst rsp rbp r14 hrdx hrbx
  have := rsp0.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk unmarshalSSZ 120
  kat hk unmarshalSSZ 121
  apply store_step_at _ _ (rdx.toBitVec + 24) _ _ _ aP _ _ (by attestation_data_addr) (by ecancel) (by exact haP)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk unmarshalSSZ 122
  kat hk unmarshalSSZ 123
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ rslot _ _ (Decode.accept_call _) (by ecancel) (by exact hrs)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  rw [Decode.accept_call] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 123 + 1)) avail lo q0 _ rfl (by omega) hlo hq0
    (by dsimp only; rw [Decode.accept_lo _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega]; ecancel)) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, sp3, hstk3, hsp3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 Hm3
  rw [Decode.accept_ret] at hrsp3
  subst hrsp3 hr143 hrbp3
  rw [Decode.accept_lo _ _ hS, show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega, Decode.accept_obj72] at Hm3
  kat hk unmarshalSSZ 124
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk unmarshalSSZ 125
  kat hk unmarshalSSZ 126
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk unmarshalSSZ 127
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rdx.toBitVec.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 128
  klabel hk hf unmarshalSSZ 135
  kat hk unmarshalSSZ 135
  kat hk unmarshalSSZ 136
  apply store_step_at _ _ (rdx.toBitVec + 48) _ _ _ aS _ _ (by attestation_data_addr) (by ecancel) (by exact haS)
  intro m3' H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk unmarshalSSZ 137
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 bf.toInt) _ _ (by attestation_data_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk unmarshalSSZ 138
  kat hk unmarshalSSZ 139
  apply load_step_at _ _ (rsp0.toBitVec + 32) _ _ s4 _ _ (by attestation_data_addr) (by ecancel) (by exact h4)
  kunfold
  kat hk unmarshalSSZ 140
  kat hk unmarshalSSZ 141
  kat hk unmarshalSSZ 142
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 123 + 1)).toBitVec.toInt) _ _
    (Decode.accept_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4' H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  rw [Decode.accept_call] at *
  -- the callee frame in the S + 96 stack bytes
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := Decode.frame_lens stk3 S hstk3
  rw [Decode.frame_slices stk3 S] at H4
  try dsimp only at H4
  rw [Decode.frame_sep _ S hS _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 l6 l7 l8, Decode.accept_mm3 _ _ l2] at H4
  rw [show (48 : BitVec 64) + bf = bf + 48 from BitVec.add_comm _ _]
  rw [show bf + 56 = bf + 48 + 8 by bv_omega] at H4
  refine eventually_trans _ _ _ _ (hcp _ (Host.addrOf (k + 142 + 1)) guard (avail - 72) se sroot _ sp3 q1 _ _ _
    ((((stk3.drop S).drop 8).take 24).take 8) (((((stk3.drop S).drop 8).take 24).drop 8).take 8)
    ((((stk3.drop S).drop 8).take 24).drop 16) _
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 32 0) _ _
    hse hsroot l8 hsp3 hq1 l6 l5 l4 (by simp [hstk3]) (by simp [hstk3]) (by simp [hstk3]) l1
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hS8 hS l0
    (Decode.accept_guard96 _ _ hguard) rfl (by omega)
    (by dsimp only
        rw [show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by bv_omega,
          show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega,
          show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by bv_omega,
          show rsp0.toBitVec - 128 - 32 = rsp0.toBitVec - 160 by bv_omega,
          show rsp0.toBitVec - 128 - 40 = rsp0.toBitVec - 168 by bv_omega,
          show rsp0.toBitVec - 128 - 48 = rsp0.toBitVec - 176 by bv_omega,
          show rsp0.toBitVec - 128 - 72 = rsp0.toBitVec - 200 by bv_omega,
          show rsp0.toBitVec - 128 - 80 = rsp0.toBitVec - 208 by bv_omega,
          show rsp0.toBitVec - 128 - 88 = rsp0.toBitVec - 216 by bv_omega,
          show rsp0.toBitVec - 128 - 96 = rsp0.toBitVec - 224 by bv_omega]
        ecancel)) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, p1, scr, mm, rs', hscr, hmm, hrs', Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  rw [Decode.accept_ret] at hrsp5
  subst rax5 rbx5 rsp5 rbp5 r145
  try dsimp only at Hm5
  rw [show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by bv_omega,
    show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega,
    show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by bv_omega,
    show rsp0.toBitVec - 128 - 32 = rsp0.toBitVec - 160 by bv_omega,
    show rsp0.toBitVec - 128 - 40 = rsp0.toBitVec - 168 by bv_omega,
    show rsp0.toBitVec - 128 - 48 = rsp0.toBitVec - 176 by bv_omega,
    show rsp0.toBitVec - 128 - 88 = rsp0.toBitVec - 216 by bv_omega,
    show rsp0.toBitVec - 128 - 96 = rsp0.toBitVec - 224 by bv_omega,
    show bf + 48 + 8 = bf + 56 by bv_omega] at Hm5
  kat hk unmarshalSSZ 143
  intro _
  kat hk unmarshalSSZ 144
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf unmarshalSSZ 172
  apply Eventually.done
  rw [show k + 142 + 1 = k + 143 from rfl] at Hm5
  exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, p1, Decode.frame scr rs' mm _ (Int.toBytes 8 0) (Int.toBytes 8 0)
    (Int.toBytes 8 p1.toInt) _ (Int.toBytes 8 (rsp0.toBitVec - 8#64).toInt),
    Decode.frame_length _ _ _ _ _ _ _ _ _ S hscr hrs' hmm l3 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
      (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _),
    by rw [Decode.frame_sep _ S hS _ _ _ _ _ _ _ _ _ hscr hrs' hmm l3 (Int.toBytes_length 8 _) (Int.toBytes_length 8 _)
          (Int.toBytes_length 8 _) l7 (Int.toBytes_length 8 _)]
       ecancel⟩

end Prysm.AttestationData
