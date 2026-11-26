module

public import Codec.SegmentAddress
public import Runtime.NewobjectContract
public import Prysm.AttestationData.DecodeAccept
public import Prysm.SingleAttestation.DecodeAcceptHead
public import Prysm.SingleAttestation.Code

@[expose] public section

/-!
# `(*v1alpha1.SingleAttestation).UnmarshalSSZ`, accept path, Data segment

    c.Data = new(AttestationData)                   // always: the old pointer is overwritten
    if err = c.Data.UnmarshalSSZ(buf[16:144]); err != nil { return fmt.Errorf("Data: %w", err) }

Directive indices of `Prysm.SingleAttestation.Code.unmarshalSSZ`: 85 `L_167`, 86–87 `lea type:AttestationData; callq
runtime.newobject`, 88–89 writeBarrier test (`jne`, not taken), 90–91 reload the receiver, `jmp L_19e`, 98 `L_19e`,
99 store `Data`, 100–106 arguments (rbx = buf + 16, rdi = cap − 16, rcx = 128) and `callq AttestationData.UnmarshalSSZ`,
107–108 `test %rax,%rax; je L_234`, 136 `L_234` (end).

The AttestationData callee is discharged by `Prysm.AttestationData.Decode.accept` (its code is placed in the host at `kA`, its
callees at `kS`, `kI`, `kC`, `kE`); its runtime contracts are hypotheses of this segment.
The callee's whole stack (its entry rsp = rsp0 − 128, scratch `Sd`) lies in the `Sd + 224` bytes below the return slot
rsp0 − 128 (`Decode.low_stack_split`).
-/

open Machine Runtime Prysm.SingleAttestation.Code
variable [Host]

namespace Prysm.SingleAttestation

omit [Host] in
/-- The `Sd + 224` bytes below the return slot x − 128 as the AttestationData callee's frame (entry rsp y = x − 128): its
scratch (`Sd + 96`), its return slot, its argument area (3 × 8), the untouched gap (80), its Root pointer save, its saved
rbp. -/
theorem Decode.low_stack_split (x y : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (hy : y = x - 128)
    (a b c0 c1 c2 d e f : List UInt8) (ha : a.length = S + 96) (hb : b.length = 8) (h0 : c0.length = 8)
    (h1 : c1.length = 8) (h2 : c2.length = 8) (hd : d.length = 80) (he : e.length = 8) (hf : f.length = 8) :
    Eq ((a ++ (b ++ (c0 ++ (c1 ++ (c2 ++ (d ++ (e ++ f))))))).At (x - 128 - BitVec.ofNat 64 (S + 224)))
      = Eq (a.At (y - 224 - BitVec.ofNat 64 S)) ⋆ Eq (b.At (y - 128)) ⋆ Eq (c0.At (y - 120)) ⋆ Eq (c1.At (y - 112))
        ⋆ Eq (c2.At (y - 104)) ⋆ Eq (d.At (y - 96)) ⋆ Eq (e.At (y - 16)) ⋆ Eq (f.At (y - 8)) := by
  have e1 : x - 128 - BitVec.ofNat 64 (S + 224) = y - 224 - BitVec.ofNat 64 S := by
    subst hy
    have : BitVec.ofNat 64 (S + 224) = BitVec.ofNat 64 S + 224 := by apply BitVec.eq_of_toNat_eq; simp
    rw [this]; bv_omega
  -- The address equations below go through `toNat` and `omega`. `bv_omega` reads every hypothesis of the context; with
  -- `e1` or another address equation in the context, it stops with a `whnf` heartbeat timeout or does not end.
  have q2 : y - 120 = y - 128 + BitVec.ofNat 64 b.length := by rw [hb]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q3 : y - 112 = y - 120 + BitVec.ofNat 64 c0.length := by rw [h0]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q4 : y - 104 = y - 112 + BitVec.ofNat 64 c1.length := by rw [h1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q5 : y - 96 = y - 104 + BitVec.ofNat 64 c2.length := by rw [h2]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q6 : y - 16 = y - 96 + BitVec.ofNat 64 d.length := by rw [hd]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q7 : y - 8 = y - 16 + BitVec.ofNat 64 e.length := by rw [he]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q1 : y - 128 = y - 224 - BitVec.ofNat 64 S + BitVec.ofNat 64 a.length := by
    rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [e1, at_app a _ q1 (by simp [ha, hb, h0, h1, h2, hd, he, hf]; omega),
    at_app b _ q2 (by simp [hb, h0, h1, h2, hd, he, hf]),
    at_app c0 _ q3 (by simp [h0, h1, h2, hd, he, hf]),
    at_app c1 _ q4 (by simp [h1, h2, hd, he, hf]),
    at_app c2 _ q5 (by simp [h2, hd, he, hf]),
    at_app d _ q6 (by simp [hd, he, hf]),
    at_app e _ q7 (by simp [he, hf])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- A fresh 96-byte AttestationData object as the receiver chunks of `Prysm.AttestationData.Decode.accept`. -/
theorem Decode.fresh_object96 (p : BitVec 64) :
    Eq ((List.replicate 96 (0 : UInt8)).At p) = Eq ((List.replicate 8 0).At p) ⋆ Eq ((List.replicate 8 0).At (p + 8))
      ⋆ Eq ((List.replicate 8 0).At (p + 16)) ⋆ Eq ((List.replicate 8 0).At (p + 24))
      ⋆ Eq ((List.replicate 8 0).At (p + 32)) ⋆ Eq ((List.replicate 8 0).At (p + 40))
      ⋆ Eq ((List.replicate 8 0).At (p + 48)) ⋆ Eq ((List.replicate 8 0).At (p + 56))
      ⋆ Eq ((List.replicate 32 0).At (p + 64)) := by
  rw [show List.replicate 96 (0 : UInt8) = List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0 ++ (List.replicate 8 0
    ++ (List.replicate 8 0 ++ List.replicate 32 0))))))) by rfl]
  rw [at_app _ _ (b := p + 8) (by simp) (by simp), at_app _ _ (b := p + 16) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 24) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 32) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 40) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 48) (by simp; bv_omega) (by simp),
    at_app _ _ (b := p + 56) (by simp; bv_omega) (by simp), at_app _ _ (b := p + 64) (by simp; bv_omega) (by simp)]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- A list as a prefix of length `n` and the rest. -/
theorem Decode.bytes_split (l : List UInt8) (n : Nat) (h : n ≤ l.length) :
    ∃ a r : List UInt8, a.length = n ∧ r.length = l.length - n ∧ l = a ++ r :=
  ⟨l.take n, l.drop n, by simp [h], by simp, (List.take_append_drop n l).symm⟩

omit [Host] in
/-- The 24 bytes at x − 120 as three 8-byte words. -/
theorem Decode.split_three_words (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8)
    (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 120)) = Eq (a.At (x - 120)) ⋆ Eq (b.At (x - 112)) ⋆ Eq (c.At (x - 104)) := by
  have q1 : x - 112 = x - 120 + BitVec.ofNat 64 a.length := by
    rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q2 : x - 104 = x - 112 + BitVec.ofNat 64 b.length := by
    rw [hb]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  rw [at_app a _ q1 (by simp [ha, hb, hc]), at_app b _ q2 (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- The 16 bytes at x − 96 as two 8-byte words. -/
theorem Decode.split_two_words (x : BitVec 64) (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 8) :
    Eq ((a ++ b).At (x - 96)) = Eq (a.At (x - 96)) ⋆ Eq (b.At (x - 88)) := by
  have q1 : x - 88 = x - 96 + BitVec.ofNat 64 a.length := by
    rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  rw [at_app a _ q1 (by simp [ha, hb])]

omit [Host] in
theorem Decode.data_guard (x : BitVec 64) (g : Nat) (h : g + 352 < x.toNat) : g + 224 < (x - 128).toNat := by bv_omega

/-- Data segment: from `L_167` (directive 85) to `L_234` (directive 136): a new AttestationData object
(`NewobjectContract`), the `Data` pointer, and the AttestationData decoder through `Prysm.AttestationData.Decode.accept`. -/
theorem Decode.data (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kA : Nat) (hkA : Prysm.AttestationData.Code.unmarshalSSZ.IsInfixAt Host.prog kA) (hfA : LabelsFresh Prysm.AttestationData.Code.unmarshalSSZ kA)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kI : Nat) (hkI : Prysm.CommitteeIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kI) (hfI : LabelsFresh Prysm.CommitteeIndex.Code.unmarshalSSZ kI)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.unmarshalSSZ.IsInfixAt Host.prog kC) (hfC : LabelsFresh Prysm.Checkpoint.Code.unmarshalSSZ kC)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (rsp0 r140 guard : UInt64) (rcv bf cap : BitVec 64)
    (ds di root se sroot te troot : List UInt8) (hds : ds.length = 8) (hdi : di.length = 8)
    (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8)
    (htroot : troot.length = 32)
    (q0 q1 q2 q3 q4 rslot lo aD : List UInt8)
    (hq0 : q0.length = 8) (hq1 : q1.length = 8) (hq2 : q2.length = 8) (hq3 : q3.length = 8) (hq4 : q4.length = 8)
    (hrs : rslot.length = 8) (haD : aD.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd8 : 8 ≤ Sd) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 224)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 336 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp0.toBitVec + 32))
      ⋆ Eq (q0.At (rsp0.toBitVec - 120)) ⋆ Eq (q1.At (rsp0.toBitVec - 112)) ⋆ Eq (q2.At (rsp0.toBitVec - 104))
      ⋆ Eq (q3.At (rsp0.toBitVec - 96)) ⋆ Eq (q4.At (rsp0.toBitVec - 88))
      ⋆ Eq (rslot.At (rsp0.toBitVec - 128)) ⋆ Eq (lo.At (rsp0.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (aD.At (rcv + 24))
      ⋆ Eq (ds.At (bf + 16)) ⋆ Eq (di.At (bf + 24)) ⋆ Eq (root.At (bf + 32)) ⋆ Eq (se.At (bf + 64))
      ⋆ Eq (sroot.At (bf + 72)) ⋆ Eq (te.At (bf + 104)) ⋆ Eq (troot.At (bf + 112))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 352 < rsp0.toNat)
    (hno : NewobjectContract Heap ElfData.PrysmTarget.typeAttestationData_addr 96 (Sd + 224))
    (hmsD : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 Sd) (hmmD : MemmoveContract Sd)
    (hmsD' : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (Sd + 96)) (hmmD' : MemmoveContract (Sd + 96))
    (hnoD : NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (Sd + 96)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 136) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := rsp0.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 } ∧ st.data.regs.r14 = r140 ∧
        ∃ (pd p ps pt p1 p2 : BitVec 64) (spA spB lo' : List UInt8), spA.length = 24 ∧ spB.length = 16
          ∧ lo'.length = Sd + 224 ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 cap.toInt).At (rsp0.toBitVec + 32))
          ⋆ Eq (spA.At (rsp0.toBitVec - 120)) ⋆ Eq (spB.At (rsp0.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 107)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Heap (avail - 336)
          ⋆ Eq ((Int.toBytes 8 pd.toInt).At (rcv + 24))
          ⋆ Eq (ds.At (bf + 16)) ⋆ Eq (di.At (bf + 24)) ⋆ Eq (root.At (bf + 32)) ⋆ Eq (se.At (bf + 64))
          ⋆ Eq (sroot.At (bf + 72)) ⋆ Eq (te.At (bf + 104)) ⋆ Eq (troot.At (bf + 112))
          ⋆ Eq ((List.replicate 8 0).At pd) ⋆ Eq (ds.At (pd + 8))
          ⋆ Eq (di.At (pd + 16)) ⋆ Eq ((Int.toBytes 8 p.toInt).At (pd + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pd + 32)) ⋆ Eq ((Int.toBytes 8 32).At (pd + 40))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (pd + 48)) ⋆ Eq ((Int.toBytes 8 pt.toInt).At (pd + 56))
          ⋆ Eq ((List.replicate 32 0).At (pd + 64))
          ⋆ Eq (root.At p)
          ⋆ Eq ((List.replicate 8 0).At ps) ⋆ Eq (se.At (ps + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16)) ⋆ Eq ((Int.toBytes 8 32).At (ps + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 32)) ⋆ Eq ((List.replicate 32 0).At (ps + 40)) ⋆ Eq (sroot.At p1)
          ⋆ Eq ((List.replicate 8 0).At pt) ⋆ Eq (te.At (pt + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16)) ⋆ Eq ((Int.toBytes 8 32).At (pt + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 32)) ⋆ Eq ((List.replicate 32 0).At (pt + 40)) ⋆ Eq (troot.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 85)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  have := rsp0.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  -- 85–87: the AttestationData object (`newobject`)
  step_directive hk unmarshalSSZ 85
  step_directive hk unmarshalSSZ 86
  step_directive hk unmarshalSSZ 87
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ rslot _ _ (Decode.call_return_slot _) (by ecancel) (by exact hrs)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  rw [Decode.call_return_slot] at *
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 87 + 1)) avail lo q0 _ rfl (by omega) hlo hq0
    (by dsimp only; rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrsp2, hr142, hrbp2, stk2, sp2, hstk2, hsp2, Hm2⟩
  dsimp only at hpc2 hrsp2 hr142 hrbp2 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrsp2 hr142 hrbp2 Hm2
  rw [Decode.return_rsp] at hrsp2
  subst hrsp2 hr142 hrbp2
  rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by bv_omega, Decode.fresh_object96] at Hm2
  -- 88–99: writeBarrier = 0, the receiver, the Data pointer
  step_directive hk unmarshalSSZ 88
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  unfold_step
  step_directive hk unmarshalSSZ 89
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  step_directive hk unmarshalSSZ 90
  apply load_step_at _ _ (rsp0.toBitVec + 8) _ _ (Int.toBytes 8 rcv.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 91
  label_address hk hf unmarshalSSZ 98
  step_directive hk unmarshalSSZ 98
  step_directive hk unmarshalSSZ 99
  apply store_step_at _ _ (rcv + 24) _ _ _ aD _ _ (by segment_addr) (by ecancel) (by exact haD)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  unfold_step
  -- 100–106: the arguments buf[16:144] (rbx, rcx = 128, rdi = cap − 16), the call
  step_directive hk unmarshalSSZ 100
  apply load_step_at _ _ (rsp0.toBitVec + 16) _ _ (Int.toBytes 8 bf.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 101
  step_directive hk unmarshalSSZ 102
  apply load_step_at _ _ (rsp0.toBitVec + 32) _ _ (Int.toBytes 8 cap.toInt) _ _ (by segment_addr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  try simp only [ofInt_ofBytes_toBytes64]
  step_directive hk unmarshalSSZ 103
  step_directive hk unmarshalSSZ 104
  step_directive hk unmarshalSSZ 105
  step_directive hk unmarshalSSZ 106
  apply store_step_at _ _ (rsp0.toBitVec - 128) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 87 + 1)).toBitVec.toInt) _ _
    (Decode.call_return_slot _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  unfold_step
  rw [Decode.call_return_slot] at *
  rw [show label "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ"
    = Host.addrOf (kA + 0) from label_at hkA hfA (j := 0) (by rfl) (by intro i hi; omega)]
  -- our scratch as the callee's frame
  obtain ⟨fa, r1, hfa, hr1, rfl⟩ := Decode.bytes_split stk2 (Sd + 96) (by omega)
  obtain ⟨fb, r2, hfb, hr2, rfl⟩ := Decode.bytes_split r1 8 (by omega)
  obtain ⟨fc0, r3, hfc0, hr3, rfl⟩ := Decode.bytes_split r2 8 (by omega)
  obtain ⟨fc1, r4, hfc1, hr4, rfl⟩ := Decode.bytes_split r3 8 (by omega)
  obtain ⟨fc2, r5, hfc2, hr5, rfl⟩ := Decode.bytes_split r4 8 (by omega)
  obtain ⟨fd, r6, hfd, hr6, rfl⟩ := Decode.bytes_split r5 80 (by omega)
  obtain ⟨fe, ff, hfe, hff, rfl⟩ := Decode.bytes_split r6 8 (by omega)
  simp only [List.length_append] at hstk2 hr1 hr2 hr3 hr4 hr5 hr6 hff
  rw [Decode.low_stack_split rsp0.toBitVec (rsp0.toBitVec - 128) Sd hSd rfl fa fb fc0 fc1 fc2 fd fe ff hfa hfb hfc0 hfc1 hfc2
    hfd hfe (by omega)] at H4
  refine eventually_trans _ _ _ _ (Prysm.AttestationData.Decode.accept kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE
    ds di root se sroot te troot hds hdi hroot hse hsroot hte htroot _
    (UInt64.ofBitVec (Host.addrOf (k + 106 + 1)).toBitVec) guard
    ff sp2 q1 q3 fc0 fc1 fc2 fe fb fa
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0)
    (by omega) hsp2 hq1 hq3 hfc0 hfc1 hfc2 hfe hfb (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) _ Sd hSd8 hSd hfa Heap (avail - 96)
    (by
      dsimp only
      rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by segment_addr,
        show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by segment_addr,
        show rsp0.toBitVec - 128 + 32 = rsp0.toBitVec - 96 by segment_addr,
        show 16 + bf = bf + 16 by segment_addr,
        show bf + 16 + 8 = bf + 24 by segment_addr,
        show bf + 16 + 16 = bf + 32 by segment_addr,
        show bf + 16 + 48 = bf + 64 by segment_addr,
        show bf + 16 + 56 = bf + 72 by segment_addr,
        show bf + 16 + 88 = bf + 104 by segment_addr,
        show bf + 16 + 96 = bf + 112 by segment_addr]
      ecancel)
    (by
      dsimp only
      exact Decode.data_guard _ _ hguard)
    (by rfl) (by omega) hmsD hmmD hmsD' hmmD' hnoD) ?_
  rintro ⟨d5, pc5⟩ ⟨hpc5, hrax5, hrbx5, hrsp5, hrbp5, hr145, p, ps, pt, p1, p2, w, lo5, hw, hlo5, Hm5⟩
  dsimp only at hpc5 hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  simp only [Int64.ofBitVec_toBitVec] at hpc5 Hm5
  subst hpc5
  obtain ⟨⟨rax5, rbx5, rcx5, rdx5, rsi5, rdi5, rsp5, rbp5, r85, r95, r105, r115, r125, r135, r145, r155⟩,
    zmms5, flags5, mem5⟩ := d5
  simp only at hrax5 hrbx5 hrsp5 hrbp5 hr145 Hm5
  rw [Decode.return_rsp] at hrsp5
  subst hrax5 hrbx5 hrsp5 hrbp5 hr145
  rw [show rsp0.toBitVec - 128 + 8 = rsp0.toBitVec - 120 by segment_addr,
    show rsp0.toBitVec - 128 + 16 = rsp0.toBitVec - 112 by segment_addr,
    show rsp0.toBitVec - 128 + 32 = rsp0.toBitVec - 96 by segment_addr,
    show 16 + bf = bf + 16 by segment_addr,
    show bf + 16 + 8 = bf + 24 by segment_addr,
    show bf + 16 + 16 = bf + 32 by segment_addr,
    show bf + 16 + 48 = bf + 64 by segment_addr,
    show bf + 16 + 56 = bf + 72 by segment_addr,
    show bf + 16 + 88 = bf + 104 by segment_addr,
    show bf + 16 + 96 = bf + 112 by segment_addr] at Hm5
  -- 107–108: err = nil, `je L_234` taken
  step_directive hk unmarshalSSZ 107
  try intro _
  step_directive hk unmarshalSSZ 108
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  label_address hk hf unmarshalSSZ 136
  apply Eventually.done
  rw [show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by segment_addr, show k + 106 + 1 = k + 107 from rfl] at Hm5
  -- the callee's saved-rbp word and the callee's capacity spill: names, so that `ecancel` matches them structurally
  have hvb := Int.toBytes_length 8 (BitVec.toInt (rsp0.toBitVec - 8#64))
  generalize Int.toBytes 8 (BitVec.toInt (rsp0.toBitVec - 8#64)) = vb at Hm5 hvb
  have hv4 := Int.toBytes_length 8 (BitVec.toInt (-16 + cap))
  generalize Int.toBytes 8 (BitVec.toInt (-16 + cap)) = v4 at Hm5 hv4
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rax2.toBitVec, p, ps, pt, p1, p2,
    Int.toBytes 8 rax2.toBitVec.toInt ++ (Int.toBytes 8 (bf + 16).toInt ++ q2), v4 ++ q4,
    lo5 ++ (Int.toBytes 8 (Host.addrOf (kA + 193)).toBitVec.toInt ++ (Int.toBytes 8 pt.toInt
      ++ (Int.toBytes 8 (bf + 104).toInt ++ (w ++ (fd ++ (Int.toBytes 8 p.toInt
      ++ vb)))))),
    by simp [hq2, Int.toBytes_length], by simp [hq4, hv4],
    by simp [hlo5, hw, hfd, hvb, Int.toBytes_length], ?_⟩
  rw [Decode.split_three_words _ _ _ _ (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hq2,
    Decode.split_two_words _ _ _ hv4 hq4,
    Decode.low_stack_split rsp0.toBitVec (rsp0.toBitVec - 128) Sd hSd rfl _ _ _ _ _ _ _ _ hlo5 (Int.toBytes_length 8 _)
      (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hw hfd (Int.toBytes_length 8 _) hvb,
    show rsp0.toBitVec - 128 - 8 = rsp0.toBitVec - 136 by segment_addr,
    show avail - 336 = avail - 96 - 240 by omega]
  dsimp only
  ecancel

end Prysm.SingleAttestation
