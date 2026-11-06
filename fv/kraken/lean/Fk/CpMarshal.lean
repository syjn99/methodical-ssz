import Fk.CpSpec
import Fk.FvMarshal

/-!
# Prysm Checkpoint.MarshalSSZTo, fast path, on Kraken main

With `cap(dst) ≥ len(dst) + 40` and `len(c.Root) = 32`, MarshalSSZTo writes
Epoch (8 LE bytes) at `dst[len:]`, copies Root with `runtime.memmove`
(contract `MemmoveC`) at `dst[len+8:]`, and returns `(dst[:len+40], nil)`;
`dst[:len]` (`pre`) is kept. `cp_marshal_reject_main`: `len(c.Root) ≠ 32` →
`ssz.ErrBytesLength` (after Epoch is written).
Premises the Go caller provides: receiver, Root bytes, `dst` and stack chunks
separated; the stack guard; `cap < 2^63` (Go slice bound).
-/

open Fk Fk.Code
variable [Host]

theorem cpm_addr (x y : BitVec 64) : y + 8 + x * 1#64 + -8 = x + y := by
  rw [BitVec.add_comm y 8]; exact add8_neg8 x y

theorem cpm_dst (x y : BitVec 64) : x + (y + 8) * 1#64 = x + y + 8 := by
  rw [BitVec.mul_one, BitVec.add_assoc]

theorem cpm_slot (x : BitVec 64) : x - 8#64 - 104 - 8#64 = x - 120 := by bv_omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem cp_marshal_main (k : Nat) (hk : PrysmCheckpointMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointMarshalSSZTo k)
    (e8 root pre d0 d1 : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (hd0 : d0.length = 8) (hd1 : d1.length = 32) (p : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l32 l40 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ Eq (root.At p) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk PrysmCheckpointMarshalSSZTo 0
  kat hk PrysmCheckpointMarshalSSZTo 1
  kat hk PrysmCheckpointMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmCheckpointMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 5
  kat hk PrysmCheckpointMarshalSSZTo 6
  kat hk PrysmCheckpointMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 8
  kat hk PrysmCheckpointMarshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 10
  kat hk PrysmCheckpointMarshalSSZTo 11
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointMarshalSSZTo 25
  kat hk PrysmCheckpointMarshalSSZTo 25
  kat hk PrysmCheckpointMarshalSSZTo 26
  rw [cpm_addr]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 27
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 p.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 28
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 32) _ _ (by kaddr) (by ecancel) (by rfl)
  simp only [show Int.ofBytes (Int.toBytes 8 32) = 32 by decide]
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 29
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk PrysmCheckpointMarshalSSZTo 30
  kat hk PrysmCheckpointMarshalSSZTo 31
  kat hk PrysmCheckpointMarshalSSZTo 32
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointMarshalSSZTo 46
  kat hk PrysmCheckpointMarshalSSZTo 46
  kat hk PrysmCheckpointMarshalSSZTo 47
  apply store_step_at _ _ (rsp.toBitVec - 16) _ _ _ l16 _ _ (f96 _) (by ecancel) (by exact hl16)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 48
  apply store_step_at _ _ (rsp.toBitVec - 32) _ _ _ l32 _ _ (f80 _) (by ecancel) (by exact hl32)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 49
  apply store_step_at _ _ (rsp.toBitVec - 40) _ _ _ l40 _ _ (f72 _) (by ecancel) (by exact hl40)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 50
  kat hk PrysmCheckpointMarshalSSZTo 51
  kat hk PrysmCheckpointMarshalSSZTo 52
  kat hk PrysmCheckpointMarshalSSZTo 53
  apply store_step_at _ _ (rsp.toBitVec - 120) _ _ _ rslot _ _ (slot120 _) (by ecancel) (by exact hrs)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [slot120] at *
  rw [cpm_dst] at *
  refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (k + 53 + 1)) root d1 scratch _
    (by rw [hroot]; rfl) (by rw [hroot, hd1]) hsc (by dsimp only; ecancel)) ?_
  rintro ⟨e1, pc1⟩ ⟨hpc1, hrsp1, _hmr141, _hmrbp1, stk1, hstk1, Hm1⟩
  dsimp only at hpc1 hrsp1 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := e1
  simp only at hrsp1 _hmr141 Hm1
  subst hrsp1 _hmr141
  kat hk PrysmCheckpointMarshalSSZTo 54
  rw [g120, h96]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 55
  rw [g120, h80]
  apply load_step _ _ _ _ (Int.toBytes 8 (rcx.toBitVec + 8 + 32).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 56
  rw [g120, h72]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 57
  intro _
  kat hk PrysmCheckpointMarshalSSZTo 58
  intro _
  kat hk PrysmCheckpointMarshalSSZTo 59
  kat hk PrysmCheckpointMarshalSSZTo 60
  rw [k104]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 61
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq (e8.At (rbx.toBitVec + rcx.toBitVec))
      ⋆ Eq (root.At (rbx.toBitVec + rcx.toBitVec + 8)) ⋆ Eq (e8.At rax.toBitVec) ⋆ Eq (root.At p) ⋆ R) (by ecancel)
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (simp [BitVec.toNat_add]; omega)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)
    | (show (rcx.toBitVec + 8 + 32).toNat = _; simp [BitVec.toNat_add]; omega)

open Fv1 EthLib.Serialization.Ssz in
/-- **Marshal fast path against EthLib.** With the receiver holding the Go
layout of `g`, MarshalSSZTo writes at `dst[len:]` the bytes of `cpEncode g`,
the EthLib serialization of `g.toValue`. -/
theorem cp_marshal_spec_k (k : Nat) (hk : PrysmCheckpointMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointMarshalSSZTo k) (g : CheckpointG)
    (pre d0 d1 : List UInt8) (hd0 : d0.length = 8) (hd1 : d1.length = 32) (p : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l32 l40 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    serialize cpDesc g.toValue = .ok (cpEncode g) ∧
    (cpEncode g).toList = (uintBytes 8 g.epoch.toNat).toList ++ g.root.toList ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rax.toBitVec) ⋆ Eq (g.root.toList.At p)
          ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨cp_serialize g, by simp [cpEncode]; rfl,
    cp_marshal_main k hk hf _ _ pre d0 d1 (by simp [Fv.uintBytes_size]) (by simp) hd0 hd1 p s ra guard hpre
      fp s2 l16 l32 l40 rslot hfp h2 hl16 hl32 hl40 hrs R S scratch hsc h_mem hguard hsp hcap hcap63 hmm⟩

open Fv1 EthLib.Serialization.Ssz in
/-- Round trip: EthLib decodes `cpEncode g` to `g.toValue`, and the
abstraction is injective (with `cp_marshal_spec_k`, `cp_unmarshal_accept_spec_k`). -/
theorem cp_roundtrip (g : CheckpointG) :
    deserialize cpDesc (cpEncode g) = .ok g.toValue ∧ ∀ g', g'.toValue = g.toValue → g' = g :=
  ⟨deserialize_enc cpDesc_wellFormed cp_serialize cp_toValue_fits g,
   fun g' h => cp_toValue_injective g' g h⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `len(c.Root) ≠ 32`: after writing Epoch, returns `(nil, ssz.ErrBytesLength)`. -/
theorem cp_marshal_reject_main (k : Nat) (hk : PrysmCheckpointMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointMarshalSSZTo k)
    (e8 root pre d0 d1 : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (hd0 : d0.length = 8) (hd1 : d1.length = 32) (p : BitVec 64) (n : BitVec 64) (hn : n ≠ 32)
    (e0 e1 : UInt64)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 l16 l32 l40 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl32 : l32.length = 8)
    (hl40 : l40.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 n.toInt).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (root.At p)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R ⋆ fun _ => True)
          st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk PrysmCheckpointMarshalSSZTo 0
  kat hk PrysmCheckpointMarshalSSZTo 1
  kat hk PrysmCheckpointMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmCheckpointMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 5
  kat hk PrysmCheckpointMarshalSSZTo 6
  kat hk PrysmCheckpointMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 8
  kat hk PrysmCheckpointMarshalSSZTo 9
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 10
  kat hk PrysmCheckpointMarshalSSZTo 11
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointMarshalSSZTo 25
  kat hk PrysmCheckpointMarshalSSZTo 25
  kat hk PrysmCheckpointMarshalSSZTo 26
  rw [cpm_addr]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 27
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 p.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 28
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 n.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 29
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hn; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointMarshalSSZTo 62
  kat hk PrysmCheckpointMarshalSSZTo 62
  kat hk PrysmCheckpointMarshalSSZTo 63
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 64
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 65
  intro _
  kat hk PrysmCheckpointMarshalSSZTo 66
  intro _
  kat hk PrysmCheckpointMarshalSSZTo 67
  kat hk PrysmCheckpointMarshalSSZTo 68
  kat hk PrysmCheckpointMarshalSSZTo 69
  rw [show (104 : BitVec 64) + (rsp.toBitVec - 8#64 - 104) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointMarshalSSZTo 70
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | exact sep_true (P := Eq (pre.At rbx.toBitVec) ⋆ Eq (e8.At (rbx.toBitVec + rcx.toBitVec)) ⋆ R) (by ecancel)
