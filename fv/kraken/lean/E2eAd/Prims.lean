import Fk.Step
import Fk.Labels
import Fk.Bytes
import E2eAd.Code

/-!
# `(*primitives.Slot).UnmarshalSSZ` and `(*primitives.CommitteeIndex).UnmarshalSSZ`, accept path (A2)

Hand-written Prysm methods (`consensus-types/primitives/slot.go:183`,
`committee_index.go:28`), not generated. Their Go 1.26.10 machine code is the
code of `(*primitives.Epoch).UnmarshalSSZ` with another name (Slot: identical
after the label rename; CommitteeIndex: also the reject format string differs,
`go_string._+110097`; checked by `diff` in A1). The theorems below are the text
of `E2e/Epoch.lean` with the names renamed, and they are proved again here on
the included Slot and CommitteeIndex code (`E2eAd.Code.SlUnmarshal`,
`E2eAd.Code.CiUnmarshal`): directive indices 0–1 labels, 2–3 stack guard, 4–7
prologue, 9–10 `cmp $0x8,%rcx; je L_bb`, 43 `L_bb`, 44 load, 46 store, 47–48
`xor`, 49–51 epilogue. `SlUAccC` / `CiUAccC` are the function specifications
(the form of `E2e.EpUAccC`); the AttestationData decoder uses the callees only
through them.
-/

open Fk E2eAd.Code
variable [Host]

namespace E2eAd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem sl_unmarshal_accept_main (k : Nat) (hk : SlUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh SlUnmarshal k)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 8) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk SlUnmarshal 0
  kat hk SlUnmarshal 1
  kat hk SlUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SlUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk SlUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk SlUnmarshal 5
  kat hk SlUnmarshal 6
  kat hk SlUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk SlUnmarshal 8
  kat hk SlUnmarshal 9
  kat hk SlUnmarshal 10
  split
  case isFalse h => exact absurd h (by decide)
  simp only [Effects.All]
  klabel hk hf SlUnmarshal 43
  kat hk SlUnmarshal 43
  kat hk SlUnmarshal 44
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk SlUnmarshal 45
  kat hk SlUnmarshal 46
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hk SlUnmarshal 47
  intro _
  kat hk SlUnmarshal 48
  intro _
  kat hk SlUnmarshal 49
  kat hk SlUnmarshal 50
  rw [show (72 : BitVec 64) + (rsp.toBitVec - 8#64 - 72) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk SlUnmarshal 51
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)

/-- **Function specification of `(*primitives.Slot).UnmarshalSSZ`, accept path**
(`len(buf) = 8`), in the shape of `Fk.ScUAccC`: a hypothesis-shaped statement
about the code at the Slot label, for every machine state, return address and
frame `F`. `sl_uacc_holds` proves it from the machine code; the AttestationData
decoder uses the callee only through this specification (no contract). -/
def SlUAccC : Prop :=
  ∀ (st : MachineData) (ret : Int64) (e8 fp s2 c0 : List UInt8) (guard : UInt64) (F : DataMem → Prop),
    e8.length = 8 → fp.length = 8 → s2.length = 8 → c0.length = 8 →
    st.regs.rcx = 8 → guard.toNat < st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.r14 = st.regs.r14
        ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label slLabel⟩

/-- The Slot machine code satisfies its specification (no assumption beyond
the code's place in the host and its label freshness). -/
theorem sl_uacc_holds (k : Nat) (hk : SlUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh SlUnmarshal k) : SlUAccC := by
  intro st ret e8 fp s2 c0 guard F he8 hfp h2 hc0 hlen hguard hm
  rw [show label slLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  exact sl_unmarshal_accept_main k hk hf e8 he8 st (UInt64.ofBitVec ret.toBitVec) guard fp s2 c0 hfp h2 hc0 F hm
    hguard hlen

end E2eAd

namespace E2eAd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ci_unmarshal_accept_main (k : Nat) (hk : CiUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CiUnmarshal k)
    (e8 : List UInt8) (he8 : e8.length = 8)
    (s : MachineData) (ra guard : UInt64) (fp s2 c0 : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hc0 : c0.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 8) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
  kat hk CiUnmarshal 0
  kat hk CiUnmarshal 1
  kat hk CiUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CiUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk CiUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk CiUnmarshal 5
  kat hk CiUnmarshal 6
  kat hk CiUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk CiUnmarshal 8
  kat hk CiUnmarshal 9
  kat hk CiUnmarshal 10
  split
  case isFalse h => exact absurd h (by decide)
  simp only [Effects.All]
  klabel hk hf CiUnmarshal 43
  kat hk CiUnmarshal 43
  kat hk CiUnmarshal 44
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk CiUnmarshal 45
  kat hk CiUnmarshal 46
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hk CiUnmarshal 47
  intro _
  kat hk CiUnmarshal 48
  intro _
  kat hk CiUnmarshal 49
  kat hk CiUnmarshal 50
  rw [show (72 : BitVec 64) + (rsp.toBitVec - 8#64 - 72) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk CiUnmarshal 51
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (apply UInt64.toBitVec_inj.mp; simp; bv_omega)

/-- **Function specification of `(*primitives.CommitteeIndex).UnmarshalSSZ`, accept path**
(`len(buf) = 8`), in the shape of `Fk.ScUAccC`: a hypothesis-shaped statement
about the code at the CommitteeIndex label, for every machine state, return address and
frame `F`. `ci_uacc_holds` proves it from the machine code; the AttestationData
decoder uses the callee only through this specification (no contract). -/
def CiUAccC : Prop :=
  ∀ (st : MachineData) (ret : Int64) (e8 fp s2 c0 : List UInt8) (guard : UInt64) (F : DataMem → Prop),
    e8.length = 8 → fp.length = 8 → s2.length = 8 → c0.length = 8 →
    st.regs.rcx = 8 → guard.toNat < st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.r14 = st.regs.r14
        ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label ciLabel⟩

/-- The CommitteeIndex machine code satisfies its specification (no assumption beyond
the code's place in the host and its label freshness). -/
theorem ci_uacc_holds (k : Nat) (hk : CiUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CiUnmarshal k) : CiUAccC := by
  intro st ret e8 fp s2 c0 guard F he8 hfp h2 hc0 hlen hguard hm
  rw [show label ciLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  exact ci_unmarshal_accept_main k hk hf e8 he8 st (UInt64.ofBitVec ret.toBitVec) guard fp s2 c0 hfp h2 hc0 F hm
    hguard hlen

end E2eAd
