import Fk.Step
import Fk.Labels
import Fk.Bytes
import E2e.Code

/-!
# `(*primitives.Epoch).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

    func (e *Epoch) UnmarshalSSZ(buf []byte) error {
        if len(buf) != e.SizeSSZ() { return fmt.Errorf("expected buffer of length %d received %d", ...) }
        *e = Epoch(UnmarshalUint64(buf)); return nil }

Hand-written Prysm method (`consensus-types/primitives/epoch.go:126`), not
generated. Proved here from the included Go 1.26.10 code `E2e.Code.EpUnmarshal`
(directive indices of `prysm/go1.26.10/e2e/link/norm/…Epoch.UnmarshalSSZ.S`):
0–1 labels, 2–3 stack guard, 4–7 prologue (`push %rbp`, `sub $0x48`, spill of
rbx at rsp + 16), 9–10 `cmp $0x8,%rcx; je L_bb`, 43 `L_bb`, 44 `mov (%rbx),%rcx`,
46 `mov %rcx,(%rax)`, 47–48 `xor`, 49–51 epilogue.

Footprint of the accept path: the return slot, the saved rbp at rsp − 8, the
rbx spill slot at rsp + 16, the guard word, 8 input bytes, 8 receiver bytes.
The rest of the frame (rsp − 0x50 … rsp − 9) and the other spill slots are not
touched on this path; they stay in the frame `R`.
-/

open Fk E2e.Code
variable [Host]

namespace E2e

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ep_unmarshal_accept_main (k : Nat) (hk : EpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh EpUnmarshal k)
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
  kat hk EpUnmarshal 0
  kat hk EpUnmarshal 1
  kat hk EpUnmarshal 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk EpUnmarshal 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk EpUnmarshal 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk EpUnmarshal 5
  kat hk EpUnmarshal 6
  kat hk EpUnmarshal 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk EpUnmarshal 8
  kat hk EpUnmarshal 9
  kat hk EpUnmarshal 10
  split
  case isFalse h => exact absurd h (by decide)
  simp only [Effects.All]
  klabel hk hf EpUnmarshal 43
  kat hk EpUnmarshal 43
  kat hk EpUnmarshal 44
  apply load_step _ _ _ _ e8 _ _ (by ecancel) (by exact he8)
  kunfold
  kat hk EpUnmarshal 45
  kat hk EpUnmarshal 46
  apply store_step_at _ _ rax.toBitVec _ _ _ c0 _ _ (by bv_omega) (by ecancel) (by exact hc0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl e8 he8] at H3
  kunfold
  kat hk EpUnmarshal 47
  intro _
  kat hk EpUnmarshal 48
  intro _
  kat hk EpUnmarshal 49
  kat hk EpUnmarshal 50
  rw [show (72 : BitVec 64) + (rsp.toBitVec - 8#64 - 72) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk EpUnmarshal 51
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

/-- **Function specification of `(*primitives.Epoch).UnmarshalSSZ`, accept path**
(`len(buf) = 8`), in the shape of `Fk.ScUAccC`: a hypothesis-shaped statement
about the code at the Epoch label, for every machine state, return address and
frame `F`. `ep_uacc_holds` proves it from the machine code; the Checkpoint
decoder uses the callee only through this specification (no contract). -/
def EpUAccC : Prop :=
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
      ⟨st, label epLabel⟩

/-- The Epoch machine code satisfies its specification (no assumption beyond
the code's place in the host and its label freshness). -/
theorem ep_uacc_holds (k : Nat) (hk : EpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh EpUnmarshal k) : EpUAccC := by
  intro st ret e8 fp s2 c0 guard F he8 hfp h2 hc0 hlen hguard hm
  rw [show label epLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  exact ep_unmarshal_accept_main k hk hf e8 he8 st (UInt64.ofBitVec ret.toBitVec) guard fp s2 c0 hfp h2 hc0 F hm
    hguard hlen

end E2e
