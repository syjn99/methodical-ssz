import E2e.Epoch
import Machine.WitnessHost
import Runtime.CopyModel

/-!
# Witness of `ep_unmarshal_accept_main` and `ep_uacc_holds`

Host: the real Go 1.26.10 `(*primitives.Epoch).UnmarshalSSZ` alone, at index 0
(directive `i` at `0x10000 + i`). Memory: one 56-byte block at `0x10000`:
guard word (r14 + 16, r14 = 0xfff0), the 8 input bytes (rbx = 0x10008), the
8-byte receiver `*Epoch` (rax = 0x10010), the saved-rbp slot (rsp − 8), the
return slot (rsp = 0x10020, return address 0), the unused spill slot rsp + 8
(the frame `R`, exactly these bytes) and the rbx spill slot rsp + 16. For every
8-byte input this state meets every premise (`ep_wit_mem`), and the function
returns nil with the receiver = the input (`ep_accept_runs`); three epoch values
below (0, a representative value, 2^64 − 1).
-/

open Machine Runtime TestTarget Machine.Witness E2e E2e.Code

namespace E2e.WitEp

set_option maxRecDepth 100000

def P : Program := EpUnmarshal

theorem P_len : P.length = 63 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : EpUnmarshal.IsInfixAt Host.prog 0 := ⟨[], by simp [Host.prog, mkHost, P]⟩

theorem hf0 : LabelsFresh EpUnmarshal 0 := fun i hi => absurd hi (Nat.not_lt_zero _)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

/-- guard · input · receiver (old value `old`) · saved rbp · return slot · spill rsp+8 · spill rsp+16. -/
def block (e8 old : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0 : UInt64).toBitVec.toInt ++ (e8 ++ (old ++ (z 8
    ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt ++ (z 8 ++ z 8)))))

def mem (e8 old : List UInt8) : DataMem := (block e8 old).At (0x10000 : BitVec 64)

def cs0 (e8 old : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10010, 0x10008, 8, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem e8 old⟩

/-- The frame `R` of the witness: exactly the unused spill slot. -/
def R0 : DataMem → Prop := Eq ((z 8).At (0x10028 : BitVec 64))

set_option maxHeartbeats 4000000 in
theorem ep_wit_mem (e8 old : List UInt8) (he8 : e8.length = 8) (hold : old.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    let s := cs0 e8 old zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (old.At s.regs.rax.toBitVec) ⋆ R0 := by
  intro s
  have H : Eq ((block e8 old).At (0x10000 : BitVec 64)) (mem e8 old) := rfl
  wit_split [he8, hold]
  simp only [s, cs0, R0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
  simp only [Std.ExtHashMap.sep_assoc] at H ⊢
  simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
  exact H

/-- **Non-vacuity of `ep_unmarshal_accept_main`**: on the concrete host and
state, for every 8-byte input, the Epoch decoder returns nil and the receiver
holds the input bytes. -/
theorem ep_accept_runs (e8 old : List UInt8) (he8 : e8.length = 8) (hold : old.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ (Eq (e8.At (0x10010 : BitVec 64)) ⋆ fun _ => True) st.data.dmem)
      ⟨cs0 e8 old zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (ep_unmarshal_accept_main 0 hk0 hf0 e8 he8 (cs0 e8 old zmms flags) 0 0 (z 8) (z 8) old
    rfl rfl hold R0 (ep_wit_mem e8 old he8 hold zmms flags) (by simp [cs0]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, by
      have hm := h.2.2.2.2.2.2
      rw [show (cs0 e8 old zmms flags).regs.rax.toBitVec = (0x10010 : BitVec 64) from rfl] at hm
      exact sep_true (P := Eq (e8.At (0x10010 : BitVec 64))) (by ecancel)⟩)

/-- The specification `EpUAccC` holds on this host (from the machine code). This is a spec instance, not premise
satisfiability; the non-vacuity witness is the run theorem above. -/
theorem ep_spec_here : EpUAccC := ep_uacc_holds 0 hk0 hf0

/-- epoch 0, a representative value (0x0123456789abcdef), and 2^64 − 1. -/
example (z' : RegZmms) (f : StatusFlags) := ep_accept_runs (Int.toBytes 8 0) (z 8) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) := ep_accept_runs (Int.toBytes 8 0x0123456789abcdef) (z 8) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) := ep_accept_runs (Int.toBytes 8 (2 ^ 64 - 1)) (z 8) (by decide) rfl z' f

end E2e.WitEp
