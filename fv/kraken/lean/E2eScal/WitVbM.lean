import E2eScal.Enc2ExVb
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of `vb_e2e_marshal_g6` (ValidatorBalance encoder, fast path only; generated-style theorem)

Hand-written (the text of `E2eScal/WitE1M.lean` with the ValidatorBalance host and layout).
Host: the real Go 1.26.10 `(*v1alpha1.ValidatorBalance).MarshalSSZTo` (index 0). The function calls no
runtime function on the fast path (`Runtime.CopyModel` is imported for `eventually_mono` only). One memory block at `0x10000`: guard word (r14 = 0xfff0), the receiver at
0x10008 (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, Index 8, Balance 16), the stack window
(rsp = 0x10048: the two 16-byte halves of the stack temp at rsp − 40 and rsp − 24, saved rbp, return slot,
the receiver spill slot, the pointer spill slot) and `dst` at 0x10060: the prefix, 8 + 8 bytes of old
contents, the spare capacity. Frame `R`: the receiver spill slot (not written on the fast path) and the spare
capacity.
Two instances: empty prefix with `cap = 16`, and a 3-byte prefix with 5 spare bytes. For every Index and
Balance every premise of the kind instance `encFastKindN VbMarshal layEncVb [.u64, .u64]` holds.
-/

open Machine Runtime TestTarget Machine.Witness E2eScal Codec E2eScal.Enc2Code E2eScal.Gen6

namespace E2eScal.WitVbM

set_option maxRecDepth 100000

def P : Program := VbMarshal

theorem P_len : P.length = 72 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk0 : VbMarshal.IsInfixAt Host.prog 0 := infixAt_of [] [] (by simp [Host.prog, mkHost, P]) rfl
theorem hf0 : LabelsFresh VbMarshal 0 := fun i hi => absurd hi (Nat.not_lt_zero _)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- guard · receiver (`state`, Index, Balance) · t40 (16) · t24 (16) · fp · return slot · receiver spill ·
pointer spill · dst = prefix · d0 (8) · d1 (8) · spare. -/
def block (v0 v1 pre spare : List UInt8) : List UInt8 :=
  w 0 ++ (z 8 ++ (v0 ++ (v1 ++ (z 16 ++ (z 16 ++ (z 8 ++ (w 0 ++ (z 8 ++ (z 8 ++ (pre ++ (z 8 ++ (z 8 ++ spare))))))))))))

def mem (v0 v1 pre spare : List UInt8) : DataMem := (block v0 v1 pre spare).At (0x10000 : BitVec 64)

def cs0 (v0 v1 pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10008, 0x10060, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 16 + spare.length), 0x10048, 0,
    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem v0 v1 pre spare⟩

set_option maxHeartbeats 16000000 in
/-- Empty prefix, `cap = 16`. -/
theorem vbm_runs_empty (v0 v1 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10060
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 v0 v1 [] [] zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (vb_e2e_marshal_g6 0 hk0 hf0 (z 8) v0 v1 [] (z 8) (z 8) rfl hv0 hv1 rfl rfl
    (cs0 v0 v1 [] [] zmms flags) 0 0 rfl
    (z 8) (z 8) (z 16) (z 16) rfl rfl rfl rfl
    (Eq ((z 8).At (0x10050 : BitVec 64)))
    (by
      have H : Eq ((block v0 v1 [] []).At (0x10000 : BitVec 64)) (mem v0 v1 [] []) := rfl
      wit_split [hv0, hv1]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

set_option maxHeartbeats 16000000 in
/-- Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + 21`). -/
theorem vbm_runs_prefix (v0 v1 : List UInt8) (hv0 : v0.length = 8) (hv1 : v1.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10060
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨cs0 v0 v1 [0xaa, 0xbb, 0xcc] (z 5) zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (vb_e2e_marshal_g6 0 hk0 hf0 (z 8) v0 v1 [0xaa, 0xbb, 0xcc] (z 8) (z 8) rfl hv0 hv1 rfl rfl
    (cs0 v0 v1 [0xaa, 0xbb, 0xcc] (z 5) zmms flags) 0 0 rfl
    (z 8) (z 8) (z 16) (z 16) rfl rfl rfl rfl
    (Eq ((z 8).At (0x10050 : BitVec 64)) ⋆ Eq ((z 5).At (0x10073 : BitVec 64)))
    (by
      have H : Eq ((block v0 v1 [0xaa, 0xbb, 0xcc] (z 5)).At (0x10000 : BitVec 64))
        (mem v0 v1 [0xaa, 0xbb, 0xcc] (z 5)) := rfl
      wit_split [hv0, hv1]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons, List.length_replicate,
        show (UInt64.ofNat 3).toBitVec = 3#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  vbm_runs_empty (Int.toBytes 8 0) (Int.toBytes 8 0) (by decide) (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) :=
  vbm_runs_prefix (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 (2 ^ 64 - 1)) (by decide) (by decide) z' f

end E2eScal.WitVbM
