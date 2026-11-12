import Prysm.Checkpoint.WitnessDecodeAccept
import Prysm.Checkpoint.DecodeSpec

/-!
# Witness of `Decode.accept_spec` on a concrete input array

Same Host and memory as `Prysm.Checkpoint.WitnessDecodeAccept` (decoder, Epoch callee, bump makeslice,
RtCopy). The input array is `SszValue.encode g0` (the consensus-specs encoding of `g0`),
with the EthLib premise `deserialize desc (SszValue.encode g0) = .ok g0.toValue`
discharged by `SszValue.roundtrip`; the memory premise `Pm` holds for every `g` with
`SszValue.encode g0 = SszValue.encode g` (such a `g` is `g0`: `sszValue_toValue_inj`). The examples fix
`g0` to the three epoch × root values of `WitCpA` (input arrays `SszValue.encode g0` of
closed `g0`; a byte-literal equality is not stated: `decide` does not reduce
`uintBytes`/`Vector.ofFn`, and `native_decide` is not allowed).
-/

open Machine Runtime TestTarget Machine.Witness Prysm.Checkpoint.Code EthLib.Serialization.Ssz

namespace Prysm.Checkpoint.Witness.DecodeAccept

theorem sszValue_toValue_inj {g h : SszValue} (e : g.toValue = h.toValue) : g = h := by
  obtain ⟨a, r⟩ := g
  obtain ⟨b, q⟩ := h
  simp only [SszValue.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq, and_true] at e
  obtain ⟨e1, e2⟩ := e
  have : a = b := UInt64.toNat_inj.mp e1
  have : r = q := Vector.toArray_inj.mp e2
  subst_vars; rfl

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Decode.accept_spec`** on the input array `SszValue.encode g0`. -/
theorem runs_spec (g0 : SszValue) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ g : SszValue, g.toValue = g0.toValue ∧ SszValue.encode g0 = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 (uintBytes 8 g0.epoch.toNat).toList g0.root.toList zmms flags, Host.addrOf 9⟩ := by
  obtain ⟨g, h1, h2, h3⟩ := Decode.accept_spec 9 hk9 hf9 117 hk117 hf117 (SszValue.encode g0) g0.toValue (SszValue.roundtrip g0)
    (cs0 (uintBytes 8 g0.epoch.toNat).toList g0.root.toList zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 32)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl R0 8 (Nat.le_refl _) (by decide) (z 8) rfl
    bumpHeap 32
    (fun g hg => by
      have hgg : g = g0 := sszValue_toValue_inj (by
        have h := SszValue.roundtrip g
        rw [← hg, SszValue.roundtrip g0] at h
        exact (Except.ok.inj h).symm)
      subst hgg
      generalize hE : (uintBytes 8 g.epoch.toNat).toList = e8
      generalize hR : g.root.toList = root
      have he8 : e8.length = 8 := by rw [← hE, Array.length_toList, Spec.uintBytes_size]
      have hroot : root.length = 32 := by rw [← hR]; simp
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      wit_split [he8, hroot]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 32).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by rw [SszValue.enc_size]; rfl) (by omega) (bump_makeslice1 180 hk180 hf180 _)
    (rt_memmove 186 hk186 hf186 8)
  exact ⟨g, h1, h2, eventually_mono h3 (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)⟩

def g0rep : SszValue := ⟨0x0123456789abcdef, Vector.ofFn (fun i => UInt8.ofNat i.val)⟩

example (z' : RegZmms) (f : StatusFlags) := runs_spec ⟨0, Vector.replicate 32 0⟩ z' f
example (z' : RegZmms) (f : StatusFlags) := runs_spec g0rep z' f
example (z' : RegZmms) (f : StatusFlags) := runs_spec ⟨0xffffffffffffffff, Vector.replicate 32 0xff⟩ z' f

end Prysm.Checkpoint.Witness.DecodeAccept
