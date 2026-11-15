import Prysm.ValidatorIndex.EncodeFastPath
import Prysm.ValidatorIndex.Spec
import Prysm.Epoch.Size
import Runtime.CopyModel

/-!
# Encoder of `primitives.ValidatorIndex` against EthLib

- `Encode.fast_path_spec`: for a receiver that holds the 8 little-endian bytes of `x : UInt64`
  (`uintBytes 8 x`, the Go layout of a `uint64`), the encoder fast path writes at `dst[len:len+8]` exactly the bytes of
  `serialize desc (.uint x)` (`desc = .uint 8`, `Prysm/ValidatorIndex/Spec.lean`).
  The full frame accounting is `Encode.fast_path`; this theorem states the output
  (`⋆ True` remainder of that conclusion).
-/

open Machine Runtime Prysm.ValidatorIndex.Code EthLib.Serialization.Ssz

namespace Prysm.ValidatorIndex

variable [Host]

theorem Encode.fast_path_spec (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (x : UInt64) (pre d0 : List UInt8) (hd0 : d0.length = 8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t28 t18 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (ht28 : t28.length = 16) (ht18 : t18.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t28.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t18.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 x.toNat).toList.At s.regs.rax.toBitVec)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat) :
    ∃ bs, serialize desc (.uint x.toNat) = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨uintBytes 8 x.toNat, Prysm.Epoch.uint64_serialize_eq x, ?_⟩
  have he8 : (uintBytes 8 x.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  refine eventually_mono (Encode.fast_path k hk hf _ pre d0 he8 hd0 s ra guard hpre fp s2 t28 t18 hfp h2 ht28 ht18 R
    h_mem hguard hcap) (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, t, u, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  generalize (uintBytes 8 x.toNat).toList = E8 at hm ⊢
  exact sep_true (by ecancel)

end Prysm.ValidatorIndex
