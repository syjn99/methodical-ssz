import Prysm.SyncCommitteeMessage.GeneratedEncodeFastPath
import Prysm.SyncCommitteeMessage.Spec
import Runtime.CopyModel

/-!
# SyncCommitteeMessage encoder fast path (generated theorem) against the independent Desc

`Encode.generated_fast_spec`: for a receiver holding the Go layout of `g : SszValue` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `Encode.generated_fast` writes at
`dst[len:len+144]` exactly the bytes of `serialize desc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `Prysm.BeaconBlockHeader.Encode.fast_path_spec`. Encoder fast path only (`len + 144 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime Codec Prysm.SyncCommitteeMessage.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.SyncCommitteeMessage

theorem SszValue.encode_toList_generated (g : SszValue) : (SszValue.encode g).toList = (uintBytes 8 g.slot.toNat).toList ++ g.blockRoot.toList ++ (uintBytes 8 g.validatorIndex.toNat).toList ++ g.signature.toList := by
  simp only [SszValue.encode, Array.toList_append] <;> rfl

theorem Encode.generated_fast_split (a : BitVec 64) (A0 A1 A2 A3 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 32) (h2 : A2.length = 8) (h3 : A3.length = 96) :
    Eq ((A0 ++ A1 ++ A2 ++ A3).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 8)) ⋆ Eq (A2.At (a + 40)) ⋆ Eq (A3.At (a + 48)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 8) (by rw [h0]; rfl) (by simp [h0, h1, h2, h3]),
    at_app A1 _ (b := a + 40) (by rw [h1]; bv_omega) (by simp [h1, h2, h3]),
    at_app A2 _ (b := a + 48) (by rw [h2]; bv_omega) (by simp [h2, h3])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_spec (k : Nat)
    (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh marshalSSZTo k)
    (g : SszValue)
    (ast c1 c3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8)
    (hc1 : c1.length = 8)
    (hc3 : c3.length = 8)
    (hd0 : d0.length = 8)
    (hd1 : d1.length = 32)
    (hd2 : d2.length = 8)
    (hd3 : d3.length = 96)
    (p1 p3 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l112 l120 l24 t88 t72 l16 l96 l104 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (ht56 : t56.length = 16)
    (ht40 : t40.length = 16)
    (hl112 : l112.length = 8)
    (hl120 : l120.length = 8)
    (hl24 : l24.length = 8)
    (ht88 : t88.length = 16)
    (ht72 : t72.length = 16)
    (hl16 : l16.length = 8)
    (hl96 : l96.length = 8)
    (hl104 : l104.length = 8)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 184 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq (g.blockRoot.toList.At p1)
      ⋆ Eq (g.signature.toList.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ R)
    (hguard : guard.toNat + 48 < s.regs.rsp.toNat)
    (hsp : 184 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 144 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 144 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, ?_⟩
  have hF0 : (uintBytes 8 g.slot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF1 : g.blockRoot.toList.length = 32 := by simp
  have hF2 : (uintBytes 8 g.validatorIndex.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF3 : g.signature.toList.length = 96 := by simp
  refine eventually_mono (Encode.generated_fast k hk hf ast (uintBytes 8 g.slot.toNat).toList (uintBytes 8 g.validatorIndex.toNat).toList c1 c3 (g.blockRoot.toList) (g.signature.toList) pre d0 d1 d2 d3 hast hF0 hF2 hc1 hc3 hF1 hF3 hd0 hd1 hd2 hd3 p1 p3 s ra guard hpre fp s1 s2 t56 t40 l112 l120 l24 t88 t72 l16 l96 l104 rslot hfp hs1 hs2 ht56 ht40 hl112 hl120 hl24 ht88 ht72 hl16 hl96 hl104 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [SszValue.encode_toList_generated, Encode.generated_fast_split _ _ _ _ _ hF0 hF1 hF2 hF3]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.slot.toNat).toList = F0 at hm ⊢
  generalize g.blockRoot.toList = F1 at hm ⊢
  generalize (uintBytes 8 g.validatorIndex.toNat).toList = F2 at hm ⊢
  generalize g.signature.toList = F3 at hm ⊢
  exact sep_true (by ecancel)

end Prysm.SyncCommitteeMessage
