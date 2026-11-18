import Prysm.StatusV2.GeneratedEncodeFastPath
import Prysm.StatusV2.Spec
import Runtime.CopyModel
import Prysm.StatusV2.Code

/-!
# StatusV2 encoder fast path (generated theorem) against the independent Desc

`Encode.generated_fast_spec`: for a receiver holding the Go layout of `g : SszValue` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `Encode.generated_fast` writes at
`dst[len:len+92]` exactly the bytes of `serialize desc g.toValue` (the Desc of the decoder's spec alignment).
Encoder fast path only (`len + 92 ≤ cap`, exact field lengths).
Written by `gen/flat-types/flat_types_encode_spec.py`.
-/

open Machine Runtime Codec Prysm.StatusV2.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.StatusV2

theorem SszValue.encode_toList_generated (g : SszValue) : (SszValue.encode g).toList = g.forkDigest.toList ++ g.finalizedRoot.toList ++ (uintBytes 8 g.finalizedEpoch.toNat).toList ++ g.headRoot.toList ++ (uintBytes 8 g.headSlot.toNat).toList ++ (uintBytes 8 g.earliestAvailableSlot.toNat).toList := by
  simp only [SszValue.encode, Array.toList_append] <;> rfl

theorem Encode.generated_fast_split (a : BitVec 64) (A0 A1 A2 A3 A4 A5 : List UInt8) (h0 : A0.length = 4) (h1 : A1.length = 32) (h2 : A2.length = 8) (h3 : A3.length = 32) (h4 : A4.length = 8) (h5 : A5.length = 8) :
    Eq ((A0 ++ A1 ++ A2 ++ A3 ++ A4 ++ A5).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 4)) ⋆ Eq (A2.At (a + 36)) ⋆ Eq (A3.At (a + 44)) ⋆ Eq (A4.At (a + 76)) ⋆ Eq (A5.At (a + 84)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 4) (by rw [h0]; rfl) (by simp [h0, h1, h2, h3, h4, h5]),
    at_app A1 _ (b := a + 36) (by rw [h1]; bv_omega) (by simp [h1, h2, h3, h4, h5]),
    at_app A2 _ (b := a + 44) (by rw [h2]; bv_omega) (by simp [h2, h3, h4, h5]),
    at_app A3 _ (b := a + 76) (by rw [h3]; bv_omega) (by simp [h3, h4, h5]),
    at_app A4 _ (b := a + 84) (by rw [h4]; bv_omega) (by simp [h4, h5])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_spec (k : Nat)
    (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh marshalSSZTo k)
    (g : SszValue)
    (ast c0 c1 c3 pre d0 d1 d2 d3 d4 d5 : List UInt8)
    (hast : ast.length = 8)
    (hc0 : c0.length = 8)
    (hc1 : c1.length = 8)
    (hc3 : c3.length = 8)
    (hd0 : d0.length = 4)
    (hd1 : d1.length = 32)
    (hd2 : d2.length = 8)
    (hd3 : d3.length = 32)
    (hd4 : d4.length = 8)
    (hd5 : d5.length = 8)
    (p0 p1 p3 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l144 l160 l24 t64 t48 l152 l168 l32 t96 t80 t128 t112 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl144 : l144.length = 8)
    (hl160 : l160.length = 8)
    (hl24 : l24.length = 8)
    (ht64 : t64.length = 16)
    (ht48 : t48.length = 16)
    (hl152 : l152.length = 8)
    (hl168 : l168.length = 8)
    (hl32 : l32.length = 8)
    (ht96 : t96.length = 16)
    (ht80 : t80.length = 16)
    (ht128 : t128.length = 16)
    (ht112 : t112.length = 16)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (t64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (t48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l168.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (t96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (t128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (t112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 232 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((uintBytes 8 g.finalizedEpoch.toNat).toList.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq ((uintBytes 8 g.headSlot.toNat).toList.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq ((uintBytes 8 g.earliestAvailableSlot.toNat).toList.At (s.regs.rax.toBitVec + 96))
      ⋆ Eq (g.forkDigest.toList.At p0)
      ⋆ Eq (g.finalizedRoot.toList.At p1)
      ⋆ Eq (g.headRoot.toList.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 4))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 36))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 44))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 76))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 84))
      ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat)
    (hsp : 232 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 92 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 92 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, ?_⟩
  have hF0 : g.forkDigest.toList.length = 4 := by simp
  have hF1 : g.finalizedRoot.toList.length = 32 := by simp
  have hF2 : (uintBytes 8 g.finalizedEpoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF3 : g.headRoot.toList.length = 32 := by simp
  have hF4 : (uintBytes 8 g.headSlot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF5 : (uintBytes 8 g.earliestAvailableSlot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  refine eventually_mono (Encode.generated_fast k hk hf ast (uintBytes 8 g.finalizedEpoch.toNat).toList (uintBytes 8 g.headSlot.toNat).toList (uintBytes 8 g.earliestAvailableSlot.toNat).toList c0 c1 c3 (g.forkDigest.toList) (g.finalizedRoot.toList) (g.headRoot.toList) pre d0 d1 d2 d3 d4 d5 hast hF2 hF4 hF5 hc0 hc1 hc3 hF0 hF1 hF3 hd0 hd1 hd2 hd3 hd4 hd5 p0 p1 p3 s ra guard hpre fp s1 s2 l144 l160 l24 t64 t48 l152 l168 l32 t96 t80 t128 t112 rslot hfp hs1 hs2 hl144 hl160 hl24 ht64 ht48 hl152 hl168 hl32 ht96 ht80 ht128 ht112 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [SszValue.encode_toList_generated, Encode.generated_fast_split _ _ _ _ _ _ _ hF0 hF1 hF2 hF3 hF4 hF5]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.forkDigest.toList = F0 at hm ⊢
  generalize g.finalizedRoot.toList = F1 at hm ⊢
  generalize (uintBytes 8 g.finalizedEpoch.toNat).toList = F2 at hm ⊢
  generalize g.headRoot.toList = F3 at hm ⊢
  generalize (uintBytes 8 g.headSlot.toNat).toList = F4 at hm ⊢
  generalize (uintBytes 8 g.earliestAvailableSlot.toNat).toList = F5 at hm ⊢
  exact sep_true (by ecancel)

end Prysm.StatusV2
