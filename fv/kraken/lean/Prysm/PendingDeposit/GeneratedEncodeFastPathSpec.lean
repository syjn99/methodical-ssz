import Prysm.PendingDeposit.GeneratedEncodeFastPath
import Prysm.PendingDeposit.Spec
import Runtime.CopyModel

/-!
# PendingDeposit encoder fast path (generated theorem) against the independent Desc

`Encode.generated_fast_spec`: for a receiver holding the Go layout of `g : SszValue` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `Encode.generated_fast` writes at
`dst[len:len+192]` exactly the bytes of `serialize desc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `Prysm.BeaconBlockHeader.Encode.fast_path_spec`. Encoder fast path only (`len + 192 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime Codec Prysm.PendingDeposit.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.PendingDeposit

theorem SszValue.encode_toList_generated (g : SszValue) : (SszValue.encode g).toList = g.pubkey.toList ++ g.withdrawalCredentials.toList ++ (uintBytes 8 g.amount.toNat).toList ++ g.signature.toList ++ (uintBytes 8 g.slot.toNat).toList := by
  simp only [SszValue.encode, Array.toList_append] <;> rfl

theorem Encode.generated_fast_split (a : BitVec 64) (A0 A1 A2 A3 A4 : List UInt8) (h0 : A0.length = 48) (h1 : A1.length = 32) (h2 : A2.length = 8) (h3 : A3.length = 96) (h4 : A4.length = 8) :
    Eq ((A0 ++ A1 ++ A2 ++ A3 ++ A4).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 48)) ⋆ Eq (A2.At (a + 80)) ⋆ Eq (A3.At (a + 88)) ⋆ Eq (A4.At (a + 184)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 48) (by rw [h0]; rfl) (by simp [h0, h1, h2, h3, h4]),
    at_app A1 _ (b := a + 80) (by rw [h1]; bv_omega) (by simp [h1, h2, h3, h4]),
    at_app A2 _ (b := a + 88) (by rw [h2]; bv_omega) (by simp [h2, h3, h4]),
    at_app A3 _ (b := a + 184) (by rw [h3]; bv_omega) (by simp [h3, h4])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem Encode.generated_fast_spec (k : Nat)
    (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh marshalSSZTo k)
    (g : SszValue)
    (ast c0 c1 c3 pre d0 d1 d2 d3 d4 : List UInt8)
    (hast : ast.length = 8)
    (hc0 : c0.length = 8)
    (hc1 : c1.length = 8)
    (hc3 : c3.length = 8)
    (hd0 : d0.length = 48)
    (hd1 : d1.length = 32)
    (hd2 : d2.length = 8)
    (hd3 : d3.length = 96)
    (hd4 : d4.length = 8)
    (p0 p1 p3 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l48 l56 l16 l96 l104 l32 l120 l40 l112 t88 t72 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl48 : l48.length = 8)
    (hl56 : l56.length = 8)
    (hl16 : l16.length = 8)
    (hl96 : l96.length = 8)
    (hl104 : l104.length = 8)
    (hl32 : l32.length = 8)
    (hl120 : l120.length = 8)
    (hl40 : l40.length = 8)
    (hl112 : l112.length = 8)
    (ht88 : t88.length = 16)
    (ht72 : t72.length = 16)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l120.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l112.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 208))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 208 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (g.pubkey.toList.At p0)
      ⋆ Eq (g.withdrawalCredentials.toList.At p1)
      ⋆ Eq (g.signature.toList.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 184))
      ⋆ R)
    (hguard : guard.toNat + 72 < s.regs.rsp.toNat)
    (hsp : 208 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 192 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 192 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, ?_⟩
  have hF0 : g.pubkey.toList.length = 48 := by simp
  have hF1 : g.withdrawalCredentials.toList.length = 32 := by simp
  have hF2 : (uintBytes 8 g.amount.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF3 : g.signature.toList.length = 96 := by simp
  have hF4 : (uintBytes 8 g.slot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  refine eventually_mono (Encode.generated_fast k hk hf ast (uintBytes 8 g.amount.toNat).toList (uintBytes 8 g.slot.toNat).toList c0 c1 c3 (g.pubkey.toList) (g.withdrawalCredentials.toList) (g.signature.toList) pre d0 d1 d2 d3 d4 hast hF2 hF4 hc0 hc1 hc3 hF0 hF1 hF3 hd0 hd1 hd2 hd3 hd4 p0 p1 p3 s ra guard hpre fp s1 s2 l48 l56 l16 l96 l104 l32 l120 l40 l112 t88 t72 rslot hfp hs1 hs2 hl48 hl56 hl16 hl96 hl104 hl32 hl120 hl40 hl112 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [SszValue.encode_toList_generated, Encode.generated_fast_split _ _ _ _ _ _ hF0 hF1 hF2 hF3 hF4]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.pubkey.toList = F0 at hm ⊢
  generalize g.withdrawalCredentials.toList = F1 at hm ⊢
  generalize (uintBytes 8 g.amount.toNat).toList = F2 at hm ⊢
  generalize g.signature.toList = F3 at hm ⊢
  generalize (uintBytes 8 g.slot.toNat).toList = F4 at hm ⊢
  exact sep_true (by ecancel)

end Prysm.PendingDeposit
