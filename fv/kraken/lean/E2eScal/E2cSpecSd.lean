import E2eScal.Gen6SdEnc
import E2eScal.SdSpec
import Fk.RtCopy

/-!
# SigningData encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`sd_e2c_spec_k`: for a receiver holding the Go layout of `g : PSd` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `sd_g6e_fast` writes at
`dst[len:len+64]` exactly the bytes of `serialize prysmSdDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 64 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Fk E2e E2eScal E2eScal.Gen6Enc E2eScal.Enc2Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem sd_e2c_enc_toList (g : PSd) : (psdEnc g).toList = g.objectRoot.toList ++ g.domain.toList := by
  simp only [psdEnc, Array.toList_append] <;> rfl

theorem sd_e2c_split (a : BitVec 64) (A0 A1 : List UInt8) (h0 : A0.length = 32) (h1 : A1.length = 32) :
    Eq ((A0 ++ A1).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 32)) := by
  rw [at_app A0 _ (b := a + 32) (by rw [h0]; rfl) (by simp [h0, h1])]

set_option maxHeartbeats 4000000 in
theorem sd_e2c_spec_k (k : Nat)
    (hk : SdMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh SdMarshal k)
    (g : PSd)
    (c0 c1 pre d0 d1 : List UInt8)
    (hc0 : c0.length = 8)
    (hc1 : c1.length = 8)
    (hd0 : d0.length = 32)
    (hd1 : d1.length = 32)
    (p0 p1 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l32 l40 l16 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl32 : l32.length = 8)
    (hl40 : l40.length = 8)
    (hl16 : l16.length = 8)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (g.objectRoot.toList.At p0)
      ⋆ Eq (g.domain.toList.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hsp : 96 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmSdDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨psdEnc g, psd_serialize g, ?_⟩
  have hF0 : g.objectRoot.toList.length = 32 := by simp
  have hF1 : g.domain.toList.length = 32 := by simp
  refine eventually_mono (sd_g6e_fast k hk hf c0 c1 (g.objectRoot.toList) (g.domain.toList) pre d0 d1 hc0 hc1 hF0 hF1 hd0 hd1 p0 p1 s ra guard hpre fp s1 s2 l32 l40 l16 rslot hfp hs1 hs2 hl32 hl40 hl16 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [sd_e2c_enc_toList, sd_e2c_split _ _ _ hF0 hF1]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.objectRoot.toList = F0 at hm ⊢
  generalize g.domain.toList = F1 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
