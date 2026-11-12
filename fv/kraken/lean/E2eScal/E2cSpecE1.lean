import E2eScal.Gen6E1Enc
import E2eScal.E1Spec
import Fk.RtCopy

/-!
# Eth1Data encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`e1_e2c_spec_k`: for a receiver holding the Go layout of `g : PE1` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `e1_g6e_fast` writes at
`dst[len:len+72]` exactly the bytes of `serialize prysmE1Desc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 72 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Fk E2e E2eScal E2eScal.Gen6Enc E2eScal.E1Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem e1_e2c_enc_toList (g : PE1) : (pe1Enc g).toList = g.depositRoot.toList ++ (uintBytes 8 g.depositCount.toNat).toList ++ g.blockHash.toList := by
  simp only [pe1Enc, Array.toList_append] <;> rfl

theorem e1_e2c_split (a : BitVec 64) (A0 A1 A2 : List UInt8) (h0 : A0.length = 32) (h1 : A1.length = 8) (h2 : A2.length = 32) :
    Eq ((A0 ++ A1 ++ A2).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 32)) ⋆ Eq (A2.At (a + 40)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 32) (by rw [h0]; rfl) (by simp [h0, h1, h2]),
    at_app A1 _ (b := a + 40) (by rw [h1]; bv_omega) (by simp [h1, h2])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem e1_e2c_spec_k (k : Nat)
    (hk : E1Marshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh E1Marshal k)
    (g : PE1)
    (ast c0 c2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8)
    (hc0 : c0.length = 8)
    (hc2 : c2.length = 8)
    (hd0 : d0.length = 32)
    (hd1 : d1.length = 8)
    (hd2 : d2.length = 32)
    (p0 p2 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl16 : l16.length = 8)
    (hl24 : l24.length = 8)
    (hl32 : l32.length = 8)
    (hl40 : l40.length = 8)
    (hl48 : l48.length = 8)
    (hl56 : l56.length = 8)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((uintBytes 8 g.depositCount.toNat).toList.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (g.depositRoot.toList.At p0)
      ⋆ Eq (g.blockHash.toList.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
      ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmE1Desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 72 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pe1Enc g, pe1_serialize g, ?_⟩
  have hF0 : g.depositRoot.toList.length = 32 := by simp
  have hF1 : (uintBytes 8 g.depositCount.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  have hF2 : g.blockHash.toList.length = 32 := by simp
  refine eventually_mono (e1_g6e_fast k hk hf ast (uintBytes 8 g.depositCount.toNat).toList c0 c2 (g.depositRoot.toList) (g.blockHash.toList) pre d0 d1 d2 hast hF1 hc0 hc2 hF0 hF2 hd0 hd1 hd2 p0 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot hfp hs1 hs2 hl16 hl24 hl32 hl40 hl48 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [e1_e2c_enc_toList, e1_e2c_split _ _ _ _ hF0 hF1 hF2]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.depositRoot.toList = F0 at hm ⊢
  generalize (uintBytes 8 g.depositCount.toNat).toList = F1 at hm ⊢
  generalize g.blockHash.toList = F2 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
