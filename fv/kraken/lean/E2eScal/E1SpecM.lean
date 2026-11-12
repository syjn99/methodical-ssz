import E2eScal.E1EncMain
import E2eScal.E1Spec
import Runtime.CopyModel

/-!
# Eth1Data encoder (fast path) against EthLib

`e1_e2e_marshal_spec_k`: for a receiver holding the Go layout of `g : PE1` (DepositRoot and BlockHash =
`(p, 32, cap)` with the 32 bytes at `p`, DepositCount = `uintBytes 8 g.depositCount`), the encoder fast
path writes at `dst[len:len+72]` exactly the bytes of `serialize prysmE1Desc g.toValue` (the independent
consensus-specs Desc of `E2eScal/E1Desc.lean`). The full frame accounting is `e1_e2e_marshal_main`; this
theorem states the output (`⋆ True` remainder of that conclusion), in the form of
`E2eScal.Bh.bh_e2e_marshal_spec_k`. Fast path only (`len + 72 ≤ cap`, roots of length 32).
-/

open Machine Runtime TestTarget E2e E2eScal.E1Code EthLib.Serialization.Ssz
variable [Host]

open Codec
namespace E2eScal.E1

theorem pe1_enc_toList (g : PE1) : (pe1Enc g).toList = g.depositRoot.toList
    ++ (uintBytes 8 g.depositCount.toNat).toList ++ g.blockHash.toList := by
  simp only [pe1Enc, Array.toList_append]; rfl

theorem e1_split3 (a : BitVec 64) (A B C : List UInt8) (hA : A.length = 32) (hB : B.length = 8)
    (hC : C.length = 32) :
    Eq ((A ++ B ++ C).At a) = Eq (A.At a) ⋆ Eq (B.At (a + 32)) ⋆ Eq (C.At (a + 40)) := by
  simp only [List.append_assoc]
  rw [at_app A _ (b := a + 32) (by rw [hA]; rfl) (by simp [hA, hB, hC]),
    at_app B _ (b := a + 40) (by rw [hB]; bv_omega) (by simp [hB, hC])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem e1_e2e_marshal_spec_k (k : Nat) (hk : E1Marshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Marshal k)
    (g : PE1) (ast c1 c2 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8)
    (hd0 : d0.length = 32) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (p1 p2 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l24 l32 l40 l48 l56 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8)
    (hl56 : l56.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((uintBytes 8 g.depositCount.toNat).toList.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (g.depositRoot.toList.At p1) ⋆ Eq (g.blockHash.toList.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40)) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat) (hsp : 144 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 72 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
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
  have hdc : (uintBytes 8 g.depositCount.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hr1 : g.depositRoot.toList.length = 32 := by simp
  have hr2 : g.blockHash.toList.length = 32 := by simp
  refine eventually_mono (e1_e2e_marshal_main k hk hf ast _ c1 c2 _ _ pre d0 d1 d2 hast hdc hc1 hc2
    hr1 hr2 hd0 hd1 hd2 p1 p2 s ra guard hpre fp s1 s2 l16 l24 l32 l40 l48 l56 rslot
    hfp h1 h2 hl16 hl24 hl32 hl40 hl48 hl56 hrs R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, scr, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [pe1_enc_toList, e1_split3 _ _ _ _ hr1 hdc hr2]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.depositCount.toNat).toList = DC at hm ⊢
  generalize g.depositRoot.toList = R1 at hm ⊢
  generalize g.blockHash.toList = R2 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E1
