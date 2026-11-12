import E2eScal.BhEncMain
import E2eScal.BhSpec
import Runtime.CopyModel

/-!
# BeaconBlockHeader encoder (fast path) against EthLib

`bh_e2e_marshal_spec_k`: for a receiver holding the Go layout of `g : PBh` (Slot = `uintBytes 8 g.slot`,
ProposerIndex = `uintBytes 8 g.proposer`, the three roots = `(p, 32, cap)` with the 32 bytes at `p`), the
encoder fast path writes at `dst[len:len+112]` exactly the bytes of `serialize prysmBhDesc g.toValue` (the
independent consensus-specs Desc of `E2eScal/BhSpec.lean`). The full frame accounting is
`bh_e2e_marshal_main`; this theorem states the output (`⋆ True` remainder of that conclusion), in the form
of `Prysm.Checkpoint.Encode.fast_path_spec`. Fast path only (`len + 112 ≤ cap`, roots of length 32).
-/

open Machine Runtime TestTarget E2e E2eScal.BhCode EthLib.Serialization.Ssz
variable [Host]

open Codec
namespace E2eScal.Bh

theorem pbh_enc_toList (g : PBh) : (pbhEnc g).toList = (uintBytes 8 g.slot.toNat).toList
    ++ (uintBytes 8 g.proposer.toNat).toList ++ g.parent.toList ++ g.state.toList ++ g.body.toList := by
  simp only [pbhEnc, Array.toList_append]; rfl

theorem bh_split5 (a : BitVec 64) (A B C D E : List UInt8) (hA : A.length = 8) (hB : B.length = 8)
    (hC : C.length = 32) (hD : D.length = 32) (hE : E.length = 32) :
    Eq ((A ++ B ++ C ++ D ++ E).At a) = Eq (A.At a) ⋆ Eq (B.At (a + 8)) ⋆ Eq (C.At (a + 16))
      ⋆ Eq (D.At (a + 48)) ⋆ Eq (E.At (a + 80)) := by
  simp only [List.append_assoc]
  rw [at_app A _ (b := a + 8) (by rw [hA]; rfl) (by simp [hA, hB, hC, hD, hE]),
    at_app B _ (b := a + 16) (by rw [hB]; bv_omega) (by simp [hB, hC, hD, hE]),
    at_app C _ (b := a + 48) (by rw [hC]; bv_omega) (by simp [hC, hD, hE]),
    at_app D _ (b := a + 80) (by rw [hD]; bv_omega) (by simp [hD, hE])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem bh_e2e_marshal_spec_k (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (g : PBh) (ast c1 c2 c3 pre d0 d1 d2 d3 d4 : List UInt8)
    (hast : ast.length = 8) (hc1 : c1.length = 8) (hc2 : c2.length = 8) (hc3 : c3.length = 8)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32) (hd3 : d3.length = 32) (hd4 : d4.length = 32)
    (p1 p2 p3 : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t1a t1b t2a t2b rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8)
    (hl96 : l96.length = 8) (hl104 : l104.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16) (ht2a : t2a.length = 16) (ht2b : t2b.length = 16)
    (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t2a.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2b.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.proposer.toNat).toList.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq (c2.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (g.parent.toList.At p1) ⋆ Eq (g.state.toList.At p2) ⋆ Eq (g.body.toList.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80)) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmBhDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 112 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pbhEnc g, pbh_serialize g, ?_⟩
  have hsl : (uintBytes 8 g.slot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hpi : (uintBytes 8 g.proposer.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hr1 : g.parent.toList.length = 32 := by simp
  have hr2 : g.state.toList.length = 32 := by simp
  have hr3 : g.body.toList.length = 32 := by simp
  refine eventually_mono (bh_e2e_marshal_main k hk hf ast _ _ c1 c2 c3 _ _ _ pre d0 d1 d2 d3 d4 hast hsl hpi hc1 hc2 hc3
    hr1 hr2 hr3 hd0 hd1 hd2 hd3 hd4 p1 p2 p3 s ra guard hpre fp s1 s2 l16 l96 l104 t1a t1b t2a t2b rslot
    hfp h1 h2 hl16 hl96 hl104 ht1a ht1b ht2a ht2b hrs R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, t1, u1, t2, u2, scr, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [pbh_enc_toList, bh_split5 _ _ _ _ _ _ hsl hpi hr1 hr2 hr3]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.slot.toNat).toList = SL at hm ⊢
  generalize (uintBytes 8 g.proposer.toNat).toList = PI at hm ⊢
  generalize g.parent.toList = R1 at hm ⊢
  generalize g.state.toList = R2 at hm ⊢
  generalize g.body.toList = R3 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.Bh
