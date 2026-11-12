import E2eScal.Gen6F24PdcEnc
import E2eScal.F24PdcSpec
import Fk.RtCopy

/-!
# PartialDataColumnGroupID encoder fast path (generated theorem) against the independent Desc (FLAT24 / H7, text of the unit E2-C emitter)

`pdc_e2c_spec_k`: for a receiver holding the Go layout of `g : PPdc` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `pdc_g6e_fast` writes at
`dst[len:len+40]` exactly the bytes of `serialize prysmPdcDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 40 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Fk E2e E2eScal E2eScal.Gen6Enc E2eScal.F24Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem pdc_e2c_enc_toList (g : PPdc) : (ppdcEnc g).toList = g.beaconBlockRoot.toList ++ (uintBytes 8 g.slot.toNat).toList := by
  simp only [ppdcEnc, Array.toList_append] <;> rfl

theorem pdc_e2c_split (a : BitVec 64) (A0 A1 : List UInt8) (h0 : A0.length = 32) (h1 : A1.length = 8) :
    Eq ((A0 ++ A1).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 32)) := by
  rw [at_app A0 _ (b := a + 32) (by rw [h0]; rfl) (by simp [h0, h1])]

set_option maxHeartbeats 4000000 in
theorem pdc_e2c_spec_k (k : Nat)
    (hk : PdcMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh PdcMarshal k)
    (g : PPdc)
    (ast c0 pre d0 d1 : List UInt8)
    (hast : ast.length = 8)
    (hc0 : c0.length = 8)
    (hd0 : d0.length = 32)
    (hd1 : d1.length = 8)
    (p0 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l24 l64 l72 t56 t40 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl24 : l24.length = 8)
    (hl64 : l64.length = 8)
    (hl72 : l72.length = 8)
    (ht56 : t56.length = 16)
    (ht40 : t40.length = 16)
    (hrslot : rslot.length = 8)
    (R : DataMem → Prop)
    (S : Nat)
    (scratch : List UInt8)
    (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 p0.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (c0.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (g.beaconBlockRoot.toList.At p0)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 32))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmPdcDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨ppdcEnc g, ppdc_serialize g, ?_⟩
  have hF0 : g.beaconBlockRoot.toList.length = 32 := by simp
  have hF1 : (uintBytes 8 g.slot.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  refine eventually_mono (pdc_g6e_fast k hk hf ast (uintBytes 8 g.slot.toNat).toList c0 (g.beaconBlockRoot.toList) pre d0 d1 hast hF1 hc0 hF0 hd0 hd1 p0 s ra guard hpre fp s1 s2 l24 l64 l72 t56 t40 rslot hfp hs1 hs2 hl24 hl64 hl72 ht56 ht40 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [pdc_e2c_enc_toList, pdc_e2c_split _ _ _ hF0 hF1]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.beaconBlockRoot.toList = F0 at hm ⊢
  generalize (uintBytes 8 g.slot.toNat).toList = F1 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
