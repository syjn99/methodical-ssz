import E2eScal.Gen6VbEnc
import E2eScal.VbSpec
import Runtime.CopyModel

/-!
# ValidatorBalance encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`vb_e2c_spec_k`: for a receiver holding the Go layout of `g : PVb` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `vb_g6e_fast` writes at
`dst[len:len+16]` exactly the bytes of `serialize prysmVbDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 16 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.Gen6Enc E2eScal.Enc2Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem vb_e2c_enc_toList (g : PVb) : (pvbEnc g).toList = (uintBytes 8 g.index.toNat).toList ++ (uintBytes 8 g.balance.toNat).toList := by
  simp only [pvbEnc, Array.toList_append] <;> rfl

theorem vb_e2c_split (a : BitVec 64) (A0 A1 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 8) :
    Eq ((A0 ++ A1).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 8)) := by
  rw [at_app A0 _ (b := a + 8) (by rw [h0]; rfl) (by simp [h0, h1])]

set_option maxHeartbeats 4000000 in
theorem vb_e2c_spec_k (k : Nat)
    (hk : VbMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh VbMarshal k)
    (g : PVb)
    (ast pre d0 d1 : List UInt8)
    (hast : ast.length = 8)
    (hd0 : d0.length = 8)
    (hd1 : d1.length = 8)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s2 t40 t24 : List UInt8)
    (hfp : fp.length = 8)
    (hs2 : s2.length = 8)
    (ht40 : t40.length = 16)
    (ht24 : t24.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.balance.toNat).toList.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    ∃ bs, serialize prysmVbDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 16 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pvbEnc g, pvb_serialize g, ?_⟩
  have hF0 : (uintBytes 8 g.index.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF1 : (uintBytes 8 g.balance.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  refine eventually_mono (vb_g6e_fast k hk hf ast (uintBytes 8 g.index.toNat).toList (uintBytes 8 g.balance.toNat).toList pre d0 d1 hast hF0 hF1 hd0 hd1 s ra guard hpre fp s2 t40 t24 hfp hs2 ht40 ht24 R h_mem hguard hsp hcap hcap63)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [vb_e2c_enc_toList, vb_e2c_split _ _ _ hF0 hF1]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.index.toNat).toList = F0 at hm ⊢
  generalize (uintBytes 8 g.balance.toNat).toList = F1 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
