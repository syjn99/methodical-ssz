import E2eScal.Gen6BhEnc
import E2eScal.BhSpec
import Runtime.CopyModel

/-!
# BeaconBlockHeader encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`bh_e2c_spec_k`: for a receiver holding the Go layout of `g : PBh` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `bh_g6e_fast` writes at
`dst[len:len+112]` exactly the bytes of `serialize prysmBhDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 112 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.Gen6Enc E2eScal.BhCode EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem bh_e2c_enc_toList (g : PBh) : (pbhEnc g).toList = (uintBytes 8 g.slot.toNat).toList ++ (uintBytes 8 g.proposer.toNat).toList ++ g.parent.toList ++ g.state.toList ++ g.body.toList := by
  simp only [pbhEnc, Array.toList_append] <;> rfl

theorem bh_e2c_split (a : BitVec 64) (A0 A1 A2 A3 A4 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 8) (h2 : A2.length = 32) (h3 : A3.length = 32) (h4 : A4.length = 32) :
    Eq ((A0 ++ A1 ++ A2 ++ A3 ++ A4).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 8)) ⋆ Eq (A2.At (a + 16)) ⋆ Eq (A3.At (a + 48)) ⋆ Eq (A4.At (a + 80)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 8) (by rw [h0]; rfl) (by simp [h0, h1, h2, h3, h4]),
    at_app A1 _ (b := a + 16) (by rw [h1]; bv_omega) (by simp [h1, h2, h3, h4]),
    at_app A2 _ (b := a + 48) (by rw [h2]; bv_omega) (by simp [h2, h3, h4]),
    at_app A3 _ (b := a + 80) (by rw [h3]; bv_omega) (by simp [h3, h4])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem bh_e2c_spec_k (k : Nat)
    (hk : BhMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh BhMarshal k)
    (g : PBh)
    (ast c2 c3 c4 pre d0 d1 d2 d3 d4 : List UInt8)
    (hast : ast.length = 8)
    (hc2 : c2.length = 8)
    (hc3 : c3.length = 8)
    (hc4 : c4.length = 8)
    (hd0 : d0.length = 8)
    (hd1 : d1.length = 8)
    (hd2 : d2.length = 32)
    (hd3 : d3.length = 32)
    (hd4 : d4.length = 32)
    (p2 p3 p4 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl16 : l16.length = 8)
    (hl96 : l96.length = 8)
    (hl104 : l104.length = 8)
    (ht56 : t56.length = 16)
    (ht40 : t40.length = 16)
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
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.proposer.toNat).toList.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (c3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ((Int.toBytes 8 p4.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 88))
      ⋆ Eq (g.parent.toList.At p2)
      ⋆ Eq (g.state.toList.At p3)
      ⋆ Eq (g.body.toList.At p4)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat)
    (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
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
  have hF0 : (uintBytes 8 g.slot.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF1 : (uintBytes 8 g.proposer.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF2 : g.parent.toList.length = 32 := by simp
  have hF3 : g.state.toList.length = 32 := by simp
  have hF4 : g.body.toList.length = 32 := by simp
  refine eventually_mono (bh_g6e_fast k hk hf ast (uintBytes 8 g.slot.toNat).toList (uintBytes 8 g.proposer.toNat).toList c2 c3 c4 (g.parent.toList) (g.state.toList) (g.body.toList) pre d0 d1 d2 d3 d4 hast hF0 hF1 hc2 hc3 hc4 hF2 hF3 hF4 hd0 hd1 hd2 hd3 hd4 p2 p3 p4 s ra guard hpre fp s1 s2 l16 l96 l104 t56 t40 t88 t72 rslot hfp hs1 hs2 hl16 hl96 hl104 ht56 ht40 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [bh_e2c_enc_toList, bh_e2c_split _ _ _ _ _ _ hF0 hF1 hF2 hF3 hF4]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.slot.toNat).toList = F0 at hm ⊢
  generalize (uintBytes 8 g.proposer.toNat).toList = F1 at hm ⊢
  generalize g.parent.toList = F2 at hm ⊢
  generalize g.state.toList = F3 at hm ⊢
  generalize g.body.toList = F4 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
