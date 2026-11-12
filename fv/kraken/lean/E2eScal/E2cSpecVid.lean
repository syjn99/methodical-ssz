import E2eScal.Gen6F24VidEnc
import E2eScal.F24VidSpec
import Fk.RtCopy

/-!
# ValidatorIdentity encoder fast path (generated theorem) against the independent Desc (FLAT24 / H7, text of the unit E2-C emitter)

`vid_e2c_spec_k`: for a receiver holding the Go layout of `g : PVid` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `vid_g6e_fast` writes at
`dst[len:len+64]` exactly the bytes of `serialize prysmVidDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 64 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Fk E2e E2eScal E2eScal.Gen6Enc E2eScal.F24Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem vid_e2c_enc_toList (g : PVid) : (pvidEnc g).toList = (uintBytes 8 g.index.toNat).toList ++ g.pubkey.toList ++ (uintBytes 8 g.activationEpoch.toNat).toList := by
  simp only [pvidEnc, Array.toList_append] <;> rfl

theorem vid_e2c_split (a : BitVec 64) (A0 A1 A2 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 48) (h2 : A2.length = 8) :
    Eq ((A0 ++ A1 ++ A2).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 8)) ⋆ Eq (A2.At (a + 56)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 8) (by rw [h0]; rfl) (by simp [h0, h1, h2]),
    at_app A1 _ (b := a + 56) (by rw [h1]; bv_omega) (by simp [h1, h2])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem vid_e2c_spec_k (k : Nat)
    (hk : VidMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh VidMarshal k)
    (g : PVid)
    (ast c1 pre d0 d1 d2 : List UInt8)
    (hast : ast.length = 8)
    (hc1 : c1.length = 8)
    (hd0 : d0.length = 8)
    (hd1 : d1.length = 48)
    (hd2 : d2.length = 8)
    (p1 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (ht56 : t56.length = 16)
    (ht40 : t40.length = 16)
    (hl24 : l24.length = 8)
    (hl104 : l104.length = 8)
    (hl96 : l96.length = 8)
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
      ⋆ Eq (t56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (t88.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (t72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 160))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 160 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (c1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((uintBytes 8 g.activationEpoch.toNat).toList.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (g.pubkey.toList.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ R)
    (hguard : guard.toNat + 24 < s.regs.rsp.toNat)
    (hsp : 160 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 64 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmVidDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 64 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pvidEnc g, pvid_serialize g, ?_⟩
  have hF0 : (uintBytes 8 g.index.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  have hF1 : g.pubkey.toList.length = 48 := by simp
  have hF2 : (uintBytes 8 g.activationEpoch.toNat).toList.length = 8 := by simp [Fv.uintBytes_size]
  refine eventually_mono (vid_g6e_fast k hk hf ast (uintBytes 8 g.index.toNat).toList (uintBytes 8 g.activationEpoch.toNat).toList c1 (g.pubkey.toList) pre d0 d1 d2 hast hF0 hF2 hc1 hF1 hd0 hd1 hd2 p1 s ra guard hpre fp s1 s2 t56 t40 l24 l104 l96 t88 t72 rslot hfp hs1 hs2 ht56 ht40 hl24 hl104 hl96 ht88 ht72 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [vid_e2c_enc_toList, vid_e2c_split _ _ _ _ hF0 hF1 hF2]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize (uintBytes 8 g.index.toNat).toList = F0 at hm ⊢
  generalize g.pubkey.toList = F1 at hm ⊢
  generalize (uintBytes 8 g.activationEpoch.toNat).toList = F2 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
