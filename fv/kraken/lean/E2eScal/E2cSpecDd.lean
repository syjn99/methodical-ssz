import E2eScal.Gen6DdEnc
import E2eScal.DdSpec
import Runtime.CopyModel

/-!
# Deposit_Data encoder fast path (generated theorem) against the independent Desc (unit E2-C)

`dd_e2c_spec_k`: for a receiver holding the Go layout of `g : PDd` (uint64 fields = `uintBytes 8`, byte
fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `dd_g6e_fast` writes at
`dst[len:len+184]` exactly the bytes of `serialize prysmDdDesc g.toValue` (the Desc of the decoder's spec alignment).
Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + 184 ≤ cap`, exact field
lengths). Emitted by the unit's evidence tool `e2cemit.py`, then built and kernel-checked.
-/

open Machine Runtime TestTarget E2e E2eScal Codec E2eScal.Gen6Enc E2eScal.Enc2Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E2c

theorem dd_e2c_enc_toList (g : PDd) : (pddEnc g).toList = g.pubkey.toList ++ g.withdrawalCredentials.toList ++ (uintBytes 8 g.amount.toNat).toList ++ g.signature.toList := by
  simp only [pddEnc, Array.toList_append] <;> rfl

theorem dd_e2c_split (a : BitVec 64) (A0 A1 A2 A3 : List UInt8) (h0 : A0.length = 48) (h1 : A1.length = 32) (h2 : A2.length = 8) (h3 : A3.length = 96) :
    Eq ((A0 ++ A1 ++ A2 ++ A3).At a) = Eq (A0.At a) ⋆ Eq (A1.At (a + 48)) ⋆ Eq (A2.At (a + 80)) ⋆ Eq (A3.At (a + 88)) := by
  simp only [List.append_assoc]
  rw [at_app A0 _ (b := a + 48) (by rw [h0]; rfl) (by simp [h0, h1, h2, h3]),
    at_app A1 _ (b := a + 80) (by rw [h1]; bv_omega) (by simp [h1, h2, h3]),
    at_app A2 _ (b := a + 88) (by rw [h2]; bv_omega) (by simp [h2, h3])]
  simp only [Std.ExtHashMap.sep_assoc]

set_option maxHeartbeats 4000000 in
theorem dd_e2c_spec_k (k : Nat)
    (hk : DdMarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh DdMarshal k)
    (g : PDd)
    (ast c0 c1 c3 pre d0 d1 d2 d3 : List UInt8)
    (hast : ast.length = 8)
    (hc0 : c0.length = 8)
    (hc1 : c1.length = 8)
    (hc3 : c3.length = 8)
    (hd0 : d0.length = 48)
    (hd1 : d1.length = 32)
    (hd2 : d2.length = 8)
    (hd3 : d3.length = 96)
    (p0 p1 p3 : BitVec 64)
    (s : MachineData)
    (ra guard : UInt64)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 l16 l40 l48 l32 l64 l56 rslot : List UInt8)
    (hfp : fp.length = 8)
    (hs1 : s1.length = 8)
    (hs2 : s2.length = 8)
    (hl16 : l16.length = 8)
    (hl40 : l40.length = 8)
    (hl48 : l48.length = 8)
    (hl32 : l32.length = 8)
    (hl64 : l64.length = 8)
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
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
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
      ⋆ Eq (g.pubkey.toList.At p0)
      ⋆ Eq (g.withdrawalCredentials.toList.At p1)
      ⋆ Eq (g.signature.toList.At p3)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 80))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ R)
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat)
    (hsp : 152 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 184 ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveC S) :
    ∃ bs, serialize prysmDdDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 184 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨pddEnc g, pdd_serialize g, ?_⟩
  have hF0 : g.pubkey.toList.length = 48 := by simp
  have hF1 : g.withdrawalCredentials.toList.length = 32 := by simp
  have hF2 : (uintBytes 8 g.amount.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hF3 : g.signature.toList.length = 96 := by simp
  refine eventually_mono (dd_g6e_fast k hk hf ast (uintBytes 8 g.amount.toNat).toList c0 c1 c3 (g.pubkey.toList) (g.withdrawalCredentials.toList) (g.signature.toList) pre d0 d1 d2 d3 hast hF2 hc0 hc1 hc3 hF0 hF1 hF3 hd0 hd1 hd2 hd3 p0 p1 p3 s ra guard hpre fp s1 s2 l16 l40 l48 l32 l64 l56 rslot hfp hs1 hs2 hl16 hl40 hl48 hl32 hl64 hl56 hrslot R S scratch hsc h_mem hguard hsp hcap hcap63 hmm)
    (fun st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, _, _, hm⟩ =>
      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)
  rw [dd_e2c_enc_toList, dd_e2c_split _ _ _ _ _ hF0 hF1 hF2 hF3]
  simp only [← Std.ExtHashMap.sep_assoc]
  generalize g.pubkey.toList = F0 at hm ⊢
  generalize g.withdrawalCredentials.toList = F1 at hm ⊢
  generalize (uintBytes 8 g.amount.toNat).toList = F2 at hm ⊢
  generalize g.signature.toList = F3 at hm ⊢
  exact sep_true (by ecancel)

end E2eScal.E2c
