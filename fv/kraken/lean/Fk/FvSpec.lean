import Fk.FvMarshal
import Fv1.SpecFixedVec
import Fv1.Transfer
import Fk.LuErr

/-!
# FixedVec against EthLib (B2.2)

`fv_unmarshal_accept_spec_k`: if EthLib accepts `bs` (64 bytes) as `v`, the
machine code returns nil and the receiver holds the Go layout of a `g` with
`g.toValue = v`: R = `g.r`, W = (p, 4, 4) with the four elements at p.
`fv_marshal_spec_k`: the marshal fast path writes `fvEncode g` (= EthLib
`serialize fvDesc g.toValue`) at `dst[len:]`, `dst[:len]` unchanged.
`fv_reject_spec`: EthLib rejects every input of another length; the machine
rejects it too (`fv_reject_size_main`). For 64-byte inputs EthLib always
accepts (`fv_accepts_64`), as the Go code does (no other check).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

theorem fvEncode_toList (g : FixedVecG) : (fvEncode g).toList = g.r.toList ++ (u64Bytes g.w.toList).toList := by
  simp [fvEncode]; rfl

theorem fv_accepts_64 (bs : Array UInt8) (h : bs.size = 64) : ∃ g : FixedVecG, bs = fvEncode g := by
  refine ⟨⟨⟨bs.extract 0 32, by simp [h]⟩, ⟨(luElems bs 32 4).toArray, by simp [luElems_length]⟩⟩, ?_⟩
  simp only [fvEncode, Vector.toArray_mk, Vector.toList_mk, List.toList_toArray]
  rw [u64Bytes_luElems bs 4 32 (by omega), Array.extract_append_extract,
    show min 0 32 = 0 from rfl, show max 32 (32 + 8 * 4) = bs.size by omega, Array.extract_size]

theorem fv_reject_spec (bs : Array UInt8) (h : bs.size ≠ 64) : ∃ e, deserialize fvDesc bs = .error e := by
  cases hd : deserialize fvDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := FixedVecG.toValue) (enc := fvEncode) fvDesc_wellFormed
      fv_serialize fv_toValue_surjective hd
    exact absurd (fv_encode_size g) h

variable [Host]

set_option maxHeartbeats 2000000 in
theorem fv_unmarshal_accept_spec_k (k : Nat) (hk : FixedVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh FixedVecUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize fvDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 rslot r0 r1 cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hrs : rslot.length = 8)
    (hr0 : r0.length = 1) (hr1 : r1.length = 31)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : FixedVecG, bsA = fvEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.r.toList.At s.regs.rbx.toBitVec) ⋆ Eq ((u64Bytes g.w.toList).toList.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (r0.At s.regs.rax.toBitVec) ⋆ Eq (r1.At (s.regs.rax.toBitVec + 1))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 40 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size)
    (hav : 8 * 4 ≤ avail) (hmm : MemmoveC S)
    (hms : MakesliceC Heap (label "type__" + 49120).toBitVec 8 S) :
    ∃ g : FixedVecG, g.toValue = v ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ p : BitVec 64, (Eq (g.r.toList.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 4).At (s.regs.rax.toBitVec + 48)) ⋆ Eq ((u64Bytes g.w.toList).toList.At p)
          ⋆ Eq (g.r.toList.At s.regs.rbx.toBitVec) ⋆ Eq ((u64Bytes g.w.toList).toList.At (s.regs.rbx.toBitVec + 32))
          ⋆ Heap (avail - 8 * 4) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := FixedVecG.toValue) (enc := fvEncode) fvDesc_wellFormed
    fv_serialize fv_toValue_surjective hd
  refine ⟨g, rfl, ?_⟩
  exact fv_accept_main k hk hf g.r.toList (u64Bytes g.w.toList).toList (by simp) (by simp [u64Bytes_size])
    s ra guard fp s1 s2 rslot r0 r1 cP cL cC hfp h1 h2 hrs hr0 hr1 hcP hcL hcC R S scratch spm hsc hspm Heap avail
    (P g rfl) hguard hsp (UInt64.toNat_inj.mp (by rw [hlen, fv_encode_size]; rfl)) hav hmm hms

/-- **Marshal fast path against EthLib**: the bytes written at `dst[len:]` are the
EthLib serialization of `g.toValue` (R, then the four elements). -/
theorem fv_marshal_spec_k (g : FixedVecG) :
    serialize fvDesc g.toValue = .ok (fvEncode g) ∧
    (fvEncode g).toList = g.r.toList ++ (u64Bytes g.w.toList).toList :=
  ⟨fv_serialize g, fvEncode_toList g⟩
