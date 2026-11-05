import Fk.LuAccept
import Fv1.SpecList
import Fv1.Transfer

/-!
# ListU64.UnmarshalSSZ accept path against EthLib (B2.1)

`lu_unmarshal_accept_spec_k`: if EthLib accepts `bs` as `v` (`deserialize
luDesc bs = .ok v`), then there is a Go value `g` with at most 16 elements and
`g.toValue = v`, and the machine code returns nil with the receiver slice
header `(p, n, n)`, `n = len g.l`, and the n elements at `p` in Go layout
(8 bytes each, little-endian: `u64Bytes g.l`).

EthLib's `serialize luDesc` succeeds only on values with at most 16 elements
(`lu_serialize` needs `g.ok`), so the transfer lemma is used on the subtype
`{g // g.ok}`. The machine premise is given for the `g` with `bs = luEncode g`
(EthLib's acceptance picks it), as in `sc_unmarshal_accept_spec_k`.

Premises the Go caller provides: see `lu_accept_main`. `hav`: the heap has
room for the largest list (16 elements).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz

abbrev LuG := { g : ListU64 // g.ok }

theorem lu_toValue_surjective' (v : Value) (h : Value.fits luDesc v = true) :
    ∃ g : LuG, g.1.toValue = v := by
  obtain ⟨g, hg, rfl⟩ := lu_toValue_surjective v h
  exact ⟨⟨g, hg⟩, rfl⟩

/-- The two input chunks of the machine premise, concatenated, are the encoding. -/
theorem luEncode_toList (g : ListU64) : (luEncode g).toList = [4, 0, 0, 0] ++ (u64Bytes g.l).toList := by
  simp [luEncode]; rfl

variable [Host]

set_option maxHeartbeats 2000000 in
theorem lu_unmarshal_accept_spec_k (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize luDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s28 s30 s38 s90 s98 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h28 : s28.length = 8) (h30 : s30.length = 8) (h38 : s38.length = 8)
    (h90 : s90.length = 8) (h98 : s98.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : ListU64, g.ok → bsA = luEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (s38.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (s90.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq ((u64Bytes g.l).toList.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R))
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hav : 8 * 16 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 49120).toBitVec 8 S) :
    ∃ g : ListU64, g.ok ∧ g.toValue = v ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        ∃ p : BitVec 64, (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((u64Bytes g.l).toList.At p)
          ⋆ Heap (avail - 8 * g.l.length) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨g, hg⟩, rfl, rfl⟩ := accepted_is_enc (G := LuG) (toV := fun g => g.1.toValue)
    (enc := fun g => luEncode g.1) luDesc_wellFormed (fun g => lu_serialize g.1 g.2)
    lu_toValue_surjective' hd
  refine ⟨g, hg, rfl, ?_⟩
  have hok : g.l.length ≤ 16 := hg
  exact lu_accept_main k hk hf (u64Bytes g.l).toList g.l.length (by simp [u64Bytes_size]) hok s ra guard
    fp s28 s30 s38 s90 s98 rslot cP cL cC hfp h28 h30 h38 h90 h98 hrs hcP hcL hcC R S scratch hsc Heap avail
    (P g hg rfl) hguard hsp (by rw [hlen, lu_encode_size]) hcap hcap63 (by omega) hms
