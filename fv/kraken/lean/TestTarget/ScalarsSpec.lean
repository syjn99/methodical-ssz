import TestTarget.ScalarsDecodeAccept
import TestTarget.ScalarsEncode
import Spec.TestScalars
import Spec.DeserializeOfSerialize

/-!
# Scalars.UnmarshalSSZ against EthLib (Kraken main)

`sc_unmarshal_accept_spec_k`: if EthLib accepts `bs` as `v`, the machine code
returns nil and the receiver holds the Go layout of some `g` with `g.toValue = v`.
-/

open Machine TestTarget TestTarget.Code Spec EthLib.Serialization.Ssz
variable [Host]

def scField (g : Scalars) : Fin 5 → List UInt8
  | 0 => (uintBytes 1 g.a.toNat).toList
  | 1 => (uintBytes 2 g.b.toNat).toList
  | 2 => (uintBytes 4 g.c.toNat).toList
  | 3 => (uintBytes 8 g.d.toNat).toList
  | 4 => [if g.e then 1 else 0]

theorem sc_unmarshal_accept_spec_k (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (hL37f : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_37"))
    (hL3bf : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_3b"))
    (s : MachineData) (ra : UInt64) (slot c0 c1 c2 c3 c4 : List UInt8) (hsl : slot.length = 8)
    (g0 : c0.length = 1) (g1 : c1.length = 2) (g2 : c2.length = 4) (g3 : c3.length = 8) (g4 : c4.length = 1)
    (R : DataMem → Prop) (bs : Array UInt8) (v : Value) (hd : deserialize scDesc bs = .ok v)
    (hlen : s.regs.rcx.toNat = bs.size)
    (P : ∀ g : Scalars, bs = scEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
        ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
        ⋆ Eq ((scField g 0).At s.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rbx.toBitVec + 1))
        ⋆ Eq ((scField g 2).At (s.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (s.regs.rbx.toBitVec + 7))
        ⋆ Eq ((scField g 4).At (s.regs.rbx.toBitVec + 15))
        ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 2))
        ⋆ Eq (c2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 8))
        ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16)) ⋆ R) :
    ∃ g : Scalars, g.toValue = v ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((scField g 0).At s.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rax.toBitVec + 2))
          ⋆ Eq ((scField g 2).At (s.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((scField g 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((scField g 0).At s.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rbx.toBitVec + 1))
          ⋆ Eq ((scField g 2).At (s.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (s.regs.rbx.toBitVec + 7))
          ⋆ Eq ((scField g 4).At (s.regs.rbx.toBitVec + 15)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := Scalars.toValue) (enc := scEncode) scDesc_wellFormed
    sc_serialize (fun v h => sc_toValue_surjective v h) hd
  refine ⟨g, rfl, ?_⟩
  have h16 : s.regs.rcx = 16 := by
    rw [sc_encode_size] at hlen; exact UInt64.toNat_inj.mp hlen
  exact sc_accept_main k hk s ra slot (scField g 0) (scField g 1) (scField g 2) (scField g 3)
    (scField g 4) c0 c1 c2 c3 c4 hsl (by simp [scField, Spec.uintBytes_size]) (by simp [scField, Spec.uintBytes_size])
    (by simp [scField, Spec.uintBytes_size]) (by simp [scField, Spec.uintBytes_size]) rfl g0 g1 g2 g3 g4 R (P g rfl)
    hL37f hL3bf h16 (by cases g.e <;> simp [scField])

theorem scEncode_toList (g : Scalars) :
    (scEncode g).toList = scField g 0 ++ scField g 1 ++ scField g 2 ++ scField g 3 ++ scField g 4 := by
  simp [scEncode, scField]

/-- **Marshal fast path against EthLib.** If the receiver holds the Go layout of `g`
(fields as `scField g i`), MarshalSSZTo writes at `dst[len:]` the five chunks whose
concatenation is the EthLib serialization of `g.toValue`. -/
theorem sc_marshal_spec_k (k : Nat) (hk : ScalarsMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ScalarsMarshalSSZTo k) (g : Scalars)
    (s : MachineData) (ra guard : UInt64) (fp sp1 sp2 d0 d1 d2 d3 d4 pre : List UInt8)
    (hfp : fp.length = 8) (hs1 : sp1.length = 8) (hs2 : sp2.length = 8)
    (hd0 : d0.length = 1) (hd1 : d1.length = 2) (hd2 : d2.length = 4) (hd3 : d3.length = 8) (hd4 : d4.length = 1)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (sp2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((scField g 0).At s.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rax.toBitVec + 2))
      ⋆ Eq ((scField g 2).At (s.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((scField g 4).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 1))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 3)) ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 7))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 16 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    serialize scDesc g.toValue = .ok (scEncode g) ∧
    (scEncode g).toList = scField g 0 ++ scField g 1 ++ scField g 2 ++ scField g 3 ++ scField g 4 ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx = s.regs.rcx + 16 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((scField g 0).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ((scField g 1).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 1))
          ⋆ Eq ((scField g 2).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 3))
          ⋆ Eq ((scField g 3).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 7))
          ⋆ Eq ((scField g 4).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 15))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq ((scField g 0).At s.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rax.toBitVec + 2))
          ⋆ Eq ((scField g 2).At (s.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((scField g 4).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨sc_serialize g, scEncode_toList g,
    sc_marshal_main k hk hf s ra guard fp sp1 sp2 (scField g 0) (scField g 1) (scField g 2) (scField g 3)
      (scField g 4) d0 d1 d2 d3 d4 pre hfp hs1 hs2 (by simp [scField, Spec.uintBytes_size])
      (by simp [scField, Spec.uintBytes_size]) (by simp [scField, Spec.uintBytes_size])
      (by simp [scField, Spec.uintBytes_size]) hd0 hd1 hd2 hd3 hd4 R h_mem hguard hcap hcap63
      (by cases g.e <;> simp [scField])⟩
