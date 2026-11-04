import Fk.ScAccept
import Fv1.SpecScalars
import Fv1.Transfer

/-!
# Scalars.UnmarshalSSZ against EthLib (Kraken main)

`sc_unmarshal_accept_spec_k`: if EthLib accepts `bs` as `v`, the machine code
returns nil and the receiver holds the Go layout of some `g` with `g.toValue = v`.
Same form as phase 1a `sc_unmarshal_accept_spec`: the machine precondition is
given for the `g` with `bs = scEncode g` (EthLib's acceptance picks it).

The Go layout of `Scalars` on amd64: A @0 (1 byte), B @2 (2, LE), C @4 (4, LE),
D @8 (8, LE), E @16 (1 byte, 0 or 1). `scField g i` is field `i` in that layout;
the bytes are EthLib's `uintBytes`, the same bytes as in `scEncode g`.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
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
        ∧ (Eq ((scField g 0).At s.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (s.regs.rax.toBitVec + 2))
          ⋆ Eq ((scField g 2).At (s.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((scField g 4).At (s.regs.rax.toBitVec + 16)) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := Scalars.toValue) (enc := scEncode) scDesc_wellFormed
    sc_serialize (fun v h => sc_toValue_surjective v h) hd
  refine ⟨g, rfl, ?_⟩
  have h16 : s.regs.rcx = 16 := by
    rw [sc_encode_size] at hlen; exact UInt64.toNat_inj.mp hlen
  exact sc_accept_main k hk s ra slot (scField g 0) (scField g 1) (scField g 2) (scField g 3)
    (scField g 4) c0 c1 c2 c3 c4 hsl (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size])
    (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size]) rfl g0 g1 g2 g3 g4 R (P g rfl)
    hL37f hL3bf h16 (by cases g.e <;> simp [scField])
