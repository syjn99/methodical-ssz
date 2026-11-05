import Fk

open Fk Fk.Code Std Std.ExtHashMap Fv1 EthLib.Serialization.Ssz

set_option linter.unusedVariables false

namespace Review1b

-- Every successful omni-execution reaches a state. Undefined choices have inhabitants.
theorem all_has_post (e : Effects) (P : MachineState → Prop) (h : e.All P) : ∃ s, P s := by
  induction e with
  | done s => exact ⟨s, h⟩
  | unimplemented _ => exact False.elim h
  | gp_unaligned _ _ => exact False.elim h
  | nonmem_load _ _ _ _ _ => exact False.elim h
  | nonmem_store _ _ _ _ _ => exact False.elim h
  | @undefined α t cont ih => exact ih (t.from_hash 0) (h (t.from_hash 0))
  | require_read_access _ cont ih => exact ih () h
  | require_write_access _ cont ih => exact ih () h
  | require_exec_access _ cont ih => exact ih () h

theorem eventually_has_post [Layout] (e : Executable) (P : MachineState → Prop) (s : MachineState)
    (h : Eventually (step1 e) P s) : ∃ t, P t := by
  induction h with
  | done s hp => exact ⟨s, hp⟩
  | step s mid ht _ ih =>
    obtain ⟨t, hp⟩ := all_has_post _ _ ht
    exact ih t hp

theorem growslice_false [Host] (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat)
    (hg : GrowsliceC Heap ty esz S)
    (st : MachineData) (ret : Int64) (stk : List UInt8) (avail : Nat) (F : DataMem → Prop)
    (hlen : stk.length = S)
    (hm : (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆
      Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) st.dmem) : False := by
  let st0 := { st with regs := { st.regs with rsi := UInt64.ofBitVec ty, rbx := UInt64.ofNat (2^63), rdi := UInt64.ofNat (2^63) } }
  have hmem : (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st0.regs.rsp.toBitVec) ⋆
      Eq (stk.At (st0.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (([] : List UInt8).At st0.regs.rax.toBitVec) ⋆ Heap avail ⋆ F) st0.dmem := by
    simpa only [Fk.Witness.nil_At_emp, sep_emp] using hm
  have hr := hg st0 ret [] stk avail F (by simp [st0]) (by exact Nat.le_refl _) (by simp [st0]) hlen hmem
  obtain ⟨out, ho⟩ := eventually_has_post _ _ _ hr
  have hle := ho.2.2.2.2.1
  have hlt := ho.2.2.2.2.2.1
  change (UInt64.ofNat (2^63)).toNat ≤ out.data.regs.rcx.toNat at hle
  have hn : (UInt64.ofNat (2^63)).toNat = 2^63 := by decide
  rw [hn] at hle
  omega

theorem growslice_false_with_slot [Host] (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat)
    (hg : GrowsliceC Heap ty esz S) (a : BitVec 64) (slot scratch : List UInt8)
    (avail : Nat) (F : DataMem → Prop) (m : DataMem)
    (hslot : slot.length = 8) (hsc : scratch.length = S)
    (hm : (Eq (slot.At a) ⋆ Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) m) : False := by
  have hm' : (Eq (slot.At a) ⋆ (Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F)) m := by ecancel
  have hout := Mem.storeInt_sep a 8 slot _ m ⟨hm', hslot⟩ 0
  let st : MachineData := { regs := { rsp := UInt64.ofBitVec a }, dmem := Mem.storeInt m a 8 0 }
  apply growslice_false Heap ty esz S hg st 0 scratch avail F hsc
  change (Eq ((Int.toBytes 8 0).At a) ⋆ Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) _
  ecancel

variable [Host]

theorem bl_accept_main_preconditions_false (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (tl : List UInt8) (hn1 : 1 ≤ tl.length) (hval : blValid tl)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 s24 l32 l40 l48 l56 l64 l72 l80 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h8 : s8.length = 8) (h16 : s16.length = 8) (h24 : s24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl80 : l80.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq (tl.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + tl.length) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hvb : ValidateBitlistC S) (hgs : GrowsliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S) : False := by
  apply growslice_false_with_slot Heap _ 1 S hgs (s.regs.rsp.toBitVec - 128) rslot scratch avail (fun _ => True) s.dmem hrs hsc
  exact sep_true (by ecancel)

theorem bl_unmarshal_accept_spec_k_preconditions_false (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize blDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 s24 l32 l40 l48 l56 l64 l72 l80 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h8 : s8.length = 8) (h16 : s16.length = 8) (h24 : s24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl80 : l80.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : BitLG, bsA = blEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((packBitsDelimited g.1).toList.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hvb : ValidateBitlistC S) (hgs : GrowsliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S) : False := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := blToValue) (enc := blEncode) blDesc_wellFormed bl_serialize bl_toValue_surjective hd
  have h_mem := P g rfl
  apply growslice_false_with_slot Heap _ 1 S hgs (s.regs.rsp.toBitVec - 128) rslot scratch avail (fun _ => True) s.dmem hrs hsc
  exact sep_true (by ecancel)

theorem lum_grow_site_preconditions_false (k : Nat) (hk : ListU64MarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64MarshalSSZTo k)
    (pre : List UInt8) (s : MachineData) (hpre : pre.length = s.regs.rcx.toNat)
    (hrdx : s.regs.rdx.toNat = s.regs.rcx.toNat + 4)
    (sl rslot : List UInt8) (hsl : sl.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq (sl.At (s.regs.rsp.toBitVec + 112)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 8#64))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 8#64 - BitVec.ofNat 64 S))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hgs : GrowsliceC Heap (label "type__" + 48736).toBitVec 1 S) : False := by
  apply growslice_false_with_slot Heap _ 1 S hgs (s.regs.rsp.toBitVec - 8#64) rslot scratch avail (fun _ => True) s.dmem hrs hsc
  exact sep_true (by ecancel)

#print axioms growslice_false
#print axioms bl_accept_main_preconditions_false
#print axioms bl_unmarshal_accept_spec_k_preconditions_false
#print axioms lum_grow_site_preconditions_false
end Review1b
