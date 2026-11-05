import Fk

open Fk Fk.Code Std Std.ExtHashMap

set_option linter.unusedVariables false

namespace ReviewKraken

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

-- A 2^64-byte block owns every 64-bit address, including any return slot.
theorem full_block_mem (p a : BitVec 64) :
    a ∈ (List.replicate (2^64) (0 : UInt8)).At p := by
  rw [mem_At_iff]
  refine ⟨(a - p).toNat, ?_, ?_⟩
  · simpa only [List.length_replicate] using (a - p).isLt
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem no_return_and_full (a p : BitVec 64) (ret : Int64) (F : DataMem → Prop) (m : DataMem)
    (h : (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At a) ⋆
      Eq ((List.replicate (2^64) 0).At p) ⋆ F) m) : False := by
  have h' : (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At a) ⋆
      (Eq ((List.replicate (2^64) 0).At p) ⋆ F)) m := by ecancel
  rcases h' with ⟨m1, m2, _, hd, rfl, m3, m4, hu, _, rfl, _⟩
  have h1 : a ∈ (Int.toBytes 8 ret.toBitVec.toInt).At a := by
    rw [mem_At_iff]
    exact ⟨0, by simp [Int.toBytes_length], by simp⟩
  have h2 : a ∈ m2 := by
    rw [← hu, union_eq, mem_union_iff]
    exact Or.inl (full_block_mem p a)
  exact (eq_empty_iff_forall_not_mem.mp hd a) (mem_inter_iff.mpr ⟨h1, h2⟩)

theorem sep_swap_middle (A B C F : DataMem → Prop) (m : DataMem)
    (h : (A ⋆ B ⋆ C ⋆ F) m) : (A ⋆ C ⋆ (B ⋆ F)) m := by ecancel

-- This is exactly LuAccept.lean's hms, named only to inspect its quantifiers.
def Hms [Host] (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (cnt : Nat) (stk : List UInt8) (F : DataMem → Prop),
      st.regs.rbx.toNat = cnt → st.regs.rcx.toNat = cnt → stk.length = S →
      (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ F) st.dmem →
      Eventually (step1 Host.exe)
        (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
          ∃ stk' : List UInt8, stk'.length = S ∧
          (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
            ⋆ Eq ((List.replicate (8 * cnt) 0).At st'.data.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
        ⟨st, label "runtime.makeslice"⟩

theorem hms_contradiction [Host] (S : Nat) (hms : Hms S)
    (st : MachineData) (ret : Int64) (stk : List UInt8) (F : DataMem → Prop)
    (hlen : stk.length = S)
    (hm : (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆
      Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ F) st.dmem) : False := by
  let st0 := { st with regs := { st.regs with rbx := UInt64.ofNat (2^61), rcx := UInt64.ofNat (2^61) } }
  have hr := hms st0 ret (2^61) stk F (by change (UInt64.ofNat (2^61)).toNat = 2^61; decide) (by change (UInt64.ofNat (2^61)).toNat = 2^61; decide) hlen hm
  obtain ⟨out, _, _, stk', _, hout⟩ := eventually_has_post _ _ _ hr
  have hmul : 8 * 2^61 = 2^64 := by decide
  rw [hmul] at hout
  exact no_return_and_full _ _ ret _ _ (sep_swap_middle _ _ _ _ _ hout)


theorem hms_contradiction_with_scratch [Host] (S : Nat) (hms : Hms S)
    (a : BitVec 64) (slot scratch : List UInt8) (F : DataMem → Prop) (m : DataMem)
    (hslot : slot.length = 8) (hsc : scratch.length = S)
    (hm : (Eq (slot.At a) ⋆ Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ F) m) : False := by
  have hm' : (Eq (slot.At a) ⋆ (Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ F)) m := by ecancel
  have hout := Mem.storeInt_sep a 8 slot _ m ⟨hm', hslot⟩ 0
  let st : MachineData := { regs := { rsp := UInt64.ofBitVec a }, dmem := Mem.storeInt m a 8 0 }
  apply hms_contradiction S hms st 0 scratch F hsc
  change (Eq ((Int.toBytes 8 0).At a) ⋆ Eq (scratch.At (a - BitVec.ofNat 64 S)) ⋆ F) _
  rw [sep_assoc]
  exact hout

variable [Host]

theorem lu_accept_preconditions_false (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (bs : List UInt8) (n : Nat) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (s : MachineData) (ra guard : UInt64)
    (fp s28 s30 s38 s90 s98 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h28 : s28.length = 8) (h30 : s30.length = 8) (h38 : s38.length = 8)
    (h90 : s90.length = 8) (h98 : s98.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s28.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (s30.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (s38.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (s90.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s98.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq (bs.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R))
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + 8 * n) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    -- Contract of runtime.makeslice (Go ABIInternal: rax = type, rbx = len, rcx = cap; result rax):
    -- given the return address at rsp and S bytes of stack below it, it returns to that address
    -- with rsp + 8, leaves every other chunk F unchanged, and gives a fresh zeroed block.
    (hms : ∀ (st : MachineData) (ret : Int64) (cnt : Nat) (stk : List UInt8) (F : DataMem → Prop),
      st.regs.rbx.toNat = cnt → st.regs.rcx.toNat = cnt → stk.length = S →
      (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ F) st.dmem →
      Eventually (step1 Host.exe)
        (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
          ∃ stk' : List UInt8, stk'.length = S ∧
          (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec) ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
            ⋆ Eq ((List.replicate (8 * cnt) 0).At st'.data.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
        ⟨st, label "runtime.makeslice"⟩) : False := by
  have hp : (Eq (rslot.At (s.regs.rsp.toBitVec - 144)) ⋆
      Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ fun _ => True) s.dmem :=
    sep_true (by ecancel)
  exact hms_contradiction_with_scratch S hms _ rslot scratch _ s.dmem hrs hsc hp

-- Separation permits a mapped address zero. It is not an OS validity predicate.
omit [Host] in
theorem nil_chunk_is_separable : ∃ m : DataMem,
    (Eq ([1].At (0 : BitVec 64)) ⋆ Eq ([2].At (4096 : BitVec 64))) m := by
  exact ⟨_, _, _, rfl, by simp [eq_empty_iff_forall_not_mem, mem_inter_iff, mem_At_iff, Nat.lt_one_iff], rfl, rfl⟩

#print axioms hms_contradiction
#print axioms lu_accept_preconditions_false
#print axioms nil_chunk_is_separable
end ReviewKraken
