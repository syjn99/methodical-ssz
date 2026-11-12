import E2e.CpWCoverF
import E2e.WitCpW
import Machine.WitnessSplit

/-!
# Witness of `cp_e2e_marshal_cover_framed`: every capacity range on the `WitCpW` host

Same host, block, registers and instances as `E2e/WitCpW.lean` (the `WitCpW` Host is the only one in
scope, because two `Host` instances in one file make instance resolution unfold both programs): len 30, cap 30 + n (n ≤ 64), and nil `dst`. The witness conclusion names the capacity range
that the run takes (the range conjunct of each disjunct of the framed cover decides it):
n ≥ 40: disjunct (1), returned in place (`rax = dst`, `rcx = cap`); 8 ≤ n < 40: disjunct (2), returned
with `nextSliceCap 70 (30+n) ≤ rcx`; n < 8 and nil: disjunct (3A)/(3B) (return) or (3C) (entry of
the second growslice call).

Which of (3A)/(3B)/(3C) the run takes is not decidable through the contract: `GrowsliceC` hides the
capacity and the remaining heap that the runtime returns (it gives only bounds). With the witness model
`rt_growslice` (capacity `2·newLen + 192`) the real run takes (3A); this is a property of the model, not
of the theorem. The second-growth path (3B) on real Go 1.26.10 is differential only.
-/

open Machine Runtime TestTarget Machine.Witness E2e E2e.Code EthLib.Serialization.Ssz

namespace E2e.WitCpWF

open E2e.WitCpW

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `cp_e2e_marshal_cover_framed`**, len 30, cap 30 + n (n ≤ 64), with the reached range. -/
theorem covf_runs (g : PCp) (n : Nat) (hn : n ≤ 64) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧ bs.toList = (uintBytes 8 g.epoch.toNat).toList ++ g.root.toList ∧
    Eventually (step1 Host.exe)
      (fun st => (40 ≤ n → st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x12438
            ∧ st.data.regs.rbx.toNat = 70 ∧ st.data.regs.rcx.toNat = 30 + n)
        ∧ (8 ≤ n → n < 40 → st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 70
            ∧ nextSliceCap 70 (30 + n) ≤ st.data.regs.rcx.toNat)
        ∧ (n < 8 → (st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 70)
            ∨ (st.pc = label "runtime.growslice" ∧ st.data.regs.rbx.toNat = 70 ∧ st.data.regs.rdi.toNat = 32)))
      ⟨(cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n) 0x12438 30 (UInt64.ofNat (30 + n)) zmms flags), Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  have r30 : UInt64.toNat 30 = 30 := rfl
  obtain ⟨bs, hs, hbs, he⟩ := cp_e2e_marshal_cover_framed 8 hk8 hf8 g _ rfl (z 8) (w 32) (z 32) pre30 (z n) rfl rfl rfl
    0x12380 (cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n) 0x12438 30 (UInt64.ofNat (30 + n)) zmms flags) 0 0 rfl (by simp only [cs0, hc]; simp [pre30])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n)).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList (pre30 ++ z n)) := rfl
      wit_split_n [he8, hroot, show pre30.length = 30 from rfl]
      have H2 := lift_heap H
      rw [at_app pre30 (z n) rfl (by simp [pre30]; omega)]
      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, show pre30.length = 30 from rfl, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp only [cs0, hc]; omega) (by simp [cs0])
    (by unfold maxAlloc; omega) (rt_growslice 99 hk99 hf99 _ 0) (rt_memmove 99 hk99 hf99 0)
  refine ⟨bs, hs, hbs, eventually_mono he ?_⟩
  rintro st (⟨e1, e2, -, -, -, -, -, h⟩ | ⟨e1, c3, -, -, -, e6, e7, -⟩)
  · have e2' : st.data.regs.rbx.toNat = 70 := by rw [e2]; rfl
    rcases h with ⟨c1, e10, e11, -⟩ | ⟨c2, c2', hnc, -⟩ | ⟨c3, -⟩ | ⟨c3, -⟩
    · have c1' : 40 ≤ n := by simp only [cs0, hc, r30] at c1; omega
      refine ⟨fun _ => ⟨e1, e10, e2', by rw [e11]; exact hc⟩, fun _ h40 => by omega, fun h8 => by omega⟩
    · have c2a : 8 ≤ n := by simp only [cs0, hc, r30] at c2; omega
      have c2b : n < 40 := by simp only [cs0, hc, r30] at c2'; omega
      refine ⟨fun h40 => by omega, fun _ _ => ⟨e1, e2', ?_⟩, fun h8 => by omega⟩
      simp only [cs0, hc] at hnc; exact hnc
    · have c3' : n < 8 := by simp only [cs0, hc, r30] at c3; omega
      exact ⟨fun h40 => by omega, fun h8 => by omega, fun _ => Or.inl ⟨e1, e2'⟩⟩
    · have c3' : n < 8 := by simp only [cs0, hc, r30] at c3; omega
      exact ⟨fun h40 => by omega, fun h8 => by omega, fun _ => Or.inl ⟨e1, e2'⟩⟩
  · have c3' : n < 8 := by simp only [cs0, hc, r30] at c3; omega
    exact ⟨fun h40 => by omega, fun h8 => by omega, fun _ => Or.inr ⟨e1, by rw [e6]; rfl, e7⟩⟩

set_option maxHeartbeats 64000000 in
/-- Nil `dst` (rbx = 0, len = cap = 0): range (3) only. -/
theorem covf_runs_nil (g : PCp) (zmms : RegZmms) (flags : StatusFlags) :
    ∃ bs, serialize prysmCpDesc g.toValue = .ok bs ∧ bs.toList = (uintBytes 8 g.epoch.toNat).toList ++ g.root.toList ∧
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 40)
            ∨ (st.pc = label "runtime.growslice" ∧ st.data.regs.rbx.toNat = 40 ∧ st.data.regs.rdi.toNat = 32))
      ⟨(cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags), Host.addrOf 8⟩ := by
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  obtain ⟨bs, hs, hbs, he⟩ := cp_e2e_marshal_cover_framed 8 hk8 hf8 g _ rfl (z 8) (w 32) (z 32) [] [] rfl rfl rfl
    0x12380 (cs0 (uintBytes 8 g.epoch.toNat).toList g.root.toList [] 0 0 0 zmms flags) 0 0 rfl rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block (uintBytes 8 g.epoch.toNat).toList g.root.toList []).At (0x10000 : BitVec 64))
        (mem (uintBytes 8 g.epoch.toNat).toList g.root.toList []) := rfl
      wit_split_n [he8, hroot]
      have H2 := lift_heap H
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, show Int.toBytes 8 (32#64).toInt = Int.toBytes 8 32 by decide, show pre30.length = 30 from rfl, Std.ExtHashMap.emp_sep,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize (uintBytes 8 g.epoch.toNat).toList = e8 at H2 ⊢
      generalize g.root.toList = root at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by simp [cs0])
    (by unfold maxAlloc; omega) (rt_growslice 99 hk99 hf99 _ 0) (rt_memmove 99 hk99 hf99 0)
  refine ⟨bs, hs, hbs, eventually_mono he ?_⟩
  rintro st (⟨e1, e2, -, -, -, -, -, -⟩ | ⟨e1, -, -, -, -, e6, e7, -⟩)
  · exact Or.inl ⟨e1, by rw [e2]; rfl⟩
  · exact Or.inr ⟨e1, by rw [e6]; rfl, e7⟩

/-- cap = len (30), len + 3, len + 8, len + 39, len + 40; nil dst. -/
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs g 0 (by decide) z' f
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs g 3 (by decide) z' f
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs g 8 (by decide) z' f
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs g 39 (by decide) z' f
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs g 40 (by decide) z' f
example (g : PCp) (z' : RegZmms) (f : StatusFlags) := covf_runs_nil g z' f

end E2e.WitCpWF
