import Fk.ScSpec
import Fk.Contracts
import Fk.LuSpec
import Fk.Frame

/-!
# Function specifications for composition

A caller (Nested, ListC) uses each callee through a specification of the same
shape as a runtime contract: a hypothesis about the code at the callee's label,
for every machine state, return address and frame `F`.
-/

open Fk Fk.Code Fv1
variable [Host]

namespace Fk

/-- `runtime.newobject(typ *_type) unsafe.Pointer`: like `MakesliceC` for one
object of `sz` bytes (zeroed, carved from the heap); the spill area is the
8-byte slot of its one register argument; r14 and rbp are kept. -/
def NewobjectC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (sz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rax.toBitVec = ty → sz ≤ avail → stk.length = S → spill.length = 8 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((List.replicate sz 0).At st'.data.regs.rax.toBitVec)
          ⋆ Heap (avail - sz) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.newobject"⟩

def ScUAccC : Prop :=
  ∀ (st : MachineData) (ret : Int64) (g : Scalars) (slot c0 c1 c2 c3 c4 : List UInt8) (F : DataMem → Prop),
    slot.length = 8 → c0.length = 1 → c1.length = 2 → c2.length = 4 → c3.length = 8 → c4.length = 1 →
    st.regs.rcx = 16 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((scField g 0).At st.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rbx.toBitVec + 1))
      ⋆ Eq ((scField g 2).At (st.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (st.regs.rbx.toBitVec + 7))
      ⋆ Eq ((scField g 4).At (st.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ Eq (c1.At (st.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (st.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (st.regs.rax.toBitVec + 16)) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ (Eq ((scField g 0).At st.regs.rax.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rax.toBitVec + 2))
          ⋆ Eq ((scField g 2).At (st.regs.rax.toBitVec + 4)) ⋆ Eq ((scField g 3).At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((scField g 4).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((scField g 0).At st.regs.rbx.toBitVec) ⋆ Eq ((scField g 1).At (st.regs.rbx.toBitVec + 1))
          ⋆ Eq ((scField g 2).At (st.regs.rbx.toBitVec + 3)) ⋆ Eq ((scField g 3).At (st.regs.rbx.toBitVec + 7))
          ⋆ Eq ((scField g 4).At (st.regs.rbx.toBitVec + 15)) ⋆ F) st'.data.dmem)
      ⟨st, label "target.Scalars.UnmarshalSSZ"⟩

/-- The Scalars machine code satisfies its specification (no assumption). -/
theorem sc_uacc_holds (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ScalarsUnmarshalSSZ k) : ScUAccC := by
  intro st ret g slot c0 c1 c2 c3 c4 F hsl g0 g1 g2 g3 g4 hlen hm
  rw [label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  have h := sc_accept_main k hk st (UInt64.ofBitVec ret.toBitVec) slot (scField g 0) (scField g 1) (scField g 2)
    (scField g 3) (scField g 4) c0 c1 c2 c3 c4 hsl (by simp [scField, Fv.uintBytes_size])
    (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size])
    (by simp [scField, Fv.uintBytes_size]) rfl g0 g1 g2 g3 g4 F hm
    (fun i hi h => hf i hi _ h (by simp [ScalarsUnmarshalSSZ]))
    (fun i hi h => hf i hi _ h (by simp [ScalarsUnmarshalSSZ])) hlen (by cases g.e <;> simp [scField])
  simp only [Nat.add_zero] at h
  exact h

/-- ListU64.UnmarshalSSZ, accept path, on the Go encoding of `g` (at most 16
elements): one stack block of `144 + S` bytes below the return slot (its frame
and the makeslice scratch), two 8-byte argument spill slots above it. -/
def LuUAccC (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (g : ListU64) (stk sp1 sp2 cP cL cC : List UInt8) (guard : UInt64)
    (avail : Nat) (F : DataMem → Prop),
    g.ok → stk.length = 144 + S → sp1.length = 8 → sp2.length = 8 → cP.length = 8 → cL.length = 8 → cC.length = 8 →
    st.regs.rcx.toNat = 4 + 8 * g.l.length → st.regs.rcx.toNat ≤ st.regs.rdi.toNat →
    st.regs.rdi.toNat < 2 ^ 63 → guard.toNat < st.regs.rsp.toNat - 8 → 8 ≤ st.regs.rsp.toNat → 8 * 16 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp1.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (sp2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At st.regs.rbx.toBitVec) ⋆ Eq ((u64Bytes g.l).toList.At (st.regs.rbx.toBitVec + 4))
      ⋆ Eq (cP.At st.regs.rax.toBitVec) ⋆ Eq (cL.At (st.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (st.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (p : BitVec 64) (stk' sp1' sp2' : List UInt8), stk'.length = 144 + S ∧ sp1'.length = 8 ∧ sp2'.length = 8 ∧
        (Eq ((Int.toBytes 8 p.toInt).At st.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (g.l.length : Int)).At (st.regs.rax.toBitVec + 16)) ⋆ Eq ((u64Bytes g.l).toList.At p)
          ⋆ Heap (avail - 8 * g.l.length)
          ⋆ Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp1'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (sp2'.At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq ([4, 0, 0, 0].At st.regs.rbx.toBitVec) ⋆ Eq ((u64Bytes g.l).toList.At (st.regs.rbx.toBitVec + 4))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "target.ListU64.UnmarshalSSZ"⟩


set_option maxHeartbeats 8000000 in
/-- The ListU64 machine code satisfies its specification, given the makeslice contract. -/
theorem lu_uacc_holds (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k) (Heap : Nat → DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60)
    (hms : MakesliceC Heap (label "type__" + 49120).toBitVec 8 S) : LuUAccC Heap S := by
  intro st ret g stk s90 s98 cP cL cC guard avail F hg hstk h8 h9 hcP hcL hcC hlen hcap hcap63 hguard hsp hav hm
  rw [label_at hk hf (j := 0) (l := "target.ListU64.UnmarshalSSZ") (by rfl) (by intro i hi; omega)]
  obtain ⟨scratch, rslot, g1, s28, s30, s38, g2, fp, rfl, h0, h1, h2, h3, h4, h5, h6, h7⟩ :
      ∃ a b c d e f g h, stk = luFrame a b c d e f g h ∧ a.length = S ∧ b.length = 8 ∧ c.length = 40 ∧
        d.length = 8 ∧ e.length = 8 ∧ f.length = 8 ∧ g.length = 64 ∧ h.length = 8 :=
    ⟨_, _, _, _, _, _, _, _, luFrame_slices stk S, by simp; omega, by simp; omega, by simp; omega,
      by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩
  rw [luFrame_sep _ S hS _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7] at hm
  have hok : g.l.length ≤ 16 := hg
  have hg1 : Eq (g1.At (st.regs.rsp.toBitVec - 136)) = Eq ((g1.take 24).At (st.regs.rsp.toBitVec - 136))
      ⋆ Eq ((g1.drop 24).At (st.regs.rsp.toBitVec - 112)) := by
    conv => lhs; rw [← List.take_append_drop 24 g1]
    exact at_app _ _ (by simp [h2]; bv_omega) (by simp [h2])
  rw [hg1] at hm
  refine eventually_trans _ _ _ _ (lu_accept_main k hk hf (u64Bytes g.l).toList g.l.length (by simp [u64Bytes_size]) hok
    st (UInt64.ofBitVec ret.toBitVec) guard fp s28 s30 s38 s90 s98 rslot cP cL cC h7 h3 h4 h5 h8 h9 h1 hcP hcL hcC
    (Eq ((g1.drop 24).At (st.regs.rsp.toBitVec - 112)) ⋆ Eq (g2.At (st.regs.rsp.toBitVec - 72)) ⋆ F) S scratch (g1.take 24)
    h0 (by simp [h2]) Heap avail
    (by ecancel) hguard hsp hlen hcap hcap63 (by omega) hms) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrsp, hr14, p, fp', s28', s30', s38', s90', s98', rslot', scratch', spm',
    l1, l2, l3, l4, l5, l6, l7, l8, l9, hmem⟩
  refine Eventually.done _ ⟨hpc, hrax, hrbx, hrsp, hr14, p, luFrame scratch' rslot' (spm' ++ g1.drop 24) s28' s30' s38' g2 fp',
    s90', s98', by simp [luFrame, *]; omega, l5, l6, ?_⟩
  rw [luFrame_sep _ S hS _ _ _ _ _ _ _ _ l8 l7 (by simp [l9, h2]) l2 l3 l4 h6 l1,
    at_app spm' (g1.drop 24) (b := st.regs.rsp.toBitVec - 112) (by rw [l9]; bv_omega) (by simp [l9, h2])]
  ecancel

end Fk
