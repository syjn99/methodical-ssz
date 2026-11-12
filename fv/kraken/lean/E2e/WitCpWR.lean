import E2e.CpWCover
import Fk.RtCopy
import Fk.WHost
import E2e.WitSplit

/-!
# Witness of `cp_e2e_marshal_reject_cover`: `len(Root) ≠ 32`, every capacity range

Host: data labels (the bump pointer, `ssz.ErrBytesLength` at 0x10008), the real Go 1.26.10
`(*v1alpha1.Checkpoint).MarshalSSZTo` (index 9) and `RtCopy` (index 100: `rt_growslice` — new capacity `2·newLen + 192` from the bump heap — and `rt_memmove`,
both with `S = 0`). One memory block at `0x10000`: bump pointer, the two `ssz.ErrBytesLength` words
(stand-ins 0x10e8, 0x2b: the real values are set by the runtime's init; non-nil-ness is not proved),
a 9000-byte heap, guard word (r14 = 0x12330), the 72-byte receiver (`Root` = (0x5000, rl, 48),
`rl ≠ 32`), the stack window (rsp = 0x12408) and `dst` at 0x12428 = a 30-byte prefix and `n` spare
bytes. Frame `R` = `emp`. Instances: n = 0 (cap = len: first growslice, then the reject), 3, 8
(cap = len + 8: no growth), 40; nil `dst`.
-/

open Fk Fk.W E2e E2e.Code EthLib.Serialization.Ssz

namespace E2e.WitCpWR

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "ssz.ErrBytesLength"]

def P : Program := dataLabels ++ CpMarshal ++ RtCopy

theorem P_len : P.length = 126 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : CpMarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels RtCopy (by simp [prog_eq, P, List.append_assoc]) rfl

theorem hk100 : RtCopy.IsInfixAt Host.prog 100 :=
  infixAt_of (dataLabels ++ CpMarshal) [] (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh CpMarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf100 : LabelsFresh RtCopy 100 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_ebl : label "ssz.ErrBytesLength" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt
def pre30 : List UInt8 := (List.range 30).map (fun i => UInt8.ofNat (0x40 + i))

/-- bump pointer · ErrBytesLength words · heap (9000) · guard · receiver (72) · rslot · growslice spill (40)
· l72 · t40 (16) · t30 (16) · l32 · l24 · l16 · fp · return slot · spill rax · spill rbx · spill rcx · dst. -/
def block (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x10018 : BitVec 64).toInt ++ (w 0x10e8 ++ (w 0x2b ++ (z 9000 ++ (w 0 ++ (z 8 ++ (e8 ++ (w 0x5000
    ++ (w rl ++ (w 48 ++ (z 32 ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 16 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (w 0
    ++ (z 8 ++ (z 8 ++ (z 8 ++ dst)))))))))))))))))))))))

def mem (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) : DataMem := (block e8 rl dst).At (0x10000 : BitVec 64)

def cs0 (e8 : List UInt8) (rl : UInt64) (dst : List UInt8) (rbx len cap : UInt64) (zmms : RegZmms) (flags : StatusFlags) :
    MachineData :=
  ⟨⟨0x12348, rbx, len, 0, 0, cap, 0x12408, 0, 0, 0, 0, 0, 0, 0, 0x12330, 0⟩, zmms, flags, mem e8 rl dst⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10018 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 9000).At (0x10018 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9000 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10018, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `cp_e2e_marshal_reject_cover`**, len 30, cap 30 + n (n ≤ 64). -/
theorem rej_runs (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32) (n : Nat) (hn : n ≤ 64)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl (pre30 ++ z n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags, Host.addrOf 9⟩ := by
  have hc : (UInt64.ofNat (30 + n)).toNat = 30 + n := by simp; omega
  refine eventually_mono (cp_e2e_marshal_reject_cover 9 hk9 hf9 (z 8) e8 (w 48) (z 32) pre30 (z n) rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (cs0 e8 rl (pre30 ++ z n) 0x12428 30 (UInt64.ofNat (30 + n)) zmms flags) 0 0 rfl (by simp only [cs0, hc]; simp [pre30])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl (pre30 ++ z n)).At (0x10000 : BitVec 64)) (mem e8 rl (pre30 ++ z n)) := rfl
      wit_split_n [he8, show pre30.length = 30 from rfl]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((w 0x2b).At _)) (Eq ((z 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((w 0x10e8).At _)) (Eq ((z 9000).At _))] at H
      have H2 := lift_heap H
      rw [at_app pre30 (z n) rfl (by simp [pre30]; omega)]
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show pre30.length = 30 from rfl, E2e.Data.e2eErrBytesLength_addr, label_ebl,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]; try omega) (by unfold maxAlloc; omega)
    (rt_growslice 100 hk100 hf100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

set_option maxHeartbeats 64000000 in
/-- **Non-vacuity of `cp_e2e_marshal_reject_cover`** (nil dst). -/
theorem rej_runs_nil (e8 : List UInt8) (he8 : e8.length = 8) (rl : UInt64) (hrl : rl ≠ 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨cs0 e8 rl [] 0 0 0 zmms flags, Host.addrOf 9⟩ := by
  refine eventually_mono (cp_e2e_marshal_reject_cover 9 hk9 hf9 (z 8) e8 (w 48) (z 32) [] [] rfl he8 rfl rfl
    0x5000 rl 0x10e8 0x2b hrl (cs0 e8 rl [] 0 0 0 zmms flags) 0 0 rfl rfl
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 16) (z 8) (z 40) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    Std.ExtHashMap.emp 0 [] rfl bumpHeap 9000
    (by
      have H : Eq ((block e8 rl []).At (0x10000 : BitVec 64)) (mem e8 rl []) := rfl
      wit_split_n [he8]
      rw [Std.ExtHashMap.sep_comm_l (Eq ((w 0x2b).At _)) (Eq ((z 9000).At _)),
        Std.ExtHashMap.sep_comm_l (Eq ((w 0x10e8).At _)) (Eq ((z 9000).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, w, nil_At_emp, List.nil_append, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep,
        show pre30.length = 30 from rfl, E2e.Data.e2eErrBytesLength_addr, label_ebl,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
        List.length_nil] at H2 ⊢
      generalize e8 = e8' at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) (by simp [cs0]) (by unfold maxAlloc; omega)
    (rt_growslice 100 hk100 hf100 _ 0)) ?_
  rintro st ⟨f1, f2, f3, f4, f5, f6, -⟩
  exact ⟨f1, f2, f3, f4, f5, f6⟩

/-- cap = len, len + 3 (first growslice, then the reject), len + 8, len + 40 (no growth); nil dst; rl = 31, 0, 33. -/
example (z' : RegZmms) (f : StatusFlags) := rej_runs (Int.toBytes 8 7) rfl 31 (by decide) 0 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := rej_runs (Int.toBytes 8 7) rfl 0 (by decide) 3 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := rej_runs (Int.toBytes 8 7) rfl 33 (by decide) 8 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := rej_runs (Int.toBytes 8 7) rfl 31 (by decide) 40 (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := rej_runs_nil (Int.toBytes 8 7) rfl 31 (by decide) z' f

end E2e.WitCpWR
