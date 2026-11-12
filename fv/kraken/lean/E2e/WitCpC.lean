import E2e.CpCompose
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost
import E2e.GoVal

/-!
# Witness of `cp_e2e_unmarshal_then_marshal` (machine-level composition, one Host for decoder and encoder)

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).UnmarshalSSZ`
(index 9), the real `(*primitives.Epoch).UnmarshalSSZ` (index 117), the 1-byte
bump `runtime.makeslice` (index 180, `bump_makeslice1`), `RtCopy` (index 186,
`rt_memmove`) and the real `(*v1alpha1.Checkpoint).MarshalSSZTo` (index 212).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 32-byte
heap, guard word, the 40 input bytes, the 72-byte receiver (all zero: a fresh
`&Checkpoint{}`), the 144-byte stack window (rsp = 0x1011c, decoder scratch
`S = 24`, encoder scratch 0) and `dst` at 0x10134 = prefix `[0xaa, 0xbb, 0xcc]`,
40 old bytes, 5 spare bytes (`cap = 48`). The frame `R0` is the spare capacity.
The middle state is a real memory: the decoder's final memory with the
encoder's return address (`ra2 = 0`) stored into the return slot
(`Mem.storeInt`).
-/

open Fk Fk.W E2e E2e.Code

namespace E2e.WitCpC

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := dataLabels ++ CpUnmarshal ++ EpUnmarshal ++ BumpAlloc1 ++ RtCopy ++ CpMarshal

theorem P_len : P.length = 303 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : CpUnmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (EpUnmarshal ++ BumpAlloc1 ++ RtCopy ++ CpMarshal) (by simp [prog_eq, P, List.append_assoc]) rfl

theorem hk117 : EpUnmarshal.IsInfixAt Host.prog 117 :=
  infixAt_of (dataLabels ++ CpUnmarshal) (BumpAlloc1 ++ RtCopy ++ CpMarshal) (by simp [prog_eq, P, List.append_assoc])
    (by rfl)

theorem hk180 : BumpAlloc1.IsInfixAt Host.prog 180 :=
  infixAt_of (dataLabels ++ CpUnmarshal ++ EpUnmarshal) (RtCopy ++ CpMarshal) (by simp [prog_eq, P, List.append_assoc])
    (by rfl)

theorem hk186 : RtCopy.IsInfixAt Host.prog 186 :=
  infixAt_of (dataLabels ++ CpUnmarshal ++ EpUnmarshal ++ BumpAlloc1) CpMarshal (by simp [prog_eq, P, List.append_assoc])
    (by rfl)

theorem hk212 : CpMarshal.IsInfixAt Host.prog 212 :=
  infixAt_of (dataLabels ++ CpUnmarshal ++ EpUnmarshal ++ BumpAlloc1 ++ RtCopy) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh CpUnmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf117 : LabelsFresh EpUnmarshal 117 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf186 : LabelsFresh RtCopy 186 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf212 : LabelsFresh CpMarshal 212 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf180 : ∀ i < 180, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt
abbrev pre : List UInt8 := [0xaa, 0xbb, 0xcc]

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (32) · guard · input (40) · receiver (72)
· stack window: scratch (24) · rslot · m0 · m1 · m2 · g64 (16) · l30 · l28 · l20 · g24 · g16 · fp ·
return slot · spill rax · spill rbx · dst: prefix (3) · d0 (8) · d1 (32) · spare (5). -/
def block (e8 root : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (z 32 ++ (w0 ++ (e8 ++ (root ++ (z 8 ++ (z 8 ++ (z 8
    ++ (z 8 ++ (z 8 ++ (z 32 ++ (z 24 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8
    ++ (z 8 ++ (z 8 ++ (z 8 ++ (w0 ++ (z 8 ++ (z 8 ++ (pre ++ (z 8 ++ (z 32 ++ z 5)))))))))))))))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def cs0 (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005c, 0x10034, 40, 0, 0, 0, 0x1011c, 0, 0, 0, 0, 0, 0, 0, 0x1001c, 0⟩, zmms, flags, mem e8 root⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z 32).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 32 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `cp_e2e_unmarshal_then_marshal`.** Every premise holds in
this one host; the decoder returns nil; from the real middle memory (return
slot rewritten with `ra2 = 0`) the encoder returns `(0x10134, 3 + 40, 48, nil)`
and `dst[3..43]` = the 40 input bytes `e8 ++ root`. -/
theorem cp_compose_runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        Eventually (step1 Host.exe)
          (fun st' => st'.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st'.data.regs.rax = 0x10134
            ∧ st'.data.regs.rbx.toNat = (3 : UInt64).toNat + 40 ∧ st'.data.regs.rcx = 48
            ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0 ∧
            (Eq (pre.At (0x10134 : UInt64).toBitVec)
              ⋆ Eq ((e8 ++ root).At ((0x10134 : UInt64).toBitVec + (3 : UInt64).toBitVec))
              ⋆ Eq ((e8 ++ root).At (cs0 e8 root zmms flags).regs.rbx.toBitVec) ⋆ fun _ => True) st'.data.dmem)
          ⟨⟨{ st.data.regs with rax := (cs0 e8 root zmms flags).regs.rax, rbx := 0x10134, rcx := 3, rdi := 48, rsp := (cs0 e8 root zmms flags).regs.rsp },
              zmms, flags,
            st.data.dmem.storeInt (cs0 e8 root zmms flags).regs.rsp.toBitVec 8 (0 : UInt64).toBitVec.toInt⟩,
            Host.addrOf 212⟩)
      ⟨cs0 e8 root zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (cp_e2e_unmarshal_then_marshal 9 hk9 hf9 117 hk117 hf117 212 hk212 hf212 e8 root he8 hroot
    (cs0 e8 root zmms flags) 0 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 32)
    (z 8) (z 8) (z 16) pre (z 8) (z 32)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    0x10134 3 48 rfl (by decide) (by decide)
    (Eq ((z 5).At (0x1015f : BitVec 64))) 24 (by omega) (by decide) (z 24) rfl
    bumpHeap 32
    (by
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      wit_split [he8, hroot]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z 32).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) (by simp [cs0]) rfl (by omega) (bump_makeslice1 180 hk180 hf180 _) (rt_memmove 186 hk186 hf186 24)
    (rt_memmove 186 hk186 hf186 _))
    (fun st h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2
      (st.data.dmem.storeInt (cs0 e8 root zmms flags).regs.rsp.toBitVec 8 (0 : UInt64).toBitVec.toInt) zmms flags
        (fun F hF => Mem.storeInt_sep _ 8 _ F _ ⟨hF, Int.toBytes_length 8 _⟩ _)⟩)

/-- epoch 0 / root 0; a representative value and pattern root; 2^64 − 1 and 0xff root. -/
example (z' : RegZmms) (f : StatusFlags) := cp_compose_runs (Int.toBytes 8 0) (z 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  cp_compose_runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  cp_compose_runs (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

/-- Go-value element: the receiver of this witness (offset 0x5c of the block) is a zero `Checkpoint`
before the decoder; the receiver that the encoder reads is the decoder conclusion's fragments
`cpAfterDecode` over it, a Go value for every `p ≠ 0`. Layout: `E2e.cpGoFields`
(IR; trust note in `E2e.GoVal`). -/
theorem witCpC_recv (p : BitVec 64) (hp : p ≠ 0) :
    cpGoValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c) = true
    ∧ cpGoValue (cpAfterDecode (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c)
      (Int.toBytes 8 0x0123456789abcdef) p) = true :=
  have h : cpGoValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c) = true := by
    decide
  ⟨h, cp_after_decode_goValue _ _ h (by decide) p hp⟩

end E2e.WitCpC
