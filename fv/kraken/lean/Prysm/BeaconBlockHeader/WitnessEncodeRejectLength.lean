import Prysm.BeaconBlockHeader.EncodeRejectLength
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of `Encode.reject_length_parent_root`, `Encode.reject_length_state_root`, `Encode.reject_length_body_root` (BeaconBlockHeader encoder, length rejects)

Hand-written (the text of `Prysm/Checkpoint/WitnessEncodeRejectLength.lean` and `Prysm/BeaconBlockHeader/WitnessEncodeFastPath.lean` with this layout).
Host: the label `ssz.ErrBytesLength` (index 0), the real Go 1.26.10
`(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` (index 1) and `MemmoveGrowsliceModel` (index 196, `model_memmove`, S = 0).
One memory block at `0x10000`: the two words of `ssz.ErrBytesLength` (stand-in values 0x10e8, 0x2b: the real
ones are set by the runtime's init), the guard word (r14 = 0x10000), the 128-byte receiver at 0x10018
(`state` 0, Slot, ProposerIndex, three root headers, 32-byte tail), the three 32-byte arrays (0x10098,
0x100b8, 0x100d8), the stack window (rsp = 0x101a0) and `dst` at 0x101b8 with `len = 0`, `cap = 112`.
In witness `n` the header of root `n` is `(p, rl, c)` with any pointer word `p`, any length `rl ≠ 32` and
any capacity word `c`; the other two headers are `(array, 32, 32)`. The instances at the end take Go
values for root `n`: the nil slice `(0, 0, 0)` and `(array, 31, 32)`. For a general `(p, rl, c)` the
receiver need not be a Go value (the theorem does not read the capacity word or the array).
The frame `R` is every piece of the block that the theorem does not name.
-/

open Machine Runtime Machine.Witness Codec Prysm.BeaconBlockHeader.Code

namespace Prysm.BeaconBlockHeader.Witness.EncodeRejectLength

set_option maxRecDepth 100000

def program : Program := [.label "ssz.ErrBytesLength"] ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 222 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_1 : marshalSSZTo.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "ssz.ErrBytesLength"] MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_196 : MemmoveGrowsliceModel.IsInfixAt Host.prog 196 :=
  infixAt_of ([.label "ssz.ErrBytesLength"] ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_1 : LabelsFresh marshalSSZTo 1 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_196 : LabelsFresh MemmoveGrowsliceModel 196 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_err_bytes_length : label "ssz.ErrBytesLength" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program]) (by simp [labs])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrBytesLength words · guard · receiver (`state`, Slot, ProposerIndex, three root headers `h1 h2 h3` =
pointer, length, capacity words; 32-byte tail) · r1 · r2 · r3 · rslot · gap (56) · l104 · l96 · t2a · t2b ·
t1a · t1b · gap (8) · l16 · fp · return slot · spill rax · spill rbx · dst = d0 (8) · d1 (8) · d2 (32) ·
d3 (32) · d4 (32). -/
def block (sl pi h1p h1l h1c h2p h2l h2c h3p h3l h3c r1 r2 r3 : List UInt8) : List UInt8 :=
  word_bytes 0x10e8 ++ (word_bytes 0x2b ++ (word_bytes 0 ++ (zeros 8 ++ (sl ++ (pi ++ (h1p ++ (h1l ++ (h1c ++ (h2p ++ (h2l ++ (h2c ++ (h3p ++ (h3l ++ (h3c ++ (zeros 32 ++ (r1 ++ (r2 ++ (r3 ++ (zeros 8 ++ (zeros 56 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 32 ++ (zeros 32)))))))))))))))))))))))))))))))))))))

def mem (sl pi h1p h1l h1c h2p h2l h2c h3p h3l h3c r1 r2 r3 : List UInt8) : DataMem :=
  (block sl pi h1p h1l h1c h2p h2l h2c h3p h3l h3c r1 r2 r3).At (0x10000 : BitVec 64)

def initial_state (m : DataMem) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10018, 0x101b8, 0, 0, 0, 112, 0x101a0, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, m⟩

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length_parent_root`**: ParentRoot = `(p, rl, c)` with `rl ≠ 32`. -/
theorem runs_parent_root (sl pi r1 r2 r3 c : List UInt8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32) (hc : c.length = 8)
    (p rl : UInt64) (hrl : rl ≠ 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state (mem sl pi (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length_parent_root 1 placed_at_1 labels_fresh_at_1 sl pi [] (zeros 8) (zeros 8) hsl hpi rfl rfl
    p.toBitVec rl hrl (initial_state (mem sl pi (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) zmms flags) 0 0 0x10e8 0x2b rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ Eq ((c).At (0x10040 : BitVec 64)) ⋆ Eq ((word_bytes 0x100b8).At (0x10048 : BitVec 64)) ⋆ Eq ((Int.toBytes 8 32).At (0x10050 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10058 : BitVec 64)) ⋆ Eq ((word_bytes 0x100d8).At (0x10060 : BitVec 64)) ⋆ Eq ((Int.toBytes 8 32).At (0x10068 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10070 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10078 : BitVec 64)) ⋆ Eq ((r1).At (0x10098 : BitVec 64)) ⋆ Eq ((r2).At (0x100b8 : BitVec 64)) ⋆ Eq ((r3).At (0x100d8 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100f8 : BitVec 64)) ⋆ Eq ((zeros 56).At (0x10100 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10138 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10140 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10188 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10190 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x101c8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x101e8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10208 : BitVec 64)))
    (by
      have H : Eq ((block sl pi (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3).At (0x10000 : BitVec 64))
        (mem sl pi (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) := rfl
      witness_split [hsl, hpi, hr1, hr2, hr3, hc]
      simp only [initial_state, word_bytes, label_err_bytes_length, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (q : UInt64) → q.toBitVec = q.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

/-- Root 1 = the nil slice. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_parent_root (Int.toBytes 8 7) (Int.toBytes 8 9) (zeros 32) (zeros 32) (zeros 32) (zeros 8) (by decide) (by decide) rfl rfl rfl rfl
    0 0 (by decide) z' f
/-- Root 1 = `(array, 31, 32)`. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_parent_root (Int.toBytes 8 (2 ^ 64 - 1)) (Int.toBytes 8 0) (List.replicate 32 0x11) (List.replicate 32 0x22)
    (List.replicate 32 0x33) (word_bytes 32) (by decide) (by decide) rfl rfl rfl (Int.toBytes_length 8 _)
    0x10098 31 (by decide) z' f

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length_state_root`**: StateRoot = `(p, rl, c)` with `rl ≠ 32`. -/
theorem runs_state_root (sl pi r1 r2 r3 c : List UInt8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32) (hc : c.length = 8)
    (p rl : UInt64) (hrl : rl ≠ 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length_state_root 1 placed_at_1 labels_fresh_at_1 sl pi [] (zeros 8) (zeros 8) r1 (zeros 32) hsl hpi rfl rfl hr1 rfl
    0x10098 p.toBitVec rl hrl (initial_state (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) zmms flags) 0 0 0x10e8 0x2b rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10040 : BitVec 64)) ⋆ Eq ((c).At (0x10058 : BitVec 64)) ⋆ Eq ((word_bytes 0x100d8).At (0x10060 : BitVec 64)) ⋆ Eq ((Int.toBytes 8 32).At (0x10068 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10070 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10078 : BitVec 64)) ⋆ Eq ((r2).At (0x100b8 : BitVec 64)) ⋆ Eq ((r3).At (0x100d8 : BitVec 64)) ⋆ Eq ((zeros 56).At (0x10100 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10188 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x101e8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10208 : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3).At (0x10000 : BitVec 64))
        (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) (word_bytes 0x100d8) (Int.toBytes 8 32) (word_bytes 32) r1 r2 r3) := rfl
      witness_split [hsl, hpi, hr1, hr2, hr3, hc]
      simp only [initial_state, word_bytes, label_err_bytes_length, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (q : UInt64) → q.toBitVec = q.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 196 placed_at_196 labels_fresh_at_196 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

/-- Root 2 = the nil slice. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_state_root (Int.toBytes 8 7) (Int.toBytes 8 9) (zeros 32) (zeros 32) (zeros 32) (zeros 8) (by decide) (by decide) rfl rfl rfl rfl
    0 0 (by decide) z' f
/-- Root 2 = `(array, 31, 32)`. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_state_root (Int.toBytes 8 (2 ^ 64 - 1)) (Int.toBytes 8 0) (List.replicate 32 0x11) (List.replicate 32 0x22)
    (List.replicate 32 0x33) (word_bytes 32) (by decide) (by decide) rfl rfl rfl (Int.toBytes_length 8 _)
    0x100b8 31 (by decide) z' f

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `Encode.reject_length_body_root`**: BodyRoot = `(p, rl, c)` with `rl ≠ 32`. -/
theorem runs_body_root (sl pi r1 r2 r3 c : List UInt8) (hsl : sl.length = 8) (hpi : pi.length = 8)
    (hr1 : r1.length = 32) (hr2 : r2.length = 32) (hr3 : r3.length = 32) (hc : c.length = 8)
    (p rl : UInt64) (hrl : rl ≠ 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = 0x10e8 ∧ st.data.regs.rsi = 0x2b)
      ⟨initial_state (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) r1 r2 r3) zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Encode.reject_length_body_root 1 placed_at_1 labels_fresh_at_1 sl pi [] (zeros 8) (zeros 8) r1 (zeros 32) r2 (zeros 32) hsl hpi rfl rfl hr1 rfl hr2 rfl
    0x10098 0x100b8 p.toBitVec rl hrl (initial_state (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) r1 r2 r3) zmms flags) 0 0 0x10e8 0x2b rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10040 : BitVec 64)) ⋆ Eq ((word_bytes 32).At (0x10058 : BitVec 64)) ⋆ Eq ((c).At (0x10070 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10078 : BitVec 64)) ⋆ Eq ((r3).At (0x100d8 : BitVec 64)) ⋆ Eq ((zeros 56).At (0x10100 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10188 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10208 : BitVec 64)))
    0 [] rfl
    (by
      have H : Eq ((block sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) r1 r2 r3).At (0x10000 : BitVec 64))
        (mem sl pi (word_bytes 0x10098) (Int.toBytes 8 32) (word_bytes 32) (word_bytes 0x100b8) (Int.toBytes 8 32) (word_bytes 32) (word_bytes p) (word_bytes rl) (c) r1 r2 r3) := rfl
      witness_split [hsl, hpi, hr1, hr2, hr3, hc]
      simp only [initial_state, word_bytes, label_err_bytes_length, nil_At_emp, Std.ExtHashMap.sep_emp,
        Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, show (UInt64.ofNat 0).toBitVec = 0#64 from rfl,
        show (q : UInt64) → q.toBitVec = q.toBitVec from fun _ => rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 196 placed_at_196 labels_fresh_at_196 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

/-- Root 3 = the nil slice. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_body_root (Int.toBytes 8 7) (Int.toBytes 8 9) (zeros 32) (zeros 32) (zeros 32) (zeros 8) (by decide) (by decide) rfl rfl rfl rfl
    0 0 (by decide) z' f
/-- Root 3 = `(array, 31, 32)`. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs_body_root (Int.toBytes 8 (2 ^ 64 - 1)) (Int.toBytes 8 0) (List.replicate 32 0x11) (List.replicate 32 0x22)
    (List.replicate 32 0x33) (word_bytes 32) (by decide) (by decide) rfl rfl rfl (Int.toBytes_length 8 _)
    0x100d8 31 (by decide) z' f

end Prysm.BeaconBlockHeader.Witness.EncodeRejectLength
