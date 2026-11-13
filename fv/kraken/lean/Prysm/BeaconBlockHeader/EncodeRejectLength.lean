import Prysm.BeaconBlockHeader.EncodeFastPath
import Codec.EncodeRejectTail
import Prysm.Checkpoint.EncodeRejectLength
import Runtime.CopyModel

/-!
# Length rejects of `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` through `Codec.enc_reject_tail`

Go source: `if size := len(b.ParentRoot); size != 32 { return nil, ssz.ErrBytesLength }` (the same for
StateRoot and BodyRoot). Directive indices of `Prysm.BeaconBlockHeader.Code.marshalSSZTo`: the three `jne` are 65, 93 and
121; the tails are `L_2e1` (175; body 176–183), `L_2c2` (165; body 166–174, with a `nop` before `retq`)
and `L_2a4` (156; body 157–164). Each tail is one instance of the reject block `enc_reject_tail`
(`Encode.rej_at`: the code facts).

* `Encode.rej_b` (from 62), `Encode.rej_c` (from 90), `Encode.rej_d` (from 118): the length test of one root with a
  length word `rl ≠ 32`, the taken `jne`, the label, the block. Memory is unchanged.
* `bh_e2e_marshal_reject{1,2,3}_main`: the function from its entry, by composition with the unchanged
  fast-path segments `Encode.enc_a1`, `Encode.enc_a2`, `Encode.enc_b`, `Encode.enc_c`. The code writes Slot and
  ProposerIndex (and the earlier roots) to `dst[len:]` before it finds the bad length; the conclusions
  state these bytes (the encoder writes the earlier fields into the caller's spare capacity before it tests a root length). The returned slice is nil.

Limits. No `runtime.growslice` branch: the premise is `len(dst) + 112 ≤ cap(dst)`, which is what the reused
segments `Encode.enc_a1` / `Encode.enc_a2` state; the code needs less on these paths (16, 48 and 80 bytes). A reject
with a smaller capacity is NOT covered. The morestack path is not covered. The two error words are a
premise (initialised `ssz.ErrBytesLength`).
-/

open Machine Runtime TestTarget Prysm.BeaconBlockHeader.Code
variable [Host]

open Codec
namespace Prysm.BeaconBlockHeader

set_option maxRecDepth 100000 in
/-- Code facts of the reject block: the three tails. -/
theorem Encode.rej_at (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) :
    (rejTail false false 152).IsInfixAt Host.prog (k + 176)
      ∧ (rejTail false true 152).IsInfixAt Host.prog (k + 166)
      ∧ (rejTail false false 152).IsInfixAt Host.prog (k + 157) := by
  refine ⟨infix_sub 176 hk ?_, infix_sub 166 hk ?_, infix_sub 157 hk ?_⟩ <;>
    simp only [marshalSSZTo, rejTail, relRsp, nopOpt, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero]

theorem Encode.reject_fp (x : BitVec 64) : relAddr false 152 (x - 8#64 - 152) = x - 8 := by
  show x - 8#64 - 152 + (152 : BitVec 64) = x - 8
  bv_omega

theorem Encode.reject_ra (x : BitVec 64) : x - 8 + 8 = x := by bv_omega

theorem Encode.reject_rsp (r x : UInt64) (h : r.toBitVec = x.toBitVec + 8) : r = x + 8 := by
  apply UInt64.toBitVec_inj.mp; rw [h]; simp

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Reject segment from directive 62: the length word `rl` of the root at receiver + 24 is not 32;
the function returns `(nil, ssz.ErrBytesLength)`. Memory unchanged. -/
theorem Encode.rej_b (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (rsp ra rbp0 e0 e1 rl : UInt64) (hrl : rl ≠ 32) (recv p1 : BitVec 64)
    (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (hrax : s.regs.rax = { toBitVec := recv })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 32))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (recv + 24))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 32))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 62)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax h_mem ⊢
  subst hrsp hrax
  kat hk marshalSSZTo 62
  apply load_step_at _ _ (recv + 24) _ _ (Int.toBytes 8 p1.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 63
  apply load_step_at _ _ (recv + 32) _ _ (Int.toBytes 8 rl.toBitVec.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk marshalSSZTo 64
  kat hk marshalSSZTo 65
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, Width.bits] at h
    exact hrl (UInt64.toBitVec_inj.mp (Prysm.Checkpoint.Encode.reject_length_eq _ h))
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 175
  kat hk marshalSSZTo 175
  refine eventually_mono (enc_reject_tail false false 152 (k + 176) (Encode.rej_at k hk).1
    (rsp.toBitVec - 8#64 - 152) (rsp.toBitVec - 8) rsp.toBitVec (Encode.reject_fp _) (Encode.reject_ra _) ra rbp0 e0 e1 _ _
    (by rfl) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  exact ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', Encode.reject_rsp _ _ hrsp', hrbp', hr14', by ecancel⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Reject segment from directive 90: the length word `rl` of the root at receiver + 48 is not 32;
the function returns `(nil, ssz.ErrBytesLength)`. Memory unchanged. -/
theorem Encode.rej_c (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (rsp ra rbp0 e0 e1 rl : UInt64) (hrl : rl ≠ 32) (recv p2 : BitVec 64)
    (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 56))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (recv + 48))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 56))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 90)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  kat hk marshalSSZTo 90
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 91
  apply load_step_at _ _ (recv + 48) _ _ (Int.toBytes 8 p2.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 92
  apply load_step_at _ _ (recv + 56) _ _ (Int.toBytes 8 rl.toBitVec.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk marshalSSZTo 93
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, Width.bits] at h
    exact hrl (UInt64.toBitVec_inj.mp (Prysm.Checkpoint.Encode.reject_length_eq _ h))
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 165
  kat hk marshalSSZTo 165
  refine eventually_mono (enc_reject_tail false true 152 (k + 166) (Encode.rej_at k hk).2.1
    (rsp.toBitVec - 8#64 - 152) (rsp.toBitVec - 8) rsp.toBitVec (Encode.reject_fp _) (Encode.reject_ra _) ra rbp0 e0 e1 _ _
    (by rfl) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  exact ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', Encode.reject_rsp _ _ hrsp', hrbp', hr14', by ecancel⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Reject segment from directive 118: the length word `rl` of the root at receiver + 72 is not 32;
the function returns `(nil, ssz.ErrBytesLength)`. Memory unchanged. -/
theorem Encode.rej_d (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (rsp ra rbp0 e0 e1 rl : UInt64) (hrl : rl ≠ 32) (recv p3 : BitVec 64)
    (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 80))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = s.regs.r14 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 recv.toInt).At (rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (recv + 72))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (recv + 80))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
          st.data.dmem)
      ⟨s, Host.addrOf (k + 118)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst hrsp
  kat hk marshalSSZTo 118
  apply load_step_at _ _ (rsp.toBitVec + 8) _ _ (Int.toBytes 8 recv.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 119
  apply load_step_at _ _ (recv + 72) _ _ (Int.toBytes 8 p3.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk marshalSSZTo 120
  apply load_step_at _ _ (recv + 80) _ _ (Int.toBytes 8 rl.toBitVec.toInt) _ _ (by eaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk marshalSSZTo 121
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, Width.bits] at h
    exact hrl (UInt64.toBitVec_inj.mp (Prysm.Checkpoint.Encode.reject_length_eq _ h))
  simp only [Effects.All]
  klabel hk hf marshalSSZTo 156
  kat hk marshalSSZTo 156
  refine eventually_mono (enc_reject_tail false false 152 (k + 157) (Encode.rej_at k hk).2.2
    (rsp.toBitVec - 8#64 - 152) (rsp.toBitVec - 8) rsp.toBitVec (Encode.reject_fp _) (Encode.reject_ra _) ra rbp0 e0 e1 _ _
    (by rfl) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  exact ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', Encode.reject_rsp _ _ hrsp', hrbp', hr14', by ecancel⟩

theorem Encode.reject_v48 (y : BitVec 64) : y + 48 = y + 8 + 8 + 32 := by bv_omega
theorem Encode.reject_v80 (y : BitVec 64) : y + 80 = y + 8 + 8 + 32 + 32 := by bv_omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Length reject of ParentRoot** (`len(b.ParentRoot) ≠ 32`, capacity premise `len + 112 ≤ cap`): the real
`(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` returns `(nil, ssz.ErrBytesLength)`. Before the test the code
has written Slot and ProposerIndex to `dst[len:]`; the conclusion states these bytes. The receiver, the prefix,
the frame `R` and the stack guard are unchanged. No growslice branch. -/
theorem Encode.reject_length_parent_root (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (sl pi pre d0 d1 : List UInt8)
    (hsl : sl.length = 8) (hpi : pi.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (p1 : BitVec 64) (rl : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard e0 e1 : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t1a t1b t2a t2b : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16) (ht2a : t2a.length = 16) (ht2b : t2b.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t2a.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2b.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8 ∧ u2.length = 16 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (pi.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pi.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  -- Slot segment, directives 0–35
  refine eventually_trans _ _ _ _ (Encode.enc_a1 k hk hf sl d0 hsl hd0 s guard fp s1 s2 t1a t1b hfp h1 h2 ht1a ht1b _
    (by ecancel) hguard hsp hcap hcap63) ?_
  rintro ⟨x1, pc1⟩ ⟨hpc1, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, hrsp1, hrbp1, hr141, t1, u1, ht1, hu1, Hm1⟩
  dsimp only at hpc1 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- ProposerIndex segment, directives 36–61
  refine eventually_trans _ _ _ _ (Encode.enc_a2 k hk hf pi d1 hpi hd1 x1 s.regs.rsp t2a t2b ht2a ht2b _
    hrsp1 (by rw [hrdx1, hrcx1]) (by rw [hrax1, hrbx1, hrcx1]; ecancel)
    (by rw [hrcx1, hrdi1]; exact hcap) (by rw [hrdi1]; exact hcap63)) ?_
  rintro ⟨x2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hr82, hrdi2, hrsp2, hrbp2, hr142, t2, u2, ht2, hu2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hr82 hrdi2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  rw [hrax1, hrbx1, hrcx1] at Hm2
  -- reject: 62–65, L_2e1
  refine eventually_mono (Encode.rej_b k hk hf x2 s.regs.rsp ra s.regs.rbp e0 e1 rl hrl s.regs.rax.toBitVec p1 _
    (hrsp2.trans hrsp1) (hrax2.trans hrax1) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  exact ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14'.trans (hr142.trans hr141),
    t1, u1, t2, u2, ht1, hu1, ht2, hu2, by ecancel⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Length reject of StateRoot** (`len(b.StateRoot) ≠ 32`, capacity premise `len + 112 ≤ cap`): the real
`(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` returns `(nil, ssz.ErrBytesLength)`. Before the test the code
has written Slot, ProposerIndex and ParentRoot to `dst[len:]`; the conclusion states these bytes. The receiver, the prefix,
the frame `R` and the stack guard are unchanged. No growslice branch. -/
theorem Encode.reject_length_state_root (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (sl pi pre d0 d1 r1 d2 : List UInt8)
    (hsl : sl.length = 8) (hpi : pi.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (hr1 : r1.length = 32) (hd2 : d2.length = 32)
    (p1 p2 : BitVec 64) (rl : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard e0 e1 : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t1a t1b t2a t2b l16 l96 l104 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16) (ht2a : t2a.length = 16) (ht2b : t2b.length = 16)
    (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t2a.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2b.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (r1.At p1)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 scr : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8 ∧ u2.length = 16
          ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (pi.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (r1.At p1)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pi.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (r1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨hcB, hcC, hcD⟩ := Encode.capacity_le s.regs.rcx.toBitVec s.regs.rdi.toBitVec hcap hcap63
  have hc63 : s.regs.rdi.toBitVec.toNat < 2 ^ 63 := hcap63
  rw [Encode.o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec] at h_mem
  -- Slot segment, directives 0–35
  refine eventually_trans _ _ _ _ (Encode.enc_a1 k hk hf sl d0 hsl hd0 s guard fp s1 s2 t1a t1b hfp h1 h2 ht1a ht1b _
    (by ecancel) hguard hsp hcap hcap63) ?_
  rintro ⟨x1, pc1⟩ ⟨hpc1, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, hrsp1, hrbp1, hr141, t1, u1, ht1, hu1, Hm1⟩
  dsimp only at hpc1 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- ProposerIndex segment, directives 36–61
  refine eventually_trans _ _ _ _ (Encode.enc_a2 k hk hf pi d1 hpi hd1 x1 s.regs.rsp t2a t2b ht2a ht2b _
    hrsp1 (by rw [hrdx1, hrcx1]) (by rw [hrax1, hrbx1, hrcx1]; ecancel)
    (by rw [hrcx1, hrdi1]; exact hcap) (by rw [hrdi1]; exact hcap63)) ?_
  rintro ⟨x2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hr82, hrdi2, hrsp2, hrbp2, hr142, t2, u2, ht2, hu2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hr82 hrdi2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  rw [hrax1, hrbx1, hrcx1] at Hm2
  have hr8' : x2.regs.r8 = { toBitVec := s.regs.rcx.toBitVec + 8 + 8 } := by
    apply UInt64.toBitVec_inj.mp; rw [hr82, hrcx1]
  -- ParentRoot segment, directives 62–89, memmove
  refine eventually_trans _ _ _ _ (Encode.enc_b k hk hf r1 d2 hr1 hd2 x2 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8) s.regs.rdi.toBitVec p1 l16 l96 l104 rslot scratch
    hl16 hl96 hl104 hrs S hsc _ (hrsp2.trans hrsp1) (hrax2.trans hrax1) (hrbx2.trans hrbx1) hr8'
    (hrdi2.trans hrdi1) (by ecancel) hcB hc63 hmm) ?_
  rintro ⟨x3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, scr1, hscr1, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- reject: 90–93, L_2c2
  refine eventually_mono (Encode.rej_c k hk hf x3 s.regs.rsp ra s.regs.rbp e0 e1 rl hrl s.regs.rax.toBitVec p2 _
    (hrsp3.trans (hrsp2.trans hrsp1)) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  refine ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14'.trans (hr143.trans (hr142.trans hr141)),
    t1, u1, t2, u2, scr1, ht1, hu1, ht2, hu2, hscr1, ?_⟩
  rw [Encode.o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, Encode.reject_v48 s.regs.rcx.toBitVec]
  ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Length reject of BodyRoot** (`len(b.BodyRoot) ≠ 32`, capacity premise `len + 112 ≤ cap`): the real
`(*v1alpha1.BeaconBlockHeader).MarshalSSZTo` returns `(nil, ssz.ErrBytesLength)`. Before the test the code
has written Slot, ProposerIndex, ParentRoot and StateRoot to `dst[len:]`; the conclusion states these bytes. The receiver, the prefix,
the frame `R` and the stack guard are unchanged. No growslice branch. -/
theorem Encode.reject_length_body_root (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (sl pi pre d0 d1 r1 d2 r2 d3 : List UInt8)
    (hsl : sl.length = 8) (hpi : pi.length = 8) (hd0 : d0.length = 8) (hd1 : d1.length = 8)
    (hr1 : r1.length = 32) (hd2 : d2.length = 32) (hr2 : r2.length = 32) (hd3 : d3.length = 32)
    (p1 p2 p3 : BitVec 64) (rl : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard e0 e1 : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 t1a t1b t2a t2b l16 l96 l104 rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16) (ht2a : t2a.length = 16) (ht2b : t2b.length = 16)
    (hl16 : l16.length = 8) (hl96 : l96.length = 8) (hl104 : l104.length = 8) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l96.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (l104.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (t2a.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2b.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 80))
      ⋆ Eq (r1.At p1)
      ⋆ Eq (r2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 scr : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8 ∧ u2.length = 16
          ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 80).toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq (pi.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 80))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 118)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 168))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 168 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 72))
          ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (r1.At p1)
          ⋆ Eq (r2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (pi.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (r1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
          ⋆ Eq (r2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrBytesLength").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨hcB, hcC, hcD⟩ := Encode.capacity_le s.regs.rcx.toBitVec s.regs.rdi.toBitVec hcap hcap63
  have hc63 : s.regs.rdi.toBitVec.toNat < 2 ^ 63 := hcap63
  rw [Encode.o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, Encode.o48 s.regs.rbx.toBitVec s.regs.rcx.toBitVec] at h_mem
  -- Slot segment, directives 0–35
  refine eventually_trans _ _ _ _ (Encode.enc_a1 k hk hf sl d0 hsl hd0 s guard fp s1 s2 t1a t1b hfp h1 h2 ht1a ht1b _
    (by ecancel) hguard hsp hcap hcap63) ?_
  rintro ⟨x1, pc1⟩ ⟨hpc1, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, hrsp1, hrbp1, hr141, t1, u1, ht1, hu1, Hm1⟩
  dsimp only at hpc1 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- ProposerIndex segment, directives 36–61
  refine eventually_trans _ _ _ _ (Encode.enc_a2 k hk hf pi d1 hpi hd1 x1 s.regs.rsp t2a t2b ht2a ht2b _
    hrsp1 (by rw [hrdx1, hrcx1]) (by rw [hrax1, hrbx1, hrcx1]; ecancel)
    (by rw [hrcx1, hrdi1]; exact hcap) (by rw [hrdi1]; exact hcap63)) ?_
  rintro ⟨x2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hr82, hrdi2, hrsp2, hrbp2, hr142, t2, u2, ht2, hu2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hr82 hrdi2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  rw [hrax1, hrbx1, hrcx1] at Hm2
  have hr8' : x2.regs.r8 = { toBitVec := s.regs.rcx.toBitVec + 8 + 8 } := by
    apply UInt64.toBitVec_inj.mp; rw [hr82, hrcx1]
  -- ParentRoot segment, directives 62–89, memmove
  refine eventually_trans _ _ _ _ (Encode.enc_b k hk hf r1 d2 hr1 hd2 x2 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8) s.regs.rdi.toBitVec p1 l16 l96 l104 rslot scratch
    hl16 hl96 hl104 hrs S hsc _ (hrsp2.trans hrsp1) (hrax2.trans hrax1) (hrbx2.trans hrbx1) hr8'
    (hrdi2.trans hrdi1) (by ecancel) hcB hc63 hmm) ?_
  rintro ⟨x3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, scr1, hscr1, Hm3⟩
  dsimp only at hpc3 hrsp3 hrbp3 hr143 Hm3
  subst hpc3
  -- StateRoot segment, directives 90–117, memmove
  refine eventually_trans _ _ _ _ (Encode.enc_c k hk hf r2 d3 hr2 hd3 x3 s.regs.rsp s.regs.rax.toBitVec
    s.regs.rbx.toBitVec (s.regs.rcx.toBitVec + 8 + 8 + 32) s.regs.rdi.toBitVec p2
    (Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt) scr1 (Int.toBytes_length 8 _) S hscr1 _
    (hrsp3.trans (hrsp2.trans hrsp1)) (by ecancel) hcC hc63 hmm) ?_
  rintro ⟨x4, pc4⟩ ⟨hpc4, hrsp4, hrbp4, hr144, scr2, hscr2, Hm4⟩
  dsimp only at hpc4 hrsp4 hrbp4 hr144 Hm4
  subst hpc4
  -- reject: 118–121, L_2a4
  refine eventually_mono (Encode.rej_d k hk hf x4 s.regs.rsp ra s.regs.rbp e0 e1 rl hrl s.regs.rax.toBitVec p3 _
    (hrsp4.trans (hrsp3.trans (hrsp2.trans hrsp1))) (by ecancel)) ?_
  rintro st ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp', hr14', hm⟩
  refine ⟨hpc, hrax', hrbx', hrcx', hrdi', hrsi', hrsp', hrbp',
    hr14'.trans (hr144.trans (hr143.trans (hr142.trans hr141))),
    t1, u1, t2, u2, scr2, ht1, hu1, ht2, hu2, hscr2, ?_⟩
  rw [Encode.o16 s.regs.rbx.toBitVec s.regs.rcx.toBitVec, Encode.o48 s.regs.rbx.toBitVec s.regs.rcx.toBitVec,
    Encode.reject_v80 s.regs.rcx.toBitVec]
  ecancel

end Prysm.BeaconBlockHeader
