import TestTarget.ListU64DecodeRejectCall
import Prysm.Checkpoint.EncodeFastPath
import E2eScal.BhCode
import Codec.StackGuard

/-!
# Real Prysm `(*v1alpha1.BeaconBlockHeader).MarshalSSZTo`, fast path, head segments (hold-out)

Hand proof. The generator has no encode mode; no template lemma is used.

    func (b *BeaconBlockHeader) MarshalSSZTo(buf []byte) (dst []byte, err error) {
        dst = buf
        dst = ssz.MarshalUint64(dst, uint64(b.Slot))            // inlined
        dst = ssz.MarshalUint64(dst, uint64(b.ProposerIndex))   // inlined
        if size := len(b.ParentRoot); size != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, b.ParentRoot...)
        ... StateRoot, BodyRoot the same ...
        return }

Directive indices of `E2eScal.BhCode.BhMarshal` on the fast path (`len(dst) + 112 ≤ cap(dst)`, all three
roots of length 32). This module: 2–4 stack guard (`lea -0x20(%rsp),%r12; cmp 0x10(%r14),%r12; jbe`, closed
with `Codec.lea_cmp_be_false`), 5–9 prologue (`sub $0x98`, rbx and rax spills to rsp + 16 and rsp + 8),
10 `lea 0x8(%rcx),%rdx`, 11 Slot load, 15–18 the first 32-byte stack temp (two `movups %xmm15`, Slot word at
rsp − 56), 19–20 capacity, 33–35 store the Slot bytes (`bh_enc_a1`, 0–35); 36–44 the ProposerIndex temp at
rsp − 88, 45–46 capacity, 59–61 store (`bh_enc_a2`, 36–61). Each segment names only the memory it touches;
the rest is the frame `R`. X15 is not assumed to be zero: the bytes 8–31 of each temp are existential in
the conclusions. `rsp` below is the entry rsp.
-/

open Machine Runtime TestTarget E2eScal.BhCode
variable [Host]

open Codec
namespace E2eScal.Bh

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Slot segment: entry to directive 36 (stack guard passed, frame set up, Slot bytes stored). -/
theorem bh_enc_a1 (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (sl d0 : List UInt8) (hsl : sl.length = 8) (hd0 : d0.length = 8)
    (s : MachineData) (guard : UInt64)
    (fp s1 s2 t1a t1b : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (ht1a : t1a.length = 16) (ht1b : t1b.length = 16)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t1a.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1b.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat + 32 < s.regs.rsp.toNat) (hsp : 168 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 36) ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rcx = s.regs.rcx ∧ st.data.regs.rdx = { toBitVec := s.regs.rcx.toBitVec + 8 }
        ∧ st.data.regs.rdi = s.regs.rdi
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 8#64 - 152 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧
        (Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BhMarshal 0
  kat hk BhMarshal 1
  kat hk BhMarshal 2
  kat hk BhMarshal 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BhMarshal 4
  split
  case isTrue h =>
    exfalso
    rw [lea_cmp_be_false rsp.toBitVec _ guard.toBitVec _ _ 32 (by rfl) hguard] at h
    exact Bool.noConfusion h
  simp only [Effects.All]
  kat hk BhMarshal 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BhMarshal 6
  kat hk BhMarshal 7
  kat hk BhMarshal 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BhMarshal 9
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ s1 _ _ (by bv_omega) (by ecancel) (by exact h1)
  intro m2' H2'
  simp only [Width.bytes, Width.bits] at H2'
  kunfold
  kat hk BhMarshal 10
  kat hk BhMarshal 11
  apply load_step _ _ _ _ sl _ _ (by ecancel) (by exact hsl)
  kunfold
  kat hk BhMarshal 12
  kat hk BhMarshal 13
  kat hk BhMarshal 14
  kat hk BhMarshal 15
  kat hk BhMarshal 16
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 152 + 104 = rsp.toBitVec - 56 by bv_omega]
  apply store_avx_step _ _ _ _ t1a _ _ (by ecancel) (by exact ht1a) (by decide)
  intro m3 H3
  kunfold
  kat hk BhMarshal 17
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 56 + 16 = rsp.toBitVec - 40 by bv_omega]
  apply store_avx_step _ _ _ _ t1b _ _ (by ecancel) (by exact ht1b) (by decide)
  intro m4 H4
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 56),
    show rsp.toBitVec - 56 + 8 = rsp.toBitVec - 48 by bv_omega] at H4
  kat hk BhMarshal 18
  apply store_step_at _ _ (rsp.toBitVec - 56) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m5 H5
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl sl hsl] at H5
  kunfold
  kat hk BhMarshal 19
  kat hk BhMarshal 20
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BhMarshal 33
  kat hk BhMarshal 33
  kat hk BhMarshal 34
  apply load_step_at _ _ (rsp.toBitVec - 56) _ _ sl _ _ (by eaddr) (by ecancel) (by exact hsl)
  kunfold
  kat hk BhMarshal 35
  rw [Prysm.Checkpoint.Encode.fast_path_mul]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m6 H6
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl sl hsl] at H6
  kunfold
  apply Eventually.done
  refine ⟨?gpc, ?grax, ?grbx, ?grcx, ?grdx, ?grdi, ?grsp, ?grbp, ?gr14,
    (Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8,
    Int.toBytes AvxWidth.W128.bytes (zmms.get (AvxReg.xmm RegMm.mm15)).toInt, ?ht1, ?hu1, ?hmem⟩
  case gpc => with_reducible rfl
  case grax => with_reducible rfl
  case grbx => with_reducible rfl
  case grcx => with_reducible rfl
  case grdx => with_reducible rfl
  case grdi => with_reducible rfl
  case grsp => with_reducible rfl
  case grbp => with_reducible rfl
  case gr14 => with_reducible rfl
  case ht1 => simp [Int.toBytes_length]
  case hu1 => rw [Int.toBytes_length]
  case hmem => ecancel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- ProposerIndex segment: directive 36 to directive 62 (ProposerIndex bytes stored). Only the atoms it touches. -/
theorem bh_enc_a2 (k : Nat) (hk : BhMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh BhMarshal k)
    (pi d1 : List UInt8) (hpi : pi.length = 8) (hd1 : d1.length = 8)
    (s : MachineData) (rsp : UInt64) (t2a t2b : List UInt8)
    (ht2a : t2a.length = 16) (ht2b : t2b.length = 16) (R : DataMem → Prop)
    (hrsp : s.regs.rsp = { toBitVec := rsp.toBitVec - 8#64 - 152 })
    (hrdx : s.regs.rdx = { toBitVec := s.regs.rcx.toBitVec + 8 })
    (h_mem : s.dmem =⋆ Eq (t2a.At (rsp.toBitVec - 88)) ⋆ Eq (t2b.At (rsp.toBitVec - 72))
      ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R)
    (hcap : s.regs.rcx.toNat + 112 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 62) ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.r8.toBitVec = s.regs.rcx.toBitVec + 8 + 8 ∧ st.data.regs.rdi = s.regs.rdi
        ∧ st.data.regs.rsp = s.regs.rsp ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t2 u2 : List UInt8), t2.length = 8 ∧ u2.length = 16 ∧
        (Eq (pi.At (rsp.toBitVec - 88)) ⋆ Eq (t2.At (rsp.toBitVec - 80))
          ⋆ Eq (u2.At (rsp.toBitVec - 72))
          ⋆ Eq (pi.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq (pi.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 36)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdxc, rsi, rdi, rspc, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrdx h_mem hcap hcap63 ⊢
  subst hrsp hrdx
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BhMarshal 36
  kat hk BhMarshal 37
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ pi _ _ (by eaddr) (by ecancel) (by exact hpi)
  kunfold
  kat hk BhMarshal 38
  kat hk BhMarshal 39
  kat hk BhMarshal 40
  kat hk BhMarshal 41
  kat hk BhMarshal 42
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 8#64 - 152 + 72 = rsp.toBitVec - 88 by bv_omega]
  apply store_avx_step _ _ _ _ t2a _ _ (by ecancel) (by exact ht2a) (by decide)
  intro m7 H7
  kunfold
  kat hk BhMarshal 43
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [show rsp.toBitVec - 88 + 16 = rsp.toBitVec - 72 by bv_omega]
  apply store_avx_step _ _ _ _ t2b _ _ (by ecancel) (by exact ht2b) (by decide)
  intro m8 H8
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 88),
    show rsp.toBitVec - 88 + 8 = rsp.toBitVec - 80 by bv_omega] at H8
  kat hk BhMarshal 44
  apply store_step_at _ _ (rsp.toBitVec - 88) _ _ _ ((Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).take 8)
    _ _ (by eaddr) (by ecancel) (by rw [List.length_take, Int.toBytes_length]; rfl)
  intro m9 H9
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl pi hpi] at H9
  kunfold
  kat hk BhMarshal 45
  kat hk BhMarshal 46
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BhMarshal 59
  kat hk BhMarshal 59
  kat hk BhMarshal 60
  apply load_step_at _ _ (rsp.toBitVec - 88) _ _ pi _ _ (by eaddr) (by ecancel) (by exact hpi)
  kunfold
  kat hk BhMarshal 61
  rw [Prysm.Checkpoint.Encode.fast_path_dst]
  apply store_step _ _ _ _ _ d1 _ _ (by ecancel) (by exact hd1)
  intro m10 H10
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl pi hpi] at H10
  kunfold
  apply Eventually.done
  refine ⟨?gpc, ?grax, ?grbx, ?gr8, ?grdi, ?grsp, ?grbp, ?gr14,
    (Int.toBytes 16 (zmms.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8,
    Int.toBytes AvxWidth.W128.bytes (zmms.get (AvxReg.xmm RegMm.mm15)).toInt, ?ht2, ?hu2, ?hmem⟩
  case gpc => with_reducible rfl
  case grax => with_reducible rfl
  case grbx => with_reducible rfl
  case gr8 => with_reducible rfl
  case grdi => with_reducible rfl
  case grsp => with_reducible rfl
  case grbp => with_reducible rfl
  case gr14 => with_reducible rfl
  case ht2 => simp [Int.toBytes_length]
  case hu2 => rw [Int.toBytes_length]
  case hmem => ecancel

end E2eScal.Bh
