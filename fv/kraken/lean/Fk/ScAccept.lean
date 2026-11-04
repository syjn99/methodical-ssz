import Fk.Bytes
import Fk.Labels

/-!
# Scalars.UnmarshalSSZ, accept path, on Kraken main (6064eec)

If `len(buf) = 16` and the bool byte is 0 or 1, the function copies the input
chunks into the receiver fields (A @0, B @2, C @4, D @8, E @16), returns nil
(rax = rbx = 0) to the return address. 25 directives on each of the two paths.

The input is given as five chunks at the widths the code reads (1, 2, 4, 8, 1
bytes); the receiver as five chunks at the widths it writes. Hypotheses `hL37f`,
`hL3bf`: the two internal labels do not occur in the host program before the function.
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 2000000 in
theorem sc_accept_main (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (s : MachineData) (ra : UInt64) (slot b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 : List UInt8)
    (hsl : slot.length = 8) (h0l : b0.length = 1) (h1l : b1.length = 2) (h2l : b2.length = 4)
    (h3l : b3.length = 8) (h4l : b4.length = 1)
    (g0 : c0.length = 1) (g1 : c1.length = 2) (g2 : c2.length = 4) (g3 : c3.length = 8) (g4 : c4.length = 1)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
      ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
      ⋆ Eq (b4.At (s.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hL37f : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_37"))
    (hL3bf : ∀ i < k, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_3b"))
    (hlen : s.regs.rcx = 16) (hb4 : b4 = [0] ∨ b4 = [1]) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ (Eq (b0.At s.regs.rax.toBitVec) ⋆ Eq (b1.At (s.regs.rax.toBitVec + 2))
          ⋆ Eq (b2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (b3.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq (b4.At (s.regs.rax.toBitVec + 16)) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hL37 := label_in_fragment hk (j := 18) (by decide) (by decide) hL37f
  have hL3b := label_in_fragment hk (j := 20) (by decide) (by decide) hL3bf
  have h0 := hk
  simp only [ScalarsUnmarshalSSZ] at h0
  apply estep h0
  simp [Directive.interp]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hlen ⊢
  subst hlen
  -- 1: spill
  apply estep h0.cons.2
  kunfold
  apply store_step _ _ _ _ _ slot _ _ (by ecancel) (by exact hsl)
  intro m1 H1
  simp only [Effects.All]
  -- 2,3: cmp, jne (not taken)
  apply estep h0.cons.2.cons.2
  kunfold
  apply estep h0.cons.2.cons.2.cons.2
  kunfold
  split
  · rename_i h; exact absurd h (by decide)
  simp only [Effects.All]
  -- 4: movzbl (%rbx),%ecx ; 5: mov %cl,(%rax)
  apply estep (isInfixAt_drop hk 4)
  kunfold
  apply load_step _ _ _ _ b0 _ _ (by ecancel) (by exact h0l)
  kunfold
  apply estep (isInfixAt_drop hk 5)
  kunfold
  apply store_step _ _ _ _ _ c0 _ _ (by ecancel) (by exact g0)
  intro m2 H2
  kunfold
  apply estep (isInfixAt_drop hk 6)
  kunfold
  apply load_step _ _ _ _ b1 _ _ (by ecancel) (by exact h1l)
  kunfold
  apply estep (isInfixAt_drop hk 7)
  kunfold
  apply store_step _ _ _ _ _ c1 _ _ (by ecancel) (by exact g1)
  intro m3 H3
  kunfold
  apply estep (isInfixAt_drop hk 8)
  kunfold
  apply load_step _ _ _ _ b2 _ _ (by ecancel) (by exact h2l)
  kunfold
  apply estep (isInfixAt_drop hk 9)
  kunfold
  apply store_step _ _ _ _ _ c2 _ _ (by ecancel) (by exact g2)
  intro m4 H4
  kunfold
  apply estep (isInfixAt_drop hk 10)
  kunfold
  apply load_step _ _ _ _ b3 _ _ (by ecancel) (by exact h3l)
  kunfold
  apply estep (isInfixAt_drop hk 11)
  kunfold
  apply store_step _ _ _ _ _ c3 _ _ (by ecancel) (by exact g3)
  intro m5 H5
  kunfold
  apply estep (isInfixAt_drop hk 12)
  kunfold
  apply load_step _ _ _ _ b4 _ _ (by ecancel) (by exact h4l)
  kunfold
  apply estep (isInfixAt_drop hk 13)
  kunfold
  apply estep (isInfixAt_drop hk 14)
  kunfold
  split
  · rename_i h; exact absurd h (by subst_vars; rcases hb4 with rfl | rfl <;> decide)
  simp only [Effects.All]
  rcases hb4 with rfl | rfl
  · -- E = false: jne taken to L_37
    apply estep (isInfixAt_drop hk 15)
    kunfold
    split
    case isFalse h => exact absurd h (by decide)
    simp only [Effects.All]
    rw [hL37]
    apply estep (isInfixAt_drop hk 18)
    kunfold
    apply estep (isInfixAt_drop hk 19)
    kunfold
    apply store_step _ _ _ _ _ c4 _ _ (by ecancel) (by exact g4)
    intro m6 H6
    kunfold
    apply estep (isInfixAt_drop hk 20)
    kunfold
    apply estep (isInfixAt_drop hk 21)
    kunfold
    intro _
    apply estep (isInfixAt_drop hk 22)
    kunfold
    intro _
    apply estep (isInfixAt_drop hk 23)
    kunfold
    apply estep (isInfixAt_drop hk 24)
    kunfold
    apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    simp only [Width.bytes, zx8, zx16, zx32, toBytes_ofInt_ofBytes 8 1 rfl b0 h0l,
      toBytes_ofInt_ofBytes 16 2 rfl b1 h1l, toBytes_ofInt_ofBytes 32 4 rfl b2 h2l,
      toBytes_ofInt_ofBytes 64 8 rfl b3 h3l,
      show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,
      show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H6
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; rfl
    · simp
    · simp
    · dsimp only; (try simp only [BitVec.ofNat_eq_ofNat] at H6 ⊢); exact sep_true (by ecancel)

  · -- E = true: jne not taken
    apply estep (isInfixAt_drop hk 15)
    kunfold
    split
    · rename_i h; exact absurd h (by decide)
    simp only [Effects.All]
    apply estep (isInfixAt_drop hk 16)
    kunfold
    apply store_step _ _ _ _ _ c4 _ _ (by ecancel) (by exact g4)
    intro m6 H6
    kunfold
    apply estep (isInfixAt_drop hk 17)
    kunfold
    rw [hL3b]
    apply estep (isInfixAt_drop hk 20)
    kunfold
    apply estep (isInfixAt_drop hk 21)
    kunfold
    intro _
    apply estep (isInfixAt_drop hk 22)
    kunfold
    intro _
    apply estep (isInfixAt_drop hk 23)
    kunfold
    apply estep (isInfixAt_drop hk 24)
    kunfold
    apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    simp only [Width.bytes, zx8, zx16, zx32, toBytes_ofInt_ofBytes 8 1 rfl b0 h0l,
      toBytes_ofInt_ofBytes 16 2 rfl b1 h1l, toBytes_ofInt_ofBytes 32 4 rfl b2 h2l,
      toBytes_ofInt_ofBytes 64 8 rfl b3 h3l,
      show Int.toBytes 1 (BitVec.truncate 8 (0 : BitVec 64)).toInt = [0] by decide,
      show Int.toBytes 1 (BitVec.truncate 8 (1 : BitVec 64)).toInt = [1] by decide] at H6
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; rfl
    · simp
    · simp
    · dsimp only; (try simp only [BitVec.ofNat_eq_ofNat] at H6 ⊢); exact sep_true (by ecancel)
