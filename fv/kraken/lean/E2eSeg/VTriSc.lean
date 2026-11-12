import E2eSeg.VTriLoop
import E2eSeg.V32Hb
import E2eList.ScLoop

/-!
# The SyncCommittee loop `E2eList.sc_loop` re-derived from the general loop `E2eSeg.vtri_loop`

The theorem has the type of the hand lemma `sc_loop` (`type_of%`); its proof instantiates `vtri_loop` (k = 4, w = 48,
n = 512, the SyncCommittee frame slots, receiver offsets 8 and 16, src = 0) and steps the exit label (directive 80). Block facts
by `infix_sub` on the real program; gaps read from the `nop` directives 39, 47 and 61.
-/

open Fk E2eList E2eHb E2eSeg E2eList.Code

namespace E2eSeg

variable [Host]

abbrev scL (s : String) : String := "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_" ++ s

theorem sc_loop_g : type_of% @E2eList.sc_loop := by
  intro _ k hk hf sp recv bf A pks hpks hpk rbp0 r140 S Heap R hms hmm j i ps l18 l20 l28 spl rslot lo avail s
    hij hps h18 h20 h28 hspl hrs hlo hav hrax hrsp hrbp hr14 h_mem
  have hB1 : (tHead (OfNat.ofNat 512) (scL "a0") (scL "156") 24 (OfNat.ofNat 48)).IsInfixAt Host.prog (k + 40) :=
    E2eScal.infix_sub 40 hk (by simp only [ScUnmarshal, tHead, scL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB2 : (tMid (OfNat.ofNat 4) 40 24 32 72).IsInfixAt Host.prog (k + 48) :=
    E2eScal.infix_sub 48 hk (by simp only [ScUnmarshal, tMid, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB3 : (tMm (OfNat.ofNat 48) 64 16 24).IsInfixAt Host.prog (k + 56) :=
    E2eScal.infix_sub 56 hk (by simp only [ScUnmarshal, tMm, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB4 : (tHdr (scL "1ff") 8 32 (OfNat.ofNat 48)).IsInfixAt Host.prog (k + 62) :=
    E2eScal.infix_sub 62 hk (by simp only [ScUnmarshal, tHdr, scL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB5 : (tTail (scL "137") (scL "91") 40).IsInfixAt Host.prog (k + 69) :=
    E2eScal.infix_sub 69 hk (by simp only [ScUnmarshal, tTail, scL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB6 : (tBack (scL "91")).IsInfixAt Host.prog (k + 36) :=
    E2eScal.infix_sub 36 hk (by simp only [ScUnmarshal, tBack, scL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have g1 : Glue (k + 40 + 7) (k + 48) := glue_of hk (a := 47)
    (by simp only [ScUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g2 : Glue (k + 56 + 5) (k + 62) := glue_of hk (a := 61)
    (by simp only [ScUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g4 : Glue (k + 36 + 3) (k + 40) := glue_of hk (a := 39)
    (by simp only [ScUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have hlb := Fk.label_at' hk hf (j := 36)
    (by simp only [ScUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [ScUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hle := Fk.label_at' hk hf (j := 80)
    (by simp only [ScUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [ScUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have e512 : Int.toBytes 8 512 = Int.toBytes 8 (BitVec.ofNat 64 512).toInt := by decide
  have e48 : (OfNat.ofNat (48 : Nat) : Int) = 48 := rfl
  have step80 : ∀ (st : MachineState), st.pc = Host.addrOf (k + 80) →
      Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + 81) ∧ st'.data = st.data) st := by
    rintro ⟨d, pc⟩ hpc
    dsimp only at hpc; subst hpc
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := d
    kat hk ScUnmarshal 80
    exact Eventually.done _ ⟨rfl, rfl⟩
  cases j with
  | zero =>
    have hi : i = 512 := by omega
    subst hi
    refine eventually_trans _ _ _ _ (vtri_exit 512 (by decide) _ _ 24 _ (k + 40) (k + 80) hB1 hle
      (fun st => st.pc = Host.addrOf (k + 80) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem) s hrax
      (fun _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro st ⟨hpc, hr, hm⟩
    refine eventually_trans _ _ _ _ (step80 st hpc) ?_
    rintro st' ⟨hpc', hd⟩
    refine Eventually.done _ ⟨hpc', by rw [hd, hr, hrsp], by rw [hd, hr, hrbp], by rw [hd, hr, hr14], ps, l18, l20,
      l28, spl, rslot, lo, hps, h18, h20, h28, hspl, hrs, hlo, ?_⟩
    rw [hd, hm]; simpa using h_mem
  | succ j =>
    refine eventually_trans _ _ _ _ (vtri_loop 4 48 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 512 (by decide) (scL "a0")
      (scL "156") (scL "1ff") (scL "137") (scL "91") 24 32 40 72 64 16 8 0 (k + 40) (k + 48) (k + 56) (k + 62)
      (k + 69) (k + 36) (k + 80) hB1 hB2 hB3 hB4 hB5 hB6 g1 (Or.inl ⟨rfl, rfl⟩) g2 (Or.inl rfl) g4 hlb hle
      sp recv bf bf A (sp + 24) (sp + 32) (sp + 40) (sp + 72) (sp + 64) (recv + 16) (recv + 8)
      (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
      (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
      (by simp only [Int64.toBitVec_ofNat]) (by simp) pks hpks hpk rbp0 r140 S Heap R hms hmm
      (j + 1) i ps l18 l20 l28 spl rslot lo avail s hij hps h18 h20 h28 hspl hrs hlo hav
      (Or.inl (by omega)) hrax hrsp hrbp hr14 (by rw [e512] at h_mem; rw [e48]; ecancel)) ?_
    rintro st ⟨hpc, hsp, hbp, h14, ps', lI', l3', lP', spl', lo', hps', g5, g6, g7, gspl, glo, Hm⟩
    refine eventually_trans _ _ _ _ (step80 st hpc) ?_
    rintro st' ⟨hpc', hd⟩
    refine Eventually.done _ ⟨hpc', by rw [hd]; exact hsp, by rw [hd]; exact hbp, by rw [hd]; exact h14, ps', lI',
      l3', lP', spl', Int.toBytes 8 (Host.addrOf (k + 56 + 1 + 1)).toBitVec.toInt, lo', hps', g5, g6, g7, gspl,
      Int.toBytes_length 8 _, glo, ?_⟩
    rw [hd, e512]
    rw [e48] at Hm
    ecancel

end E2eSeg
