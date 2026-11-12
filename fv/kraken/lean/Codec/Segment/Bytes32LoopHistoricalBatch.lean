import Codec.Segment.Bytes32LoopProof
import E2eHb.HbLoop2
import Codec.SegmentTemplate

/-!
# The HistoricalBatch BlockRoots loop `E2eHb.hb_loop1` re-derived from the general loop `Codec.Segment.v32_loop`

The theorem below has the type of the hand lemma `hb_loop1` (`type_of%`); its proof instantiates `v32_loop`
(n = 8192, the HistoricalBatch frame slots, receiver offsets 0 and 8, src = 0) and steps the exit label (directive 85).
The block facts come from the real program by `infix_sub` (the templates equal the `.S` directives), the glue
facts by reading the `nop` directives 39 and 48. This is the check that the general loop covers the hand loop.
-/

open Machine Runtime TestTarget E2eList E2eHb E2eHb.Code

namespace Codec.Segment

variable [Host]

theorem glue_of {p : Program} {k a : Nat} (hk : p.IsInfixAt Host.prog k) (h : p[a]? = some v32Nop) :
    Glue (k + a) (k + a + 1) := by
  refine Or.inr ⟨rfl, ?_⟩
  have ha : a < p.length := by
    rcases (List.getElem?_eq_some_iff.mp h) with ⟨ha, -⟩; exact ha
  rw [List.isInfixAt_iff_getElem?.mp hk a ha, ← List.getElem?_eq_getElem ha]; exact h

theorem src_of {p : Program} {k a : Nat} {src : Int64} (hk : p.IsInfixAt Host.prog k)
    (h : p[a]? = some (v32LeaSrc src)) : GlueSrc (k + a) (k + a + 1) src := by
  refine Or.inr ⟨rfl, ?_⟩
  have ha : a < p.length := by
    rcases (List.getElem?_eq_some_iff.mp h) with ⟨ha, -⟩; exact ha
  rw [List.isInfixAt_iff_getElem?.mp hk a ha, ← List.getElem?_eq_getElem ha]; exact h

/-- `nop` positions and the `cmp/jge` head need these strings. -/
abbrev hbL (s : String) : String := "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_" ++ s

theorem hb_loop1_g : type_of% @E2eHb.hb_loop1 := by
  intro _ k hk hf sp recv bf A pks hpks hpk rbp0 r140 S Heap R hms hmm j i ps l18 l20 l28 l30 spl rslot lo avail s
    hij hps h18 h20 h28 h30 hspl hrs hlo hav hrax hrsp hrbp hr14 h_mem
  have hB1 : (v32Head (OfNat.ofNat 8192) (hbL "a0") (hbL "166")).IsInfixAt Host.prog (k + 40) :=
    Codec.infix_sub 40 hk (by simp only [HbUnmarshal, v32Head, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB2 : (v32Mid (hbL "2aa") 40 32 24 48 80).IsInfixAt Host.prog (k + 49) :=
    Codec.infix_sub 49 hk (by simp only [HbUnmarshal, v32Mid, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB3 : (v32Mm 72 8 40).IsInfixAt Host.prog (k + 62) :=
    Codec.infix_sub 62 hk (by simp only [HbUnmarshal, v32Mm, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB4 : (v32Hdr (hbL "2a5") 0).IsInfixAt Host.prog (k + 67) :=
    Codec.infix_sub 67 hk (by simp only [HbUnmarshal, v32Hdr, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB5 : (v32Tail (hbL "14c") (hbL "8f") 48).IsInfixAt Host.prog (k + 75) :=
    Codec.infix_sub 75 hk (by simp only [HbUnmarshal, v32Tail, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB6 : (v32Back (hbL "8f") 24).IsInfixAt Host.prog (k + 36) :=
    Codec.infix_sub 36 hk (by simp only [HbUnmarshal, v32Back, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have g1 : Glue (k + 40 + 8) (k + 49) := glue_of hk (a := 48)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g4 : Glue (k + 36 + 3) (k + 40) := glue_of hk (a := 39)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g3 : Glue (k + 67 + 7) (k + 75) := glue_of hk (a := 74)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have hlb := Machine.label_at' hk hf (j := 36)
    (by simp only [HbUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [HbUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hle := Machine.label_at' hk hf (j := 85)
    (by simp only [HbUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [HbUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have e8192 : Int.toBytes 8 8192 = Int.toBytes 8 (BitVec.ofNat 64 8192).toInt := by decide
  -- the exit label step (directive 85) after the general loop
  have step85 : ∀ (st : MachineState), st.pc = Host.addrOf (k + 85) →
      Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + 86) ∧ st'.data = st.data) st := by
    rintro ⟨d, pc⟩ hpc
    dsimp only at hpc; subst hpc
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := d
    kat hk HbUnmarshal 85
    exact Eventually.done _ ⟨rfl, rfl⟩
  have hmem' := h_mem
  rw [e8192] at hmem'
  cases j with
  | zero =>
    have hi : i = 8192 := by omega
    subst hi
    refine eventually_trans _ _ _ _ (v32_exit 8192 (by decide) _ _ (k + 40) (k + 85) hB1 hle
      (fun st => st.pc = Host.addrOf (k + 85) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem) s hrax
      (fun _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro st ⟨hpc, hr, hm⟩
    refine eventually_trans _ _ _ _ (step85 st hpc) ?_
    rintro st' ⟨hpc', hd⟩
    refine Eventually.done _ ⟨hpc', by rw [hd, hr, hrsp], by rw [hd, hr, hrbp], by rw [hd, hr, hr14], ps, l18, l20,
      l28, l30, spl, rslot, lo, hps, h18, h20, h28, h30, hspl, hrs, hlo, ?_⟩
    rw [hd, hm]; simpa using h_mem
  | succ j =>
    refine eventually_trans _ _ _ _ (v32_loop 8192 (by decide) (hbL "a0") (hbL "166") (hbL "2aa") (hbL "2a5")
      (hbL "14c") (hbL "8f") 40 32 24 48 80 72 8 0 0 (k + 40) (k + 49) (k + 62) (k + 67) (k + 75) (k + 36) (k + 85)
      hB1 hB2 hB3 hB4 hB5 hB6 g1 (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) g3 g4 hlb hle sp recv bf bf A (sp + 40) (sp + 32)
      (sp + 24) (sp + 48) (sp + 80) (sp + 72) (recv + 8) recv
      (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
      (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
      (by simp only [Int64.toBitVec_ofNat]) (by simp) (by simp) pks hpks hpk rbp0 r140 S Heap R hms hmm
      (j + 1) i ps l28 l20 l18 l30 spl rslot lo avail s hij hps h28 h20 h18 h30 hspl hrs hlo hav
      (Or.inl (by omega)) hrax hrsp hrbp hr14 (by ecancel)) ?_
    rintro st ⟨hpc, hsp, hbp, h14, ps', lI', lD', lI1', lP', spl', lo', hps', g5, g6, g7, g8, gspl, glo, Hm⟩
    refine eventually_trans _ _ _ _ (step85 st hpc) ?_
    rintro st' ⟨hpc', hd⟩
    refine Eventually.done _ ⟨hpc', by rw [hd]; exact hsp, by rw [hd]; exact hbp, by rw [hd]; exact h14, ps', lI1',
      lD', lI', lP', spl', Int.toBytes 8 (Host.addrOf (k + 62 + 1 + 1)).toBitVec.toInt, lo', hps', g7, g6, g5, g8, gspl, Int.toBytes_length 8 _, glo, ?_⟩
    rw [hd, e8192]
    ecancel

theorem hb_loop2_g : type_of% @E2eHb.hb_loop2 := by
  intro _ k hk hf sp recv bf A pks hpks hpk rbp0 r140 S Heap R hms hmm j i ps l18 l20 l28 l30 spl rslot lo avail s
    hij hps h18 h20 h28 h30 hspl hrs hlo hav hr0 hrax hrsp hrbp hr14 h_mem
  have hB1 : (v32Head (OfNat.ofNat 8192) (hbL "1c0") (hbL "28c")).IsInfixAt Host.prog (k + 108) :=
    Codec.infix_sub 108 hk (by simp only [HbUnmarshal, v32Head, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB2 : (v32Mid (hbL "29b") 40 32 24 48 80).IsInfixAt Host.prog (k + 117) :=
    Codec.infix_sub 117 hk (by simp only [HbUnmarshal, v32Mid, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB3 : (v32Mm 72 32 40).IsInfixAt Host.prog (k + 131) :=
    Codec.infix_sub 131 hk (by simp only [HbUnmarshal, v32Mm, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB4 : (v32Hdr (hbL "296") 24).IsInfixAt Host.prog (k + 137) :=
    Codec.infix_sub 137 hk (by simp only [HbUnmarshal, v32Hdr, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB5 : (v32Tail (hbL "272") (hbL "1b4") 48).IsInfixAt Host.prog (k + 144) :=
    Codec.infix_sub 144 hk (by simp only [HbUnmarshal, v32Tail, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB6 : (v32Back (hbL "1b4") 24).IsInfixAt Host.prog (k + 104) :=
    Codec.infix_sub 104 hk (by simp only [HbUnmarshal, v32Back, hbL, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have g1 : Glue (k + 108 + 8) (k + 117) := glue_of hk (a := 116)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g2 : Glue (k + 131 + 5) (k + 137) := glue_of hk (a := 136)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g4 : Glue (k + 104 + 3) (k + 108) := glue_of hk (a := 107)
    (by simp only [HbUnmarshal, v32Nop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have gs : GlueSrc (k + 117 + 13) (k + 131) 262144 := src_of hk (a := 130)
    (by simp only [HbUnmarshal, v32LeaSrc, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have hlb := Machine.label_at' hk hf (j := 104)
    (by simp only [HbUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [HbUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hle := Machine.label_at' hk hf (j := 154)
    (by simp only [HbUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [HbUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have e8192 : Int.toBytes 8 8192 = Int.toBytes 8 (BitVec.ofNat 64 8192).toInt := by decide
  have step154 : ∀ (st : MachineState), st.pc = Host.addrOf (k + 154) →
      Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + 155) ∧ st'.data = st.data) st := by
    rintro ⟨d, pc⟩ hpc
    dsimp only at hpc; subst hpc
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := d
    kat hk HbUnmarshal 154
    exact Eventually.done _ ⟨rfl, rfl⟩
  refine eventually_trans _ _ _ _ (v32_loop 8192 (by decide) (hbL "1c0") (hbL "28c") (hbL "29b") (hbL "296")
    (hbL "272") (hbL "1b4") 40 32 24 48 80 72 32 24 262144 (k + 108) (k + 117) (k + 131) (k + 137) (k + 144)
    (k + 104) (k + 154)
    hB1 hB2 hB3 hB4 hB5 hB6 g1 gs g2 (Or.inl rfl) g4 hlb hle sp recv bf (bf + 262144) A (sp + 40) (sp + 32)
    (sp + 24) (sp + 48) (sp + 80) (sp + 72) (recv + 32) (recv + 24)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    pks hpks hpk rbp0 r140 S Heap R hms hmm
    j i ps l28 l20 l18 l30 spl rslot lo avail s hij hps h28 h20 h18 h30 hspl hrs hlo hav
    hr0 hrax hrsp hrbp hr14 (by rw [e8192] at h_mem; ecancel)) ?_
  rintro st ⟨hpc, hsp, hbp, h14, ps', lI', lD', lI1', lP', spl', lo', hps', g5, g6, g7, g8, gspl, glo, Hm⟩
  refine eventually_trans _ _ _ _ (step154 st hpc) ?_
  rintro st' ⟨hpc', hd⟩
  rw [show k + 131 + 1 + 1 = k + 133 from rfl] at Hm
  refine Eventually.done _ ⟨hpc', by rw [hd]; exact hsp, by rw [hd]; exact hbp, by rw [hd]; exact h14, ps', lI1',
    lD', lI', lP', spl', lo', hps', g7, g6, g5, g8, gspl, glo, ?_⟩
  rw [hd, e8192]
  ecancel

end Codec.Segment
