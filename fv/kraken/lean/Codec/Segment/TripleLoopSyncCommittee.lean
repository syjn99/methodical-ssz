import Codec.Segment.TripleLoopProof
import Codec.Segment.Bytes32LoopHistoricalBatch
import Prysm.SyncCommittee.DecodeLoop

/-!
# The SyncCommittee loop `Prysm.SyncCommittee.Decode.loop` re-derived from the general loop `Codec.Segment.triple_loop`

The theorem has the type of the hand lemma `Prysm.SyncCommittee.Decode.loop` (`type_of%`); its proof instantiates `triple_loop` (k = 4, w = 48,
n = 512, the SyncCommittee frame slots, receiver offsets 8 and 16, src = 0) and steps the exit label (directive 80). Block facts
by `infix_sub` on the real program; gaps read from the `nop` directives 39, 47 and 61.
-/

open Machine Runtime Prysm.HistoricalBatch Codec.Segment

namespace Codec.Segment

variable [Host]

abbrev syncCommitteeLabel (s : String) : String := "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_" ++ s

theorem sync_committee_loop : type_of% @Prysm.SyncCommittee.Decode.loop := by
  intro _ k hk hf sp recv bf A pks hpks hpk rbp0 r140 S Heap R hms hmm j i ps l18 l20 l28 spl rslot lo avail s
    hij hps h18 h20 h28 hspl hrs hlo hav hrax hrsp hrbp hr14 h_mem
  have hB1 : (tripleLoopHead (OfNat.ofNat 512) (syncCommitteeLabel "a0") (syncCommitteeLabel "156") 24 (OfNat.ofNat 48)).IsInfixAt Host.prog (k + 40) :=
    Codec.infix_sub 40 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopHead, syncCommitteeLabel, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB2 : (tripleLoopMiddle (OfNat.ofNat 4) 40 24 32 72).IsInfixAt Host.prog (k + 48) :=
    Codec.infix_sub 48 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopMiddle, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB3 : (tripleLoopMemmove (OfNat.ofNat 48) 64 16 24).IsInfixAt Host.prog (k + 56) :=
    Codec.infix_sub 56 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopMemmove, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB4 : (tripleLoopHeader (syncCommitteeLabel "1ff") 8 32 (OfNat.ofNat 48)).IsInfixAt Host.prog (k + 62) :=
    Codec.infix_sub 62 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopHeader, syncCommitteeLabel, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB5 : (tripleLoopTail (syncCommitteeLabel "137") (syncCommitteeLabel "91") 40).IsInfixAt Host.prog (k + 69) :=
    Codec.infix_sub 69 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopTail, syncCommitteeLabel, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have hB6 : (tripleLoopBack (syncCommitteeLabel "91")).IsInfixAt Host.prog (k + 36) :=
    Codec.infix_sub 36 hk (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, tripleLoopBack, syncCommitteeLabel, List.drop_succ_cons, List.drop_zero,
      List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero] <;> first | rfl | decide)
  have g1 : Glue (k + 40 + 7) (k + 48) := glue_of hk (a := 47)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, bytes32LoopNop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g2 : Glue (k + 56 + 5) (k + 62) := glue_of hk (a := 61)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, bytes32LoopNop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have g4 : Glue (k + 36 + 3) (k + 40) := glue_of hk (a := 39)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, bytes32LoopNop, List.getElem?_cons_succ, List.getElem?_cons_zero])
  have hlb := Machine.label_at' hk hf (j := 36)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have hle := Machine.label_at' hk hf (j := 80)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [Prysm.SyncCommittee.Code.unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  have e512 : Int.toBytes 8 512 = Int.toBytes 8 (BitVec.ofNat 64 512).toInt := by decide
  have e48 : (OfNat.ofNat (48 : Nat) : Int) = 48 := rfl
  have step80 : ∀ (st : MachineState), st.pc = Host.addrOf (k + 80) →
      Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + 81) ∧ st'.data = st.data) st := by
    rintro ⟨d, pc⟩ hpc
    dsimp only at hpc; subst hpc
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := d
    step_directive hk Prysm.SyncCommittee.Code.unmarshalSSZ 80
    exact Eventually.done _ ⟨rfl, rfl⟩
  cases j with
  | zero =>
    have hi : i = 512 := by omega
    subst hi
    refine eventually_trans _ _ _ _ (triple_loop_exit 512 (by decide) _ _ 24 _ (k + 40) (k + 80) hB1 hle
      (fun st => st.pc = Host.addrOf (k + 80) ∧ st.data.regs = s.regs ∧ st.data.dmem = s.dmem) s hrax
      (fun _ => ⟨rfl, rfl, rfl⟩)) ?_
    rintro st ⟨hpc, hr, hm⟩
    refine eventually_trans _ _ _ _ (step80 st hpc) ?_
    rintro st' ⟨hpc', hd⟩
    refine Eventually.done _ ⟨hpc', by rw [hd, hr, hrsp], by rw [hd, hr, hrbp], by rw [hd, hr, hr14], ps, l18, l20,
      l28, spl, rslot, lo, hps, h18, h20, h28, hspl, hrs, hlo, ?_⟩
    rw [hd, hm]; simpa using h_mem
  | succ j =>
    refine eventually_trans _ _ _ _ (triple_loop 4 48 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 512 (by decide) (syncCommitteeLabel "a0")
      (syncCommitteeLabel "156") (syncCommitteeLabel "1ff") (syncCommitteeLabel "137") (syncCommitteeLabel "91") 24 32 40 72 64 16 8 0 (k + 40) (k + 48) (k + 56) (k + 62)
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

end Codec.Segment
