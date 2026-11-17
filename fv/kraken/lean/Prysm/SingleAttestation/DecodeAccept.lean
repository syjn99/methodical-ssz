import Prysm.SingleAttestation.Statements
import Prysm.SingleAttestation.DecodeAcceptHead
import Prysm.SingleAttestation.DecodeAcceptData
import Prysm.SingleAttestation.DecodeAcceptSignature
import Prysm.SingleAttestation.Code

/-!
# Prysm `(*v1alpha1.SingleAttestation).UnmarshalSSZ`, accept path, Go 1.26.10 machine code

The statement is `Decode.accept_statement` (`Prysm/SingleAttestation/Statements.lean`).
Three segment lemmas: `Decode.head` (entry → `L_167`, the CommitteeIndex and ValidatorIndex callees),
`Decode.data` (→ `L_234`, the new AttestationData object and its decoder), `Decode.signature` (→ return, the Signature
`makeslice` and `memmove`).
Every directive index comes from the Go 1.26.10 `.S` file.

**Case covered.** One theorem covers every receiver: the code has no branch on `Data`.
It always allocates the AttestationData object through `runtime.newobject` and overwrites the old pointer (`aD` is
arbitrary bytes, nil or not).

**Callees.** CommitteeIndex and ValidatorIndex are discharged through the proved function specifications
`Prysm.CommitteeIndex.Decode.accept_function_spec_holds` and `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`.
AttestationData is discharged through `Prysm.AttestationData.Decode.accept` (with its own callees Slot, CommitteeIndex,
Checkpoint and Epoch).
The code of each callee is placed in the host (`kA`, `kS`, `kI`, `kV`, `kC`, `kE`); the statement has no hypothesis
about their behavior.
The runtime contracts stay visible: this function's `NewobjectContract … typeAttestationData 96 (Sd + 224)`,
`MakesliceContract … (Sd + 224)` and `MemmoveContract (Sd + 224)`, and the ones that `Prysm.AttestationData.Decode.accept`
needs with the scratch `Sd`.

Stack (x = s.regs.rsp at entry): see `Prysm/SingleAttestation/Statements.lean`.
The callees write the frame word at x − 136 (their saved rbp); it is the top 8 bytes of the scratch `lo`.
-/

open Machine Runtime Prysm.SingleAttestation.Code
variable [Host]

namespace Prysm.SingleAttestation

omit [Host] in
/-- The scratch below the return slot x − 128 as its first `S + 216` bytes and the callees' saved-rbp word at x − 136. -/
theorem Decode.low_stack_top (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S + 216)
    (hf : f.length = 8) :
    Eq ((a ++ f).At (x - 128 - BitVec.ofNat 64 (S + 224))) = Eq (a.At (x - 128 - BitVec.ofNat 64 (S + 224)))
      ⋆ Eq (f.At (x - 136)) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega

omit [Host] in
/-- The 40-byte spill area at x − 120 as five 8-byte words. -/
theorem Decode.split_five_words (x : BitVec 64) (a b c d e : List UInt8) (ha : a.length = 8) (hb : b.length = 8)
    (hc : c.length = 8) (hd : d.length = 8) (he : e.length = 8) :
    Eq ((a ++ (b ++ (c ++ (d ++ e)))).At (x - 120)) = Eq (a.At (x - 120)) ⋆ Eq (b.At (x - 112)) ⋆ Eq (c.At (x - 104))
      ⋆ Eq (d.At (x - 96)) ⋆ Eq (e.At (x - 88)) := by
  have q1 : x - 112 = x - 120 + BitVec.ofNat 64 a.length := by
    rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q2 : x - 104 = x - 112 + BitVec.ofNat 64 b.length := by
    rw [hb]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q3 : x - 96 = x - 104 + BitVec.ofNat 64 c.length := by
    rw [hc]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  have q4 : x - 88 = x - 96 + BitVec.ofNat 64 d.length := by
    rw [hd]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  rw [at_app a _ q1 (by simp [ha, hb, hc, hd, he]), at_app b _ q2 (by simp [hb, hc, hd, he]),
    at_app c _ q3 (by simp [hc, hd, he]), at_app d _ q4 (by simp [hd, he])]
  simp only [Std.ExtHashMap.sep_assoc]

omit [Host] in
/-- The 40-byte spill area at x − 120 as its first 24 bytes and its last 16 bytes. -/
theorem Decode.split_spill_area (x : BitVec 64) (a b : List UInt8) (ha : a.length = 24) (hb : b.length = 16) :
    Eq ((a ++ b).At (x - 120)) = Eq (a.At (x - 120)) ⋆ Eq (b.At (x - 96)) := by
  have q1 : x - 96 = x - 120 + BitVec.ofNat 64 a.length := by
    rw [ha]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  rw [at_app a _ q1 (by simp [ha, hb])]

/-- **Accept path of the `(*v1alpha1.SingleAttestation).UnmarshalSSZ` (Go 1.26.10)**; statement =
`Decode.accept_statement`. -/
theorem Decode.accept : Decode.accept_statement := by
  intro k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kV hkV hfV kC hkC hfC kE hkE hfE ci ai ds di root se sroot te troot sig
    hci hai hds hdi hroot hse hsroot hte htroot hsig s ra guard
    fp s1 s2 s4 l28 l30 l38 spl rslot lo ast aCI aAI aD aP aL aC
    hfp h1 h2 h4 hl28 hl30 hl38 hspl hrs hast haCI haAI haD haP haL haC
    R Sd hSd8 hSd hlo Heap avail h_mem hguard hlen hav hno hms hmm hmsD hmmD hmsD' hmmD' hnoD
  have hcis : Prysm.CommitteeIndex.Decode.accept_function_spec := Prysm.CommitteeIndex.Decode.accept_function_spec_holds kI hkI hfI
  have hvis : Prysm.ValidatorIndex.Decode.accept_function_spec := Prysm.ValidatorIndex.Decode.accept_function_spec_holds kV hkV hfV
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  -- the spill area as five words, the scratch as its lower part and the callees' saved-rbp word
  have espl : spl = spl.take 8 ++ ((spl.drop 8).take 8 ++ ((spl.drop 16).take 8 ++ ((spl.drop 24).take 8
      ++ spl.drop 32))) := by
    conv => lhs; rw [← List.take_append_drop 8 spl, ← List.take_append_drop 8 (spl.drop 8),
      ← List.take_append_drop 8 ((spl.drop 8).drop 8), ← List.take_append_drop 8 (((spl.drop 8).drop 8).drop 8)]
    simp only [List.drop_drop]
  have hw0 : (spl.take 8).length = 8 := by simp [hspl]
  have hw1 : ((spl.drop 8).take 8).length = 8 := by simp [hspl]
  have hw2 : ((spl.drop 16).take 8).length = 8 := by simp [hspl]
  have hw3 : ((spl.drop 24).take 8).length = 8 := by simp [hspl]
  have hw4 : (spl.drop 32).length = 8 := by simp [hspl]
  rw [espl, Decode.split_five_words _ _ _ _ _ _ hw0 hw1 hw2 hw3 hw4] at h_mem
  have hlt : (lo.take (Sd + 216)).length = Sd + 216 := by simp [hlo]
  have hld : (lo.drop (Sd + 216)).length = 8 := by simp [hlo]
  have elo : Eq (lo.At (rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224))) =
      Eq ((lo.take (Sd + 216)).At (rsp.toBitVec - 128 - BitVec.ofNat 64 (Sd + 224)))
        ⋆ Eq ((lo.drop (Sd + 216)).At (rsp.toBitVec - 136)) := by
    conv => lhs; rw [← List.take_append_drop (Sd + 216) lo]
    exact Decode.low_stack_top _ Sd hSd _ _ hlt hld
  rw [elo] at h_mem
  -- head segment: entry → L_167 (CommitteeIndex, ValidatorIndex)
  refine eventually_trans _ _ _ _ (Decode.head k hk hf hcis hvis ci ai hci hai _ ra guard fp s1 s2 s4 ((spl.drop 8).take 8)
    rslot (lo.drop (Sd + 216)) ast aCI aAI hfp h1 h2 h4 hw1 hrs hld hast haCI haAI _ (by dsimp only; ecancel) hguard hlen) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hrbp1, hr141, Hm1⟩
  dsimp only at hpc1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  -- Data segment: L_167 → L_234
  refine eventually_trans _ _ _ _ (Decode.data k hk hf kA hkA hfA kS hkS hfS kI hkI hfI kC hkC hfC kE hkE hfE rsp r14 guard
    rax.toBitVec rbx.toBitVec rdi.toBitVec ds di root se sroot te troot hds hdi hroot hse hsroot hte htroot
    (spl.take 8) (Int.toBytes 8 (rbx.toBitVec + 8).toInt) ((spl.drop 16).take 8) ((spl.drop 24).take 8) (spl.drop 32)
    (Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt)
    (lo.take (Sd + 216) ++ Int.toBytes 8 (rsp.toBitVec - 8#64).toInt) aD
    hw0 (Int.toBytes_length 8 _) hw2 hw3 hw4 (Int.toBytes_length 8 _) haD _ Sd hSd8 hSd
    (by simp only [List.length_append, hlt, Int.toBytes_length]) Heap avail (by omega)
    d1 (by rw [hrsp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp))
    (by rw [hrbp1]; first | rfl | (apply UInt64.toBitVec_inj.mp; simp)) hr141
    (by rw [Decode.low_stack_top _ Sd hSd _ _ hlt (Int.toBytes_length 8 _)]; ecancel)
    hguard hno hmsD hmmD hmsD' hmmD' hnoD) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, pd, p, ps, pt, p1, p2, spA, spB, lo2, hspA, hspB, hlo2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  -- Signature segment: L_234 → return
  refine eventually_mono (Decode.signature k hk hf rsp r14 ra rbp rax.toBitVec rbx.toBitVec sig hsig l28 l30 l38 spA
    (Int.toBytes 8 (Host.addrOf (k + 107)).toBitVec.toInt) lo2 aP aL aC hl28 hl30 hl38 hspA (Int.toBytes_length 8 _)
    haP haL haC _ (Sd + 224) hlo2 Heap (avail - 336) (by omega) d2 hrsp2 hrbp2 hr142 hrax2 hrbx2
    (by ecancel)
    hms hmm) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, psig, spA', lo', hspA', hlo', Hm3⟩
  rw [show avail - 336 - 96 = avail - 432 by omega] at Hm3
  refine ⟨e1, e2, e3, e4, e5, e6, pd, p, ps, pt, p1, p2, psig, spA' ++ spB, lo', by simp [hspA', hspB], hlo', ?_⟩
  rw [Decode.split_spill_area _ _ _ hspA' hspB]
  ecancel

end Prysm.SingleAttestation
