import Codec.Bytes32Decode
import E2eAd.AdRoot

/-!
# In-sample check of the 32-byte field pattern (decode): `AttestationData.BeaconBlockRoot` from `rootdec_seg`

`ad_e2e_root_s` has the statement of `E2eAd.ad_e2e_root` (`E2eAd/AdRoot.lean`) word for word.
Its proof steps the label `L_167` (directive 85), applies `Codec.rootdec_seg` with the
AttestationData parameters (head block at k + 86, second block at k + 100 = `L_1ac`,
`lwb` = `L_1f3`; receiver spill 0x80, buffer spill 0x88, pointer slot 0x68; field offsets
24 / 32 / 40; source offset 16; callee stack `S + 96`), and does the two instance-specific
directives by hand: 112 `mov 0x68(%rsp),%rbx`, 113 `jmp L_208`, then `L_208` (directive 120).
`ad_root_same_stmt` checks that the statements are the same proposition.
-/

open Machine Runtime TestTarget E2eAd.Code
variable [Host]

open Codec
namespace E2eScal

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem ad_e2e_root_s (k : Nat) (hk : AdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh AdUnmarshal k)
    (rsp0 r140 : UInt64) (rcv bf : BitVec 64) (root : List UInt8) (hroot : root.length = 32)
    (spl rslot lo l68 aP aL aC : List UInt8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8) (hl68 : l68.length = 8)
    (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 96)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 ≤ avail)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := rsp0.toBitVec - 120 })
    (hrbp : s.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 }) (hr14 : s.regs.r14 = r140)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
      ⋆ Eq (spl.At (rsp0.toBitVec - 120)) ⋆ Eq (rslot.At (rsp0.toBitVec - 128))
      ⋆ Eq (lo.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S)) ⋆ Eq (l68.At (rsp0.toBitVec - 16))
      ⋆ Heap avail
      ⋆ Eq (aP.At (rcv + 24)) ⋆ Eq (aL.At (rcv + 32)) ⋆ Eq (aC.At (rcv + 40))
      ⋆ Eq (root.At (bf + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 (S + 96)) (hmm : MemmoveC (S + 96)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 120) ∧ st.data.regs.rsp = { toBitVec := rsp0.toBitVec - 120 }
        ∧ st.data.regs.rbp = { toBitVec := rsp0.toBitVec - 8#64 } ∧ st.data.regs.r14 = r140 ∧
        ∃ (p : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S + 96
          ∧ st.data.regs.rbx.toBitVec = p ∧ st.data.regs.rdx.toBitVec = rcv ∧
        (Eq ((Int.toBytes 8 rcv.toInt).At (rsp0.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bf.toInt).At (rsp0.toBitVec + 16))
          ⋆ Eq (spl'.At (rsp0.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 107)).toBitVec.toInt).At (rsp0.toBitVec - 128))
          ⋆ Eq (lo'.At (rsp0.toBitVec - 224 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rsp0.toBitVec - 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (rcv + 24)) ⋆ Eq ((Int.toBytes 8 32).At (rcv + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (rcv + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (root.At (bf + 16))
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + 85)⟩ := by
  have hA := infix_sub (q := rootDecHead
    "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1ac" 128 32 40) 86 hk
    (by simp only [AdUnmarshal, rootDecHead, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero])
  have hB := infix_sub (q := rootDecMid
    "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1ac"
    "L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1f3"
    128 136 104 24 32 40 16) 100 hk
    (by simp only [AdUnmarshal, rootDecMid, List.drop_succ_cons, List.drop_zero, List.length_cons,
      List.length_nil, List.take_succ_cons, List.take_zero])
  have hl := Machine.label_at' hk hf (j := 100)
    (by simp only [AdUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [AdUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 h_mem ⊢
  subst rsp rbp r14
  kat hk AdUnmarshal 85
  refine eventually_trans _ _ _ _ (rootdec_seg _ _ 128 136 104 24 32 40 16 (k + 86) (k + 100) hA hB hl
    (rsp0.toBitVec - 120) rcv bf (rsp0.toBitVec + 8) (rsp0.toBitVec + 16) (rsp0.toBitVec - 16)
    (rsp0.toBitVec - 128) (rsp0.toBitVec - 224 - BitVec.ofNat 64 S) (rcv + 24) (rcv + 32) (rcv + 40) (bf + 16)
    (S + 96)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by simp only [Int64.toBitVec_ofNat]; bv_omega)
    (by simp only [Int64.toBitVec_ofNat]; bv_omega) (by bv_omega)
    (by rw [show rsp0.toBitVec - 120 - 8 = rsp0.toBitVec - 128 by bv_omega]; exact E2eAd.ada_lo _ _ hS)
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    (by simp only [Int64.toBitVec_ofNat]) (by simp only [Int64.toBitVec_ofNat])
    { toBitVec := rsp0.toBitVec - 8#64 } r140 root hroot spl rslot lo l68 aP aL aC hspl hrs hlo hl68 haP haL haC
    R Heap avail hav _ rfl rfl rfl (by ecancel) hms hmm) ?_
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hrbp3, hr143, p, spl', lo', hspl', hlo', hrdx3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrbp3 hrdx3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrbp3 hrdx3 Hm3
  subst hrsp3 hr143 hrbp3
  have hl208 := Machine.label_at' hk hf (j := 120)
    (by simp only [AdUnmarshal, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [AdUnmarshal, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  kat hk AdUnmarshal 112
  apply load_step_at _ _ (rsp0.toBitVec - 16) _ _ (Int.toBytes 8 p.toInt) _ _ (by adaddr) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk AdUnmarshal 113
  rw [hl208]
  apply Eventually.done
  rw [show k + 100 + 6 + 1 = k + 107 from rfl] at Hm3
  exact ⟨rfl, rfl, rfl, rfl, p, spl', lo', hspl', hlo', rfl, hrdx3, by ecancel⟩

/-- The in-sample statement is the hand statement (same proposition). -/
theorem ad_root_same_stmt : @E2eAd.ad_e2e_root = @ad_e2e_root_s := rfl

end E2eScal
