import Prysm.DataColumnsByRootIdentifier.StatementsDecodeThenEncode

/-!
# Corrected round-trip statement: a bound on the scratch size (added after the freeze of `Prysm/DataColumnsByRootIdentifier/StatementsDecodeThenEncode.lean`)

`DecodeThenEncode.round_trip_scratch_bounded_statement` is the frozen text of `DecodeThenEncode.round_trip_statement` with one added premise
`(hS : S < 2 ^ 60)`; nothing else differs. Reason: the encoder's scratch is the decoder's scratch and return slot
(`S + 8` bytes, `Prysm/DataColumnsByRootIdentifier/DecodeThenEncode.lean`); splitting that block needs `S + 8 < 2^64`, and nothing in the original premises
bounds `S` (a list longer than 2^64 would cover every address, but the separation facts that refute it are not
proved here). The precondition is stronger than the frozen one. The original stays unchanged and unproved (N).
Precedent: `Prysm.Checkpoint.DecodeThenEncode.round_trip` has the same premise `hS : S < 2 ^ 60`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

/-- **Round trip (machine), scratch bounded.** -/
def DecodeThenEncode.round_trip_scratch_bounded_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (km : Nat) (hkm : Prysm.DataColumnsByRootIdentifier.Code.marshalSSZTo.IsInfixAt Host.prog km) (hfm : LabelsFresh Prysm.DataColumnsByRootIdentifier.Code.marshalSSZTo km)
    (n : Nat) (hn : n ≤ 128) (root ib : List UInt8) (hroot : root.length = 32) (hib : ib.length = 8 * n)
    (s : MachineData) (ra ra2 guard : UInt64)
    (fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (h4 : s4.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hl40 : l40.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (g24 g32 g40 g56 g64 pre d : List UInt8) (hg24 : g24.length = 8) (hg32 : g32.length = 8)
    (hg40 : g40.length = 8) (hg56 : g56.length = 8) (hg64 : g64.length = 8) (hd : d.length = 36 + 8 * n)
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat) (hcap2 : dlen.toNat + 36 + 8 * n ≤ cap.toNat)
    (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S) (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 104)) ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 152 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (root.At s.regs.rbx.toBitVec) ⋆ Eq (offsetBytes.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (ib.At (s.regs.rbx.toBitVec + 36))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ (Eq (g24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (g32.At (s.regs.rsp.toBitVec - 32))
        ⋆ Eq (g40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (g56.At (s.regs.rsp.toBitVec - 56))
        ⋆ Eq (g64.At (s.regs.rsp.toBitVec - 64))
        ⋆ Eq (pre.At dptr.toBitVec) ⋆ Eq (d.At (dptr.toBitVec + dlen.toBitVec)) ⋆ R))
    (hguard : guard.toNat + 16 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = 36 + 8 * n)
    (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hav : 32 + 8 * n ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 S) (hmsU : MakesliceC Heap ElfData.PrysmTarget.lvU64Type_addr 8 S)
    (hmm : MemmoveC S) (hmm2 : MemmoveC (S + 8)),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        ∀ (mem2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) mem2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx.toNat = dlen.toNat + 36 + 8 * n ∧ st'.data.regs.rcx = cap
              ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0 ∧
              (Eq ((pre ++ (root ++ offsetBytes ++ ib)).At dptr.toBitVec)
                ⋆ Eq ((root ++ offsetBytes ++ ib).At s.regs.rbx.toBitVec) ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp },
              zm, fl, mem2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf k⟩

end Prysm.DataColumnsByRootIdentifier
