import Runtime.Contracts
import TestTarget.FunctionSpecs
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import E2eList.Data
import E2eList.Defs
import E2eScal.H4Code
import E2eDep.Code

/-!
# Hand STATEMENTS of `(*v1alpha1.Deposit).UnmarshalSSZ` (statements only, no proof)

Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Selection: the same family as HistoricalBatch (a `Vector[Bytes32, N]` field as `[][]byte`), not forbidden, no
existing proof. The only such types without a pointer field are HistoricalBatch and SyncCommittee; Deposit has the
one pointer field whose decoder already has a proof (`E2eScal.H4.dd_e2e_accept_main`, Deposit_Data).

    func (c *Deposit) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 1240 { return ssz.ErrSize }
        c.Proof = make([][]byte, 33)
        for i := 0; i < 33; i++ {
            tmp := make([]byte, 0, 32); tmp = append(tmp, buf[i*32:(1+i)*32]...); c.Proof[i] = tmp }
        c.Data = new(Deposit_Data)
        if err = c.Data.UnmarshalSSZ(buf[1056:1240]); err != nil { return fmt.Errorf("Data: %w", err) }
        return err }

Receiver: protoc struct, IR `go_fields`: `state` 0, `Proof` 8 (ptr, len, cap), `Data` 32 (pointer); the rest in `R`.
Frame (`.S`, x = entry rsp): `sub $0x58`, sp = x − 96; spills `0x68(%rsp)` = x + 8 (rax), `0x70(%rsp)` = x + 16 (rbx),
`0x80(%rsp)` = x + 32 (rdi); loop locals `0x28` = x − 56 (i + 1), `0x30` = x − 48 (32i), `0x38` = x − 40 (i),
`0x40` = x − 32 (element pointer); `0x0…0x17` = x − 96 (24 bytes `spl`: the callees' spill area); runtime call
return slot x − 104; `lo` = the `Sd + 48` scratch bytes below it. The Deposit_Data decoder (machine code in the
host, at `kd`) is called with rsp = x − 104: its spill words are the first 16 bytes of `spl`, its frame (40 bytes
and its own `Sd` scratch) is our `lo`. Hence `guard + 104 < x`.
Calls: makeslice of the backing array (`lvSliceType_addr`, esz 24, cnt 33), 33 uint8 makeslice + memmove pairs,
newobject of the Deposit_Data object (`depDataType_addr`, 120 bytes), the Deposit_Data decoder (176 heap bytes).
Heap: 24·33 + 32·33 + 120 + 176 = 2144. The last call is directive 105, so the return slot holds directive 106.
Error paths not on the accept path: `fmt.errorf` wrap (Deposit_Data accepts every 184-byte input), panicBounds.
Size reject: directives 2–10, `cmp $0x4d8,%rcx; jne L_85` taken, 31–36.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eList E2eDep.Code
variable [Host]

namespace E2eDep

/-- **Deposit size reject (machine).** `len(buf) ≠ 1240`: the decoder returns the two words of `ssz.ErrSize`. -/
def dep_reject_size_stmt : Prop :=
  ∀ (k : Nat) (hk : DepUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DepUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 1240),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Deposit accept (machine).** On a 1240-byte input `proofs.flatten ‖ pk ‖ wc ‖ amt ‖ sig` (33 blocks of 32 bytes,
then the 184 bytes of a Deposit_Data) the decoder returns nil; the receiver holds a fresh `[][]byte` Proof
(len = cap = 33, headers `(ps[i], 32, 32)`, element i = `proofs[i]`) and a fresh Deposit_Data object `po` decoded
by the real Deposit_Data decoder (the postcondition of `E2eScal.H4.dd_e2e_accept_main`: PublicKey = pk,
WithdrawalCredentials = wc, Amount = amt, Signature = sig); input, `state`, the spills, the caller's frame `R`
and the stack guard are unchanged; 2144 heap bytes are used. -/
def dep_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : DepUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DepUnmarshal k)
    (kd : Nat) (hkd : E2eScal.H4Code.DdUnmarshal.IsInfixAt Host.prog kd)
    (hfd : LabelsFresh E2eScal.H4Code.DdUnmarshal kd)
    (proofs : List (List UInt8)) (hps : proofs.length = 33) (hp : ∀ e ∈ proofs, e.length = 32)
    (pk wc amt sig : List UInt8) (hpk : pk.length = 48) (hwc : wc.length = 32) (hamt : amt.length = 8)
    (hsig : sig.length = 96)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hlI1 : lI1.length = 8) (hlD : lD.length = 8) (hlI : lI.length = 8) (hlP : lP.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (hast : ast.length = 8) (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8) (haD : aD.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 48)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (lI1.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (lD.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (lI.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (lP.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 (Sd + 48)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (proofs.flatten.At s.regs.rbx.toBitVec)
      ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 1056)) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 1104))
      ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 1136)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 1144))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aD.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 104 < s.regs.rsp.toNat) (hlen : s.regs.rcx = 1240) (hav : 2144 ≤ avail)
    (hmsA : MakesliceC Heap E2eList.Data.lvSliceType_addr 24 (Sd + 48))
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (Sd + 48)) (hmm : MemmoveC (Sd + 48))
    (hno : NewobjectC Heap depDataType_addr 120 (Sd + 48))
    (hmsD : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 Sd) (hmmD : MemmoveC Sd),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A po p1 p2 p3 : BitVec 64) (ps : List (BitVec 64)) (lI1' lD' lI' lP' spl' lo' : List UInt8),
          ps.length = 33 ∧ lI1'.length = 8 ∧ lD'.length = 8 ∧ lI'.length = 8 ∧ lP'.length = 8
          ∧ spl'.length = 24 ∧ lo'.length = Sd + 48 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (lI1'.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (lD'.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lI'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (lP'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 106)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 (Sd + 48)))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 2144)
          ⋆ Eq (proofs.flatten.At s.regs.rbx.toBitVec)
          ⋆ Eq (pk.At (s.regs.rbx.toBitVec + 1056)) ⋆ Eq (wc.At (s.regs.rbx.toBitVec + 1104))
          ⋆ Eq (amt.At (s.regs.rbx.toBitVec + 1136)) ⋆ Eq (sig.At (s.regs.rbx.toBitVec + 1144))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 33).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 33).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 po.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((lvHdrs 32 ps).At A) ⋆ lvElems ps proofs
          ⋆ Eq ((List.replicate 8 0).At po)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (po + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (po + 16)) ⋆ Eq ((Int.toBytes 8 48).At (po + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (po + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (po + 40)) ⋆ Eq ((Int.toBytes 8 32).At (po + 48))
          ⋆ Eq (amt.At (po + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (po + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (po + 72)) ⋆ Eq ((Int.toBytes 8 96).At (po + 80))
          ⋆ Eq ((List.replicate 32 0).At (po + 88))
          ⋆ Eq (pk.At p1) ⋆ Eq (wc.At p2) ⋆ Eq (sig.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eDep
