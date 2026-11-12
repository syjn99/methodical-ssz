import E2eDep.Stmt
import E2eScal.DdSpec

/-!
# Hand STATEMENTS of the Deposit spec companions (statements only, no proof)

Frozen at their commit. The hand `Desc` below is written from consensus-specs phase0 BEFORE the producer's Desc of
`(v1alpha1, Deposit)` is generated or printed:

    DEPOSIT_CONTRACT_TREE_DEPTH = 32
    class Deposit(Container):
        proof: Vector[Bytes32, DEPOSIT_CONTRACT_TREE_DEPTH + 1]   # 33
        data: DepositData

`DepositData` is the hand `Desc` `E2e.prysmDdDesc` (imported). `PDep` is the SSZ content of a Go
`v1alpha1.Deposit` whose byte fields have the spec lengths; `depEnc` is its 1240-byte SSZ encoding.
Shapes: `E2eHb.hb_accept_spec_stmt`, `hb_reject_size_spec_stmt`, `hb_reject_complete_stmt`.
-/

open Machine Runtime TestTarget E2e EthLib.Serialization.Ssz E2eList E2eDep.Code
variable [Host]

namespace E2eDep

/-- consensus-specs phase0 `Deposit`. -/
def prysmDepDesc : Desc := .container ["proof", "data"] [.vector (.byteVector 32) 33, prysmDdDesc]

/-- SSZ content of a Go `v1alpha1.Deposit` (33 proof roots of 32 bytes, Deposit_Data). -/
structure PDep where
  proof : Vector (Vector UInt8 32) 33
  data : PDd

/-- The 33 proof roots as byte lists, in order. -/
def PDep.proofs (g : PDep) : List (List UInt8) := g.proof.toList.map (·.toList)

def PDep.toValue (g : PDep) : Value :=
  .seq [.seq (g.proof.toList.map fun p => .bytes p.toArray), g.data.toValue]

/-- `proof[0] ‖ … ‖ proof[32] ‖ pubkey ‖ withdrawalCredentials ‖ amount ‖ signature`. -/
def depEnc (g : PDep) : Array UInt8 := g.proofs.flatten.toArray ++ pddEnc g.data

/-- **Deposit accept (spec).** If EthLib accepts `bsA` against `prysmDepDesc` as `v`, there is `g : PDep` with
`g.toValue = v` and `bsA = depEnc g`; with the input chunks of that `g` the machine code returns nil and the
receiver holds `g` (postcondition of `dep_accept_stmt`). -/
def dep_accept_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DepUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DepUnmarshal k)
    (kd : Nat) (hkd : E2eScal.H4Code.DdUnmarshal.IsInfixAt Host.prog kd)
    (hfd : LabelsFresh E2eScal.H4Code.DdUnmarshal kd)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmDepDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 lI1 lD lI lP spl rslot lo ast aP aL aC aD : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hlI1 : lI1.length = 8) (hlD : lD.length = 8) (hlI : lI.length = 8) (hlP : lP.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (hast : ast.length = 8) (haP : aP.length = 8) (haL : aL.length = 8) (haC : aC.length = 8) (haD : aD.length = 8)
    (R : DataMem → Prop) (Sd : Nat) (hSd : Sd < 2 ^ 60) (hlo : lo.length = Sd + 48)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PDep, bsA = depEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (lI1.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (lD.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (lI.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (lP.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 104 - BitVec.ofNat 64 (Sd + 48)))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.proofs.flatten.At s.regs.rbx.toBitVec)
      ⋆ Eq (g.data.pubkey.toList.At (s.regs.rbx.toBitVec + 1056)) ⋆ Eq (g.data.withdrawalCredentials.toList.At (s.regs.rbx.toBitVec + 1104))
      ⋆ Eq ((uintBytes 8 g.data.amount.toNat).toList.At (s.regs.rbx.toBitVec + 1136)) ⋆ Eq (g.data.signature.toList.At (s.regs.rbx.toBitVec + 1144))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aD.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 104 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 2144 ≤ avail)
    (hmsA : MakesliceC Heap E2eList.Data.lvSliceType_addr 24 (Sd + 48))
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (Sd + 48)) (hmm : MemmoveC (Sd + 48))
    (hno : NewobjectC Heap depDataType_addr 120 (Sd + 48))
    (hmsD : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 Sd) (hmmD : MemmoveC Sd),
    ∃ g : PDep, g.toValue = v ∧ bsA = depEnc g ∧
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
          ⋆ Eq (g.proofs.flatten.At s.regs.rbx.toBitVec)
          ⋆ Eq (g.data.pubkey.toList.At (s.regs.rbx.toBitVec + 1056)) ⋆ Eq (g.data.withdrawalCredentials.toList.At (s.regs.rbx.toBitVec + 1104))
          ⋆ Eq ((uintBytes 8 g.data.amount.toNat).toList.At (s.regs.rbx.toBitVec + 1136)) ⋆ Eq (g.data.signature.toList.At (s.regs.rbx.toBitVec + 1144))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 33).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 33).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 po.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((lvHdrs 32 ps).At A) ⋆ lvElems ps g.proofs
          ⋆ Eq ((List.replicate 8 0).At po)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (po + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (po + 16)) ⋆ Eq ((Int.toBytes 8 48).At (po + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (po + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (po + 40)) ⋆ Eq ((Int.toBytes 8 32).At (po + 48))
          ⋆ Eq ((uintBytes 8 g.data.amount.toNat).toList.At (po + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (po + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (po + 72)) ⋆ Eq ((Int.toBytes 8 96).At (po + 80))
          ⋆ Eq ((List.replicate 32 0).At (po + 88))
          ⋆ Eq (g.data.pubkey.toList.At p1) ⋆ Eq (g.data.withdrawalCredentials.toList.At p2) ⋆ Eq (g.data.signature.toList.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Deposit size reject (spec).** `bs.size ≠ 1240`: EthLib rejects, and the machine code returns the two words
of `ssz.ErrSize`. -/
def dep_reject_size_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DepUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DepUnmarshal k)
    (bs : Array UInt8) (hbs : bs.size ≠ 1240)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize prysmDepDesc bs = .error e) ∧
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

/-- **Deposit reject completeness (spec).** Every input that EthLib rejects has `size ≠ 1240`: the path condition
of the decoder's one reject site (the Deposit_Data decoder accepts every 184-byte input). -/
def dep_reject_complete_stmt : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize prysmDepDesc bs = .ok v) → bs.size ≠ 1240

end E2eDep
