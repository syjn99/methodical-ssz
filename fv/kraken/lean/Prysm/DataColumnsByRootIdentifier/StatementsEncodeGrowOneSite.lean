import Prysm.DataColumnsByRootIdentifier.StatementsEncode
import Prysm.DataColumnsByRootIdentifier.Code

/-!
# Statements of the encoder with one growth at any one site

Statements only. A change to a statement needs a new name and a reason.
The fast path and the first-site grow path (site 1 only) of
`Prysm/DataColumnsByRootIdentifier/StatementsEncode.lean` are the special cases with no growth and with one growth at site 1.

- `dst` is `(dp, len, cap)` with the old block `pre ‖ spare` (`len + |spare| = cap`).
- Any one of the n + 2 append sites (site 1 `append(BlockRoot)`, site 2 `WriteOffset`, the n `AppendUint64`) may call
  `growslice` (contract `GrowsliceContract Heap typeUint8_addr 1 S`).
- `hbud : K ≤ avail` gives the heap for one growth, with K = 4·(len + 36 + 8n) + 8576.
  A call needs `2·nextSliceCap + 8192` free bytes and takes at most that many.
  With `newLen ≤ L = len + 36 + 8n`, `nextSliceCap ≤ 2·L + 192`, so K is enough.
- `hone`: for every new length `m ≤ L` above `cap`, `L ≤ nextSliceCap m cap`.
  So the first site that grows gets a capacity that holds the whole output, and no second growth occurs.
- The result block holds `pre ‖ root ‖ offset 36 ‖ cb` and a named rest.
  The old block of a growth (the copied prefix and the unused spare bytes) stays allocated: it is the existential frame `G`.
  With no growth, `G` is empty and the result block is the old block.
- Slots written only on growth paths (x + 24, x − 16, x − 48, x − 72, the 40-byte spill area) are in the premise and
  existential in the conclusion.

Reason for `hone`: `GrowsliceContract` bounds the heap after a call only from above (`avail' + esz·newCap ≤ avail`).
After one growth, nothing bounds the remaining heap from below.
So the budget premise of a second `growslice` call does not follow from the contract forms of `Runtime/Contracts.lean`.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

/-- **One-growth path: growth at any one site (machine).** -/
def Encode.grow_one_site_statement : Prop :=
  ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (n : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (root cb pre spare : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8 * n)
    (hpre : pre.length = s.regs.rcx.toNat) (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 l32 l40 l48 l56 l64 l72 spl rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hbud : 4 * (s.regs.rcx.toNat + 36 + 8 * n) + 8576 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hone : ∀ m, m ≤ s.regs.rcx.toNat + 36 + 8 * n → s.regs.rdi.toNat < m →
      s.regs.rcx.toNat + 36 + 8 * n ≤ nextSliceCap m s.regs.rdi.toNat)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36 + 8 * n
        ∧ s.regs.rcx.toNat + 36 + 8 * n ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (s3' l16' l24' l32' l40' l48' l56' l64' l72' spl' rslot' scr rest : List UInt8) (av' : Nat)
          (G : DataMem → Prop), s3'.length = 8 ∧ l16'.length = 8
          ∧ l24'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8 ∧ l48'.length = 8 ∧ l56'.length = 8
          ∧ l64'.length = 8 ∧ l72'.length = 8 ∧ spl'.length = 40 ∧ rslot'.length = 8 ∧ scr.length = S
          ∧ s.regs.rcx.toNat + 36 + 8 * n + rest.length = st.data.regs.rcx.toNat
          ∧ av' ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (s3'.At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (l16'.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24'.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l48'.At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (l56'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l64'.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72'.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
          ⋆ Eq ((pre ++ root ++ offsetBytes ++ cb ++ rest).At st.data.regs.rax.toBitVec)
          ⋆ G ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **One-growth path against EthLib.** -/
def Encode.grow_one_site_spec_statement : Prop :=
  ∀ (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (g : SszValue) (hnb : nb.toNat = g.cols.length)
    (pre spare : List UInt8)
    (hpre : pre.length = s.regs.rcx.toNat) (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 l32 l40 l48 l56 l64 l72 spl rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (g.root.toList.At pr) ⋆ Eq ((Spec.uint64Bytes g.cols).toList.At pc)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hbud : 4 * (s.regs.rcx.toNat + 36 + 8 * g.cols.length) + 8576 ≤ avail)
    (hone : ∀ m, m ≤ s.regs.rcx.toNat + 36 + 8 * g.cols.length → s.regs.rdi.toNat < m →
      s.regs.rcx.toNat + 36 + 8 * g.cols.length ≤ nextSliceCap m s.regs.rdi.toNat) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S),
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + bs.size ∧ s.regs.rcx.toNat + bs.size ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Prysm.DataColumnsByRootIdentifier
