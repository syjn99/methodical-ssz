import E2eEnc.StmtEnc

/-!
# Frozen STATEMENTS of the encoder for every capacity (any-site grow path: growslice at any site, any number of times)

Statements only. Frozen at their commit; a later change needs a new name and a reason.
The fast path and the first-site grow path (site 1 only) of
`StmtEnc.lean` are the special cases with no growth and with one growth at site 1.

- `dst` is `(dp, len, cap)` with the old block `pre ‖ spare` (`len + |spare| = cap`).
- Any of the n + 2 append sites (site 1 `append(BlockRoot)`, site 2 `WriteOffset`, the n `AppendUint64`) may call
  `growslice` (contract `GrowsliceC Heap e2eU8Type_addr 1 S`). Each call needs `2·nextSliceCap + 8192` free bytes and
  takes at most that many; with `newLen ≤ L = len + 36 + 8n`, `nextSliceCap ≤ 2·L + 192`, so `K = 4·L + 8576` per
  site suffices. The heap premise is `(n + 2)·K ≤ avail`.
- The result block holds `pre ‖ root ‖ offset 36 ‖ cb` and a named rest. The old blocks of every growth (the copied
  prefix and the unused spare bytes) stay allocated: they are the existential frame `G`. With no growth, `G` is empty
  and the result block is the old block.
- Slots written only on growth paths (x + 24, x − 16, x − 48, x − 72, the 40-byte spill area) are in the premise and
  existential in the conclusion.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eEnc.Code
variable [Host]

namespace E2eEnc

/-- **Any-site grow path: every capacity (machine).** -/
def dc_marshal_any_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
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
    (hbud : (n + 2) * (4 * (s.regs.rcx.toNat + 36 + 8 * n) + 8576) ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
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
          ⋆ Eq ((pre ++ root ++ dcOff ++ cb ++ rest).At st.data.regs.rax.toBitVec)
          ⋆ G ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Any-site grow path against EthLib.** -/
def dc_marshal_any_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (g : PDc) (hnb : nb.toNat = g.cols.length)
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
      ⋆ Eq (g.root.toList.At pr) ⋆ Eq ((Spec.u64Bytes g.cols).toList.At pc)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hbud : (g.cols.length + 2) * (4 * (s.regs.rcx.toNat + 36 + 8 * g.cols.length) + 8576) ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    ∃ bs, serialize prysmDcDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + bs.size ∧ s.regs.rcx.toNat + bs.size ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end E2eEnc
