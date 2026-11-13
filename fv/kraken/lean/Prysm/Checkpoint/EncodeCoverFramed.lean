import Prysm.Checkpoint.EncodeGrowAnySiteThreeCases
import Prysm.Checkpoint.EncodeCover

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: case covers with the exact frame

The covers `Encode.cover` and `Encode.reject_length_cover` (`Prysm/Checkpoint/EncodeCover.lean`) stay as they
are. These two theorems have the same premises (the epoch bytes are named `e8` with
`e8 = uintBytes 8 g.epoch`) and a conclusion without `⋆ True`: each disjunct is the exact postcondition
of the member theorem for that capacity range, with every caller-visible byte named (stack slots, the
caller's argument words, the 72-byte receiver, the root, the caller's array `pre ++ spare`, every new
block, the guard word, `Heap`, `R`).

`Encode.cover_framed` (`len(Root) = 32`), by the code's own capacity tests:

| disjunct | range | member | caller's array after |
| (1) | `len + 40 ≤ cap` | `Encode.fast_path` | `pre ++ serialize ++ spare[40:]` (written in place, returned) |
| (2) | `len + 8 ≤ cap < len + 40` | `Encode.grow_second_site` | `pre ++ epoch ++ spare[8:]` (epoch written before the root test); new block returned |
| (3A) | `cap < len + 8`, `C1 ≥ len + 40` | `Encode.grow_any_site_three_cases` (A) | unchanged `pre ++ spare` |
| (3B) | `cap < len + 8`, `C1 < len + 40`, heap left ≥ budget | `Encode.grow_any_site_three_cases` (B) | unchanged |
| (3C) | `cap < len + 8`, `C1 < len + 40`, heap left < budget | `Encode.grow_any_site_three_cases` (C) | unchanged; **not a return** |

(3C) is the entry of the second `runtime.growslice` call with the remaining heap below that call's
budget premise: the existing `GrowsliceC` form gives no lower bound on the remaining heap.
Its return is differential only. In (1), (2), (3A), (3B) the returned block is `pre ++ bs` with
`serialize desc g.toValue = .ok bs` (EthLib).

`Encode.reject_length_cover_framed` (`len(Root) ≠ 32`): `len + 8 ≤ cap`: the epoch bytes are in the
caller's array (`blk = dst`, written before the root length test); `cap < len + 8`: the caller's array `pre ++ spare` is unchanged and the
epoch bytes are in the new block `nb` from growslice only.
-/

open Machine Runtime Prysm.Checkpoint.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.Checkpoint

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.cover_framed (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (g : SszValue) (e8 : List UInt8) (he8g : e8 = (uintBytes 8 g.epoch.toNat).toList)
    (cst cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hl72 : l72.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ bs : Array UInt8, serialize desc g.toValue = .ok bs ∧ bs.toList = e8 ++ g.root.toList ∧
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
          ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
          ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
          -- (1) len + 40 ≤ cap: written into the caller's array and returned (Encode.fast_path)
          ((s.regs.rcx.toNat + 40 ≤ s.regs.rdi.toNat ∧ st.data.regs.rax = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rdi ∧
            ∃ (t u scr : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧
            (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
              ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
              ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
              ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
              ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
              ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
              ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
              ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
              ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
              ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
              ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
              ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
              ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
              ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
              ⋆ Eq ((pre ++ bs.toList).At s.regs.rbx.toBitVec)
              ⋆ Eq ((spare.drop 40).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 40))
              ⋆ Heap avail ⋆ R) st.data.dmem)
          -- (2) len + 8 ≤ cap < len + 40: epoch into the caller's array, then one growth (Encode.grow_second_site)
          ∨ (s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat ∧ s.regs.rdi.toNat < s.regs.rcx.toNat + 40
            ∧ nextSliceCap (s.regs.rcx.toNat + 40) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat ∧
            ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
              ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
              ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
            (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
              ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
              ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
              ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
              ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
              ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
              ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
              ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
              ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
              ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
              ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
              ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
              ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
              ⋆ Eq ((spare.drop 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
              ⋆ Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec)
              ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
              ⋆ Heap av' ⋆ R) st.data.dmem)
          -- (3A) cap < len + 8, the first new block holds the root (Encode.grow_any_site_three_cases (A))
          ∨ (s.regs.rdi.toNat < s.regs.rcx.toNat + 8
            ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat ∧
            ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
              ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
              ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
            (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
              ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
              ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
              ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
              ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
              ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
              ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
              ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
              ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
              ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
              ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
              ⋆ Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec)
              ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
              ⋆ Heap av' ⋆ R) st.data.dmem)
          -- (3B) cap < len + 8, first growth then second growth (Encode.grow_any_site_three_cases (B))
          ∨ (s.regs.rdi.toNat < s.regs.rcx.toNat + 8 ∧
            ∃ (t u scr spl' mid rest : List UInt8) (nb : BitVec 64) (C1 av1 av' : Nat), t.length = 8 ∧ u.length = 16
              ∧ scr.length = S ∧ spl'.length = 40
              ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ C1 ∧ C1 < s.regs.rcx.toNat + 40
              ∧ s.regs.rcx.toNat + 8 + mid.length = C1 ∧ av1 + C1 ≤ avail
              ∧ 2 * nextSliceCap (s.regs.rcx.toNat + 40) C1 + 8192 ≤ av1
              ∧ nextSliceCap (s.regs.rcx.toNat + 40) C1 ≤ st.data.regs.rcx.toNat
              ∧ s.regs.rcx.toNat + 40 + rest.length = st.data.regs.rcx.toNat
              ∧ av' + st.data.regs.rcx.toNat ≤ av1 ∧
            (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
              ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec - 16))
              ⋆ Eq ((Int.toBytes 8 st.data.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 24))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 40).toInt).At (s.regs.rsp.toBitVec - 32))
              ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
              ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
              ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
              ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
              ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 63)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
              ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
              ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
              ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
              ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
              ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
              ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
              ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
              ⋆ Eq (pre.At nb) ⋆ Eq (e8.At (nb + s.regs.rcx.toBitVec)) ⋆ Eq (mid.At (nb + s.regs.rcx.toBitVec + 8))
              ⋆ Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec)
              ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 40))
              ⋆ Heap av' ⋆ R) st.data.dmem)))
        -- (3C) cap < len + 8, C1 < len + 40, heap left below the second call's budget: entry of that call
        ∨ (st.pc = label "runtime.growslice" ∧ s.regs.rdi.toNat < s.regs.rcx.toNat + 8
          ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 120 }
          ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8#64 } ∧ st.data.regs.r14 = s.regs.r14
          ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40 ∧ st.data.regs.rdi.toNat = 32
          ∧ st.data.regs.rsi.toBitVec = ElfData.CheckpointAndEpoch.e2eU8Type_addr
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
          ∧ st.data.regs.rcx.toNat < s.regs.rcx.toNat + 40 ∧
          ∃ (t u scr spl' mid : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
            ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 8 + mid.length = st.data.regs.rcx.toNat
            ∧ av' + st.data.regs.rcx.toNat ≤ avail
            ∧ av' < 2 * nextSliceCap (s.regs.rcx.toNat + 40) st.data.regs.rcx.toNat + 8192 ∧
          (Eq ((Int.toBytes 8 (Host.addrOf (k + 50)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
            ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
            ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56))
            ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 8).toInt).At (s.regs.rsp.toBitVec - 72))
            ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
            ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
            ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
            ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
            ⋆ Eq (pre.At st.data.regs.rax.toBitVec) ⋆ Eq (e8.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec))
            ⋆ Eq (mid.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
            ⋆ Heap av' ⋆ R) st.data.dmem))
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, by rw [SszValue.enc_toList, he8g], ?_⟩
  rw [SszValue.enc_toList, ← he8g]
  have he8 : e8.length = 8 := by rw [he8g]; simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  generalize g.root.toList = root at *
  clear he8g
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap63 hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hL : rcx.toNat + 40 < 2 ^ 64 := by unfold maxAlloc at hmax; omega
  by_cases c1 : rcx.toNat + 40 ≤ rdi.toNat
  · -- (1) fast path
    have htl : 40 ≤ spare.length := by omega
    rw [Encode.grow_first_site_split rbx.toBitVec rcx.toBitVec pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (Encode.fast_path k hk hf cst _ cC ctl _ pre (spare.take 8) ((spare.drop 8).take 32)
      hcst he8 hcC hctl hroot (by simp only [List.length_take]; omega)
      (by simp only [List.length_take, List.length_drop]; omega) p _ ra guard hpre fp s2 l16 l24 l32 t40 t30 rslot
      hfp h2 hl16 hl24 hl32 ht40 ht30 hrs _ S scratch hsc (by dsimp only; ecancel) hguard hsp c1 hcap63 hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, Hm⟩
    refine Or.inl ⟨e1, e3, e5, e6, e7, e8', e9, Or.inl ⟨c1, e2, e4, t, u, scr, ht, hu, hscr, ?_⟩⟩
    rw [Encode.cover_out rbx.toBitVec rcx pre _ _ hpre he8 hroot hL]
    ecancel
  by_cases c2 : rcx.toNat + 8 ≤ rdi.toNat
  · -- (2) first append fits, second grows
    have htl : 8 ≤ spare.length := by omega
    rw [Encode.grow_any_site_split8 rbx.toBitVec rcx pre spare hpre htl (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 40) rdi.toNat (by omega)
    have hng := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
    refine eventually_mono (Encode.grow_second_site k hk hf cst _ cC ctl _ pre (spare.take 8)
      hcst he8 hcC hctl hroot (by simp only [List.length_take]; omega) p _ ra guard hpre fp s2 l16 l24 l32 t40 t30
      l72 spl rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hl72 hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel)
      hguard hsp c2 (by dsimp only; omega) (by dsimp only; omega) hmax hgs hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hav', Hm⟩
    refine Or.inl ⟨e1, e2, e4, e5, e6, e7, e8', Or.inr (Or.inl ⟨c2, by omega, e3, t, u, scr, spl', rest, av', ht, hu,
      hscr, hspl', hrest, hav', ?_⟩)⟩
    rw [Encode.cover_out _ rcx pre _ _ hpre he8 hroot hL]
    ecancel
  · -- (3) first append grows
    have hlc : rcx.toNat ≤ rdi.toNat := by omega
    have c3 : rdi.toNat < rcx.toNat + 8 := by omega
    rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
    refine eventually_mono (Encode.grow_any_site_three_cases k hk hf cst _ cC ctl _ pre
      hcst he8 hcC hctl hroot p _ ra guard hpre fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot hfp h1 h2 h3 hl16 hl24
      hl32 ht40 ht30 hl72 hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hsp hlc
      c3 (by dsimp only; omega) hmax hgs hmm) ?_
    rintro st (⟨e1, e2, e3, e4, e5, e6, e7, t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hnc, hav', Hm⟩
      | ⟨e1, e2, e3, e4, e5, e6, e7, t, u, scr, spl', mid, rest, nb, C1, av1, av', ht, hu, hscr, hspl', hnc1, hlt,
          hmid, hav1, hb2, hnc2, hrest, hav', Hm⟩
      | ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, spl', mid, av', ht, hu, hscr, hspl', hmid, hav', hlow, Hm⟩)
    · refine Or.inl ⟨e1, e2, e3, e4, e5, e6, e7, Or.inr (Or.inr (Or.inl ⟨c3, hnc, t, u, scr, spl', rest, av', ht, hu,
        hscr, hspl', hrest, hav', ?_⟩))⟩
      rw [Encode.cover_out _ rcx pre _ _ hpre he8 hroot hL, Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)]
      ecancel
    · refine Or.inl ⟨e1, e2, e3, e4, e5, e6, e7, Or.inr (Or.inr (Or.inr ⟨c3, t, u, scr, spl', mid, rest, nb, C1, av1,
        av', ht, hu, hscr, hspl', hnc1, hlt, hmid, hav1, hb2, hnc2, hrest, hav', ?_⟩))⟩
      rw [Encode.cover_out _ rcx pre _ _ hpre he8 hroot hL, Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)]
      ecancel
    · refine Or.inr ⟨e1, c3, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, spl', mid, av', ht, hu, hscr, hspl', hmid,
        hav', hlow, ?_⟩
      rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)]
      ecancel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.reject_length_cover_framed (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh marshalSSZTo k)
    (cst e8 cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8) (hcC : cC.length = 8)
    (hctl : ctl.length = 32)
    (p : BitVec 64) (rl e0 e1 : UInt64) (hrl : rl ≠ 32)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8)
    (hl24 : l24.length = 8) (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16)
    (hl72 : l72.length = 8) (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        -- len + 8 ≤ cap: the epoch bytes are in the caller's array (blk = dst, written before the root length test); no runtime call
        ((s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat ∧ ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
            ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
            ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 112))
            ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24))
            ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
            ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (e8.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
            ⋆ Eq ((spare.drop 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
            ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
            ⋆ Heap avail ⋆ R) st.data.dmem)
        -- cap < len + 8: the caller's array is unchanged; the epoch bytes are in the new block nb only
        ∨ (s.regs.rdi.toNat < s.regs.rcx.toNat + 8 ∧
          ∃ (t u scr spl' mid : List UInt8) (nb : BitVec 64) (C1 av' : Nat), t.length = 8 ∧ u.length = 16
            ∧ scr.length = S ∧ spl'.length = 40 ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ C1
            ∧ s.regs.rcx.toNat + 8 + mid.length = C1 ∧ av' + C1 ≤ avail ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 64))
            ⋆ Eq (t.At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
            ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 112))
            ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 28)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 120))
            ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 rl.toBitVec.toInt).At (s.regs.rax.toBitVec + 24))
            ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
            ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
            ⋆ Eq (pre.At nb) ⋆ Eq (e8.At (nb + s.regs.rcx.toBitVec)) ⋆ Eq (mid.At (nb + s.regs.rcx.toBitVec + 8))
            ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
            ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec)
            ⋆ Heap av' ⋆ R) st.data.dmem)))
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  by_cases c2 : rcx.toNat + 8 ≤ rdi.toNat
  · have htl : 8 ≤ spare.length := by omega
    rw [Encode.grow_any_site_split8 rbx.toBitVec rcx pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (Encode.reject_length k hk hf cst e8 cC ctl pre (spare.take 8) hcst he8 hcC hctl
      (by simp only [List.length_take]; omega) p rl hrl _ ra guard e0 e1 hpre fp s2 t40 t30 hfp h2 ht40 ht30 _
      (by dsimp only; ecancel) hguard hsp c2) ?_
    rintro st ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, t, u, ht, hu, Hm⟩
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, Or.inl ⟨c2, t, u, ht, hu, ?_⟩⟩
    ecancel
  · have hlc : rcx.toNat ≤ rdi.toNat := by omega
    have c3 : rdi.toNat < rcx.toNat + 8 := by omega
    rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
    refine eventually_mono (Encode.reject_length_grow_first_site k hk hf cst e8 cC ctl pre hcst he8 hcC hctl p _ ra guard
      hpre fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 ht40 ht30 hl72 hspl hrs _ S
      scratch hsc Heap avail rl e0 e1 hrl (by dsimp only; ecancel) hguard hsp hlc c3
      (by dsimp only; omega) hmax hgs) ?_
    rintro st ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, t, u, scr, spl', mid, nb, C1, av', ht, hu, hscr, hspl', hnc, hmid,
      hav', Hm⟩
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, Or.inr ⟨c3, t, u, scr, spl', mid, nb, C1, av', ht, hu, hscr, hspl',
      hnc, hmid, hav', ?_⟩⟩
    rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)]
    ecancel

end Prysm.Checkpoint
