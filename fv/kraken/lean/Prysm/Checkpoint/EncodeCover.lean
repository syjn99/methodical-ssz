import Prysm.Checkpoint.EncodeGrowAnySite
import Prysm.Checkpoint.EncodeSpec

/-!
# `(*v1alpha1.Checkpoint).MarshalSSZTo`: case cover over every capacity, against EthLib

`Encode.cover` (`len(Root) = 32`): for every `len ≤ cap` (one premise shape: the caller's
backing array `pre ++ spare`, `len(pre) = len`, `len + len(spare) = cap`) the code takes one of three
proved paths, by the code's own capacity tests:

| capacity range           | theorem                              | result                                |
| `len + 40 ≤ cap`         | `Encode.fast_path`                | returns `dst ++ serialize`            |
| `len + 8 ≤ cap < len+40` | `Encode.grow_second_site`          | returns `dst ++ serialize` (new block)|
| `cap < len + 8`          | `Encode.grow_any_site`       | left: returns `dst ++ serialize`;     |
|                          |                                      | right: reaches the 2nd growslice call |

The conclusion is the disjunction "returned with `pre ++ serialize desc g.toValue` at the
returned pointer (frame `R` and the root unchanged, the rest `⋆ True`; the exact frame accounting is in
the three theorems)" or "at the entry of the second `runtime.growslice` call" — the run after that call
is not proved (the `GrowsliceC` contract form does not chain two calls: it bounds the remaining heap only from above).

`Encode.reject_length_cover` (`len(Root) ≠ 32`): for every `len ≤ cap`, `Encode.reject_length`
(`len + 8 ≤ cap`) or `Encode.reject_length_grow_first_site` (`cap < len + 8`): the result is
`(nil, ErrBytesLength words)`, and some block (the caller's or the growslice one) holds
`pre ++ epoch` (the epoch bytes are written before the root length test). Heap budget for both: `4·len + 8736 ≤ avail` (covers the one growslice call
of every proved path).
-/

open Machine Runtime Prysm.Checkpoint.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.Checkpoint

theorem Encode.cover_out (b : BitVec 64) (L : UInt64) (pre e8 root : List UInt8) (hpre : pre.length = L.toNat)
    (he8 : e8.length = 8) (hroot : root.length = 32) (hb : L.toNat + 40 < 2 ^ 64) :
    Eq ((pre ++ (e8 ++ root)).At b) = Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) ⋆ Eq (root.At (b + L.toBitVec + 8)) := by
  rw [at_app pre _ (b := b + L.toBitVec) (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp)
      (by simp only [List.length_append, hpre, he8, hroot]; omega),
    at_app e8 root (b := b + L.toBitVec + 8) (by rw [he8]; rfl) (by simp only [he8, hroot]; omega)]
  simp only [Std.ExtHashMap.sep_assoc]

theorem Encode.cover_pre (b : BitVec 64) (L : UInt64) (pre spare : List UInt8) (hpre : pre.length = L.toNat)
    (hb : pre.length + spare.length < 2 ^ 64) :
    Eq ((pre ++ spare).At b) = Eq (pre.At b) ⋆ Eq (spare.At (b + L.toBitVec)) :=
  at_app pre spare (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp) (by omega)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.cover (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (g : SszValue) (cst cC ctl pre spare : List UInt8) (hcst : cst.length = 8) (hcC : cC.length = 8)
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
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveC S) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => (st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
          ∧ s.regs.rcx.toNat + 40 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
          ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
          ∧ (Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec) ⋆ Eq (g.root.toList.At p) ⋆ R ⋆ fun _ => True)
            st.data.dmem)
        ∨ (st.pc = label "runtime.growslice" ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 40
          ∧ st.data.regs.rdi.toNat = 32))
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, ?_⟩
  rw [SszValue.enc_toList]
  have he8 : (uintBytes 8 g.epoch.toNat).toList.length = 8 := by simp [Spec.uintBytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  generalize (uintBytes 8 g.epoch.toNat).toList = e8 at *
  generalize g.root.toList = root at *
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap63 hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hL : rcx.toNat + 40 < 2 ^ 64 := by unfold maxAlloc at hmax; omega
  by_cases c1 : rcx.toNat + 40 ≤ rdi.toNat
  · -- fast path
    have htl : 40 ≤ spare.length := by omega
    rw [Encode.grow_first_site_split rbx.toBitVec rcx.toBitVec pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (Encode.fast_path k hk hf cst _ cC ctl _ pre (spare.take 8) ((spare.drop 8).take 32)
      hcst he8 hcC hctl hroot (by simp only [List.length_take]; omega)
      (by simp only [List.length_take, List.length_drop]; omega) p _ ra guard hpre fp s2 l16 l24 l32 t40 t30 rslot
      hfp h2 hl16 hl24 hl32 ht40 ht30 hrs _ S scratch hsc (by dsimp only; ecancel) hguard hsp c1 hcap63 hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, scr, ht, hu, hscr, Hm⟩
    refine Or.inl ⟨e1, e3, by rw [e4]; exact c1, e5, e6, e7, e8', e9, ?_⟩
    rw [e2]
    apply sep_true
    rw [Encode.cover_out rbx.toBitVec rcx pre _ _ hpre he8 hroot hL]
    ecancel
  by_cases c2 : rcx.toNat + 8 ≤ rdi.toNat
  · -- first append fits, second grows
    have htl : 8 ≤ spare.length := by omega
    rw [Encode.grow_any_site_split8 rbx.toBitVec rcx pre spare hpre htl (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 40) rdi.toNat (by omega)
    have hng := nextSliceCap_ge (rcx.toNat + 40) rdi.toNat
    refine eventually_mono (Encode.grow_second_site k hk hf cst _ cC ctl _ pre (spare.take 8)
      hcst he8 hcC hctl hroot (by simp only [List.length_take]; omega) p _ ra guard hpre fp s2 l16 l24 l32 t40 t30
      l72 spl rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hl72 hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel)
      hguard hsp c2 (by dsimp only; omega) (by dsimp only; omega) hmax hgs hmm) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hav', Hm⟩
    refine Or.inl ⟨e1, e2, by dsimp only at hrest ⊢; omega, e4, e5, e6, e7, e8', ?_⟩
    apply sep_true
    rw [Encode.cover_out _ rcx pre _ _ hpre he8 hroot hL]
    ecancel
  · -- first append grows
    have hlc : rcx.toNat ≤ rdi.toNat := by omega
    rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
    refine eventually_mono (Encode.grow_any_site k hk hf cst _ cC ctl _ pre
      hcst he8 hcC hctl hroot p _ ra guard hpre fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot hfp h1 h2 h3 hl16 hl24
      hl32 ht40 ht30 hl72 hspl hrs _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hsp hlc
      (by dsimp only; omega) (by dsimp only; omega) hmax hgs hmm) ?_
    rintro st (⟨e1, e2, e3, e4, e5, e6, e7, t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hnc, hav', Hm⟩
      | ⟨e1, e2, e3, e4, e5, e6, e7, -, -, -⟩)
    · refine Or.inl ⟨e1, e2, by dsimp only at hrest ⊢; omega, e3, e4, e5, e6, e7, ?_⟩
      apply sep_true
      rw [Encode.cover_out _ rcx pre _ _ hpre he8 hroot hL]
      ecancel
    · exact Or.inr ⟨e1, e5, e6⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem Encode.reject_length_cover (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
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
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hbud : 4 * s.regs.rcx.toNat + 8736 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.PrysmTarget.typeUint8_addr 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ blk : BitVec 64, (Eq (pre.At blk) ⋆ Eq (e8.At (blk + s.regs.rcx.toBitVec))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R
          ⋆ fun _ => True) st.data.dmem)
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
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, rbx.toBitVec, ?_⟩
    apply sep_true
    ecancel
  · have hlc : rcx.toNat ≤ rdi.toNat := by omega
    rw [Encode.cover_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
    refine eventually_mono (Encode.reject_length_grow_first_site k hk hf cst e8 cC ctl pre hcst he8 hcC hctl p _ ra guard
      hpre fp s1 s2 s3 l16 l24 l32 t40 t30 l72 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 ht40 ht30 hl72 hspl hrs _ S
      scratch hsc Heap avail rl e0 e1 hrl (by dsimp only; ecancel) hguard hsp hlc (by dsimp only; omega)
      (by dsimp only; omega) hmax hgs) ?_
    rintro st ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, t, u, scr, spl', mid, nb, C1, av', ht, hu, hscr, hspl', hnc, hmid,
      hav', Hm⟩
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, nb, ?_⟩
    apply sep_true
    ecancel

end Prysm.Checkpoint
