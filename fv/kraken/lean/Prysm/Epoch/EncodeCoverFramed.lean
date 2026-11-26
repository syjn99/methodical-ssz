module

public import Prysm.Epoch.EncodeGrowFirstSite
public import Prysm.Epoch.EncodeSpec

@[expose] public section

/-!
# `(*primitives.Epoch).MarshalSSZTo`: case cover over every capacity, with the exact frame

`Encode.cover_framed` holds for every `len ≤ cap` within the heap budget `4 * len + 8608 ≤ avail`.
The caller's backing array is `pre ++ spare`, with `len(pre) = len` and `len + len(spare) = cap`.
The code takes one of two proved paths, by its only capacity test:

| disjunct | range | member | caller's array after |
| (1) | `len + 8 ≤ cap` | `Encode.fast_path` | `pre ++ serialize ++ spare[8:]` (written in place, returned) |
| (2) | `cap < len + 8` | `Encode.grow_first_site` | unchanged `pre ++ spare`; new block returned |

Each disjunct is the exact postcondition of its member theorem.
Every caller-visible byte is named.
These are the stack slots, the receiver, the caller's array, the new block, the guard word, `Heap` and `R`.
In both disjuncts the returned block starts with `pre ++ bs`.
Here `serialize desc (.uint x) = .ok bs` (EthLib).
Heap budget: `4·len + 8608 ≤ avail`.
This bound covers the growslice call, because `nextSliceCap (len + 8) cap ≤ 2·(len + 8) + 192`.
-/

open Machine Runtime Prysm.Epoch.Code EthLib.Serialization.Ssz

namespace Prysm.Epoch

theorem Encode.cover_framed_out (b : BitVec 64) (L : UInt64) (pre e8 : List UInt8) (hpre : pre.length = L.toNat)
    (he8 : e8.length = 8) (hb : L.toNat + 8 < 2 ^ 64) :
    Eq ((pre ++ e8).At b) = Eq (pre.At b) ⋆ Eq (e8.At (b + L.toBitVec)) :=
  at_app pre e8 (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp) (by simp only [hpre, he8]; omega)

theorem Encode.cover_framed_pre (b : BitVec 64) (L : UInt64) (pre spare : List UInt8) (hpre : pre.length = L.toNat)
    (hb : pre.length + spare.length < 2 ^ 64) :
    Eq ((pre ++ spare).At b) = Eq (pre.At b) ⋆ Eq (spare.At (b + L.toBitVec)) :=
  at_app pre spare (by rw [hpre]; apply BitVec.eq_of_toNat_eq; simp) (by omega)

variable [Host]

theorem Encode.cover_framed (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (x : UInt64) (e8 : List UInt8) (he8x : e8 = (uintBytes 8 x.toNat).toList) (pre spare : List UInt8)
    (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)
    (hspare : pre.length + spare.length = s.regs.rdi.toNat)
    (fp s2 s3 t28 t18 rslot spl : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (h3 : s3.length = 8)
    (ht28 : t28.length = 16) (ht18 : t18.length = 16) (hrs : rslot.length = 8) (hspl : spl.length = 40)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (t28.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t18.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec)
      ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat)
    (hbud : 4 * s.regs.rcx.toNat + 8608 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) :
    ∃ bs : Array UInt8, serialize desc (.uint x.toNat) = .ok bs ∧ bs.toList = e8 ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 8
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        -- (1) len + 8 ≤ cap: written into the caller's array and returned (Encode.fast_path)
        ((s.regs.rcx.toNat + 8 ≤ s.regs.rdi.toNat ∧ st.data.regs.rax = s.regs.rbx ∧ st.data.regs.rcx = s.regs.rdi ∧
          ∃ (t u : List UInt8), t.length = 8 ∧ u.length = 16 ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
            ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (e8.At s.regs.rax.toBitVec)
            ⋆ Eq ((pre ++ bs.toList).At s.regs.rbx.toBitVec)
            ⋆ Eq ((spare.drop 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
            ⋆ Heap avail ⋆ R) st.data.dmem)
        -- (2) cap < len + 8: one growth, the caller's array unchanged (Encode.grow_first_site)
        ∨ (s.regs.rdi.toNat < s.regs.rcx.toNat + 8
          ∧ nextSliceCap (s.regs.rcx.toNat + 8) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat ∧
          ∃ (t u scr spl' rest : List UInt8) (av' : Nat), t.length = 8 ∧ u.length = 16 ∧ scr.length = S
            ∧ spl'.length = 40 ∧ s.regs.rcx.toNat + 8 + rest.length = st.data.regs.rcx.toNat
            ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
          (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
            ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
            ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
            ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
            ⋆ Eq (e8.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (t.At (s.regs.rsp.toBitVec - 32))
            ⋆ Eq (u.At (s.regs.rsp.toBitVec - 24))
            ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 80))
            ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 25)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
            ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
            ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
            ⋆ Eq (e8.At s.regs.rax.toBitVec)
            ⋆ Eq ((pre ++ spare).At s.regs.rbx.toBitVec)
            ⋆ Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec)
            ⋆ Eq (rest.At (st.data.regs.rax.toBitVec + s.regs.rcx.toBitVec + 8))
            ⋆ Heap av' ⋆ R) st.data.dmem)))
      ⟨s, Host.addrOf k⟩ := by
  refine ⟨uintBytes 8 x.toNat, uint64_serialize_eq x, he8x.symm, ?_⟩
  rw [← he8x]
  have he8 : e8.length = 8 := by rw [he8x]; simp [Spec.uintBytes_size]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hbud hpre hspare ⊢
  have := rcx.toNat_lt_size; have := rdi.toNat_lt_size; simp only [UInt64.size] at *
  have hL : rcx.toNat + 8 < 2 ^ 64 := by unfold maxAlloc at hmax; omega
  by_cases c1 : rcx.toNat + 8 ≤ rdi.toNat
  · -- fast path
    have htl : 8 ≤ spare.length := by omega
    rw [Encode.grow_first_site_split rbx.toBitVec rcx.toBitVec pre spare hpre htl (by omega)] at h_mem
    refine eventually_mono (Encode.fast_path k hk hf e8 pre (spare.take 8) he8 (by simp only [List.length_take]; omega)
      _ ra guard hpre fp s2 t28 t18 hfp h2 ht28 ht18 _ (by dsimp only; ecancel) hguard c1) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', e9, t, u, ht, hu, Hm⟩
    refine ⟨e1, e3, e5, e6, e7, e8', e9, Or.inl ⟨c1, e2, e4, t, u, ht, hu, ?_⟩⟩
    rw [Encode.cover_framed_out rbx.toBitVec rcx pre _ hpre he8 hL]
    ecancel
  · -- the append grows
    have hlc : rcx.toNat ≤ rdi.toNat := by omega
    rw [Encode.cover_framed_pre rbx.toBitVec rcx pre spare hpre (by omega)] at h_mem
    have hn := nextSliceCap_le (rcx.toNat + 8) rdi.toNat (by omega)
    refine eventually_mono (Encode.grow_first_site k hk e8 pre he8 _ ra guard hpre fp s2 s3 t28 t18 rslot spl
      hfp h2 h3 ht28 ht18 hrs hspl _ S scratch hsc Heap avail (by dsimp only; ecancel) hguard hlc
      (by dsimp only; omega) (by dsimp only; omega) hmax hgs) ?_
    rintro st ⟨e1, e2, e3, e4, e5, e6, e7, e8', t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest, hav', Hm⟩
    refine ⟨e1, e2, e4, e5, e6, e7, e8', Or.inr ⟨by omega, e3, t, u, scr, spl', rest, av', ht, hu, hscr, hspl', hrest,
      hav', ?_⟩⟩
    rw [Encode.cover_framed_out _ rcx pre _ hpre he8 hL, Encode.cover_framed_pre rbx.toBitVec rcx pre spare hpre (by omega)]
    ecancel

end Prysm.Epoch
