import Prysm.AttestationData.GeneratedEncodeFastPath
import Prysm.AttestationData.EncodeSpec

/-!
# AttestationData encoder fast path (generated theorem) against the independent Desc

`Encode.generated_fast_spec` has the statement of the hand theorem `Encode.fast_path_spec`.
It takes a receiver whose fields hold the SSZ content `g : SszValue`.
Then the generated theorem `Encode.generated_fast` writes at `dst[len:len+128]` exactly the bytes of `serialize desc g.toValue`.
`desc` is the independent consensus-specs Desc of `Prysm.AttestationData.Spec`.
The statement keeps the exact frame, and it has no `True` part.
The proof applies `Encode.generated_fast`, not the hand theorem.
A person writes this file, because `gen/flat-types/flat_types_encode_spec.py` has no form for a nested field.
-/

open Machine Runtime Codec Prysm.AttestationData.Code EthLib.Serialization.Ssz

namespace Prysm.AttestationData
variable [Host]

/-- **The generated encoder fast path writes `serialize desc g.toValue`** (the statement of `Encode.fast_path_spec`). -/
theorem Encode.generated_fast_spec (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (kC : Nat) (hkC : Prysm.Checkpoint.Code.marshalSSZTo.IsInfixAt Host.prog kC)
    (hfC : LabelsFresh Prysm.Checkpoint.Code.marshalSSZTo kC)
    (S : Nat) (hS : S < 2 ^ 60) (hmm : MemmoveContract S)
    (s : MachineData) (ra guard : UInt64) (rp ps pt p1 p2 : BitVec 64) (hps : ps ≠ 0) (hpt : pt ≠ 0)
    (g : SszValue) (sl ix root cs e1 cC1 ctl1 root1 ct e2 cC2 ctl2 root2 pre d0 d1 d2 d3 d4 d5 d6 : List UInt8)
    (hsl : sl = (uintBytes 8 g.slot.toNat).toList) (hix : ix = (uintBytes 8 g.index.toNat).toList)
    (hroot : root = g.root.toList)
    (he1 : e1 = (uintBytes 8 g.source.epoch.toNat).toList) (hroot1 : root1 = g.source.root.toList)
    (he2 : e2 = (uintBytes 8 g.target.epoch.toNat).toList) (hroot2 : root2 = g.target.root.toList)
    (hcs : cs.length = 8) (hcC1 : cC1.length = 8) (hctl1 : ctl1.length = 32)
    (hct : ct.length = 8) (hcC2 : cC2.length = 8) (hctl2 : ctl2.length = 32)
    (hpre : pre.length = s.regs.rcx.toNat) (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (hd3 : d3.length = 8) (hd4 : d4.length = 32) (hd5 : d5.length = 8) (hd6 : d6.length = 32)
    (fp a8 b16 ta tb tc td q48 q120 q128 q176 rslot lo : List UInt8)
    (hfp : fp.length = 8) (ha8 : a8.length = 8) (hb16 : b16.length = 8) (hta : ta.length = 16) (htb : tb.length = 16)
    (htc : tc.length = 16) (htd : td.length = 16) (h48 : q48.length = 8) (h120 : q120.length = 8)
    (h128 : q128.length = 8) (h176 : q176.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = S + 120)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (a8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (b16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (ta.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (tb.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (tc.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (td.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (q48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (q120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (q128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (q176.At (s.regs.rsp.toBitVec - 176))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (root.At rp)
      ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
      ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq (d3.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq (d4.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq (d5.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq (d6.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ R)
    (hguard : guard.toNat + 312 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 128 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    ∃ bs, serialize desc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 128 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 t u scr rs' gap : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8
          ∧ u2.length = 16 ∧ t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧ gap.length = 48 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (ix.At (s.regs.rsp.toBitVec - 112)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48).toInt).At (s.regs.rsp.toBitVec - 120))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 128))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 176))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 178)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt).At (s.regs.rsp.toBitVec - 200))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec - 208))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec - 216))
          ⋆ Eq ((Int.toBytes 8 (s.regs.rcx.toBitVec + 48 + 40 + 40).toInt).At (s.regs.rsp.toBitVec - 224))
          ⋆ Eq (u.At (s.regs.rsp.toBitVec - 240)) ⋆ Eq (e2.At (s.regs.rsp.toBitVec - 256))
          ⋆ Eq (t.At (s.regs.rsp.toBitVec - 248)) ⋆ Eq (gap.At (s.regs.rsp.toBitVec - 304))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 312)) ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 312 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 ps.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 pt.toInt).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (root.At rp)
          ⋆ Eq (cs.At ps) ⋆ Eq (e1.At (ps + 8)) ⋆ Eq ((Int.toBytes 8 p1.toInt).At (ps + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (ps + 24)) ⋆ Eq (cC1.At (ps + 32)) ⋆ Eq (ctl1.At (ps + 40)) ⋆ Eq (root1.At p1)
          ⋆ Eq (ct.At pt) ⋆ Eq (e2.At (pt + 8)) ⋆ Eq ((Int.toBytes 8 p2.toInt).At (pt + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (pt + 24)) ⋆ Eq (cC2.At (pt + 32)) ⋆ Eq (ctl2.At (pt + 40)) ⋆ Eq (root2.At p2)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have h8 : ∀ x : UInt64, (uintBytes 8 x.toNat).toList.length = 8 := fun x => by simp [Spec.uintBytes_size]
  have lsl : sl.length = 8 := by rw [hsl]; exact h8 _
  have lix : ix.length = 8 := by rw [hix]; exact h8 _
  have lroot : root.length = 32 := by rw [hroot]; simp
  have le1 : e1.length = 8 := by rw [he1]; exact h8 _
  have lroot1 : root1.length = 32 := by rw [hroot1]; simp
  have le2 : e2.length = 8 := by rw [he2]; exact h8 _
  have lroot2 : root2.length = 32 := by rw [hroot2]; simp
  refine ⟨SszValue.encode g, SszValue.serialize_eq g, ?_⟩
  rw [SszValue.encode_toList, ← hsl, ← hix, ← hroot, ← he1, ← hroot1, ← he2, ← hroot2]
  refine eventually_mono (Encode.generated_fast k hk hf kC hkC hfC sl ix root e1 root1 e2 root2 cs cC1 ctl1 ct cC2 ctl2
    pre d0 d1 d2 d3 d4 d5 d6 lsl lix lroot le1 lroot1 le2 lroot2 hcs hcC1 hctl1 hct hcC2 hctl2 hd0 hd1 hd2 hd3 hd4 hd5 hd6
    rp ps p1 pt p2 hps hpt s ra guard hpre fp a8 b16 ta tb tc td q48 q120 q128 q176 rslot hfp ha8 hb16 hta htb htc htd
    h48 h120 h128 h176 hrs R S hS lo hlo (by ecancel) hguard hcap hcap63 hmm) ?_
  rintro st ⟨h1, h2, h3, h4, h5, h6, h7, h8', h9, x0, x1, x2, x3, x4, x5, x6, x7, x8,
    hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hm⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8', h9, x0, x1, x2, x3, x6, x5, x8, x7, x4,
    hx0, hx1, hx2, hx3, hx6, hx5, hx8, hx7, hx4, ?_⟩
  rw [Encode.merge_encoding sl ix root e1 root1 e2 root2 _ lsl lix lroot le1 lroot1 le2 lroot2,
    show s.regs.rcx.toBitVec + 48 + 40 + 40 = s.regs.rcx.toBitVec + 128 by bv_omega]
  ecancel

end Prysm.AttestationData
