import Prysm.AttestationData.EncodeHeadRoot

/-!
# `(*v1alpha1.AttestationData).MarshalSSZTo`, fast path, segments 1 to 3 together

`Encode.head` composes `Encode.head_slot` (directives 0–33), `Encode.head_index` (33–59) and `Encode.head_root`
(59 to the return of `runtime.memmove` at directive 90).
After it, `dst[len:len+48]` holds the Slot bytes, the CommitteeIndex bytes and the 32 root bytes.
-/

open Machine Runtime Prysm.AttestationData.Code
variable [Host]

namespace Prysm.AttestationData

/-- Segments 1 to 3 of the encoder fast path: from the entry to directive 90. -/
theorem Encode.head (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (s : MachineData) (ra guard : UInt64) (rp : BitVec 64) (sl ix root d0 d1 d2 : List UInt8)
    (hsl : sl.length = 8) (hix : ix.length = 8) (hroot : root.length = 32)
    (hd0 : d0.length = 8) (hd1 : d1.length = 8) (hd2 : d2.length = 32)
    (fp a8 b16 ta tb tc td q48 q120 q128 rslot : List UInt8)
    (hfp : fp.length = 8) (ha8 : a8.length = 8) (hb16 : b16.length = 8) (hta : ta.length = 16) (htb : tb.length = 16)
    (htc : tc.length = 16) (htd : td.length = 16) (h48 : q48.length = 8) (h120 : q120.length = 8)
    (h128 : q128.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (a8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (b16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (ta.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (tb.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (tc.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (td.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (q48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (q120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (q128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At rp)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 56 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 48 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hmm : MemmoveContract S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 90)
        ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - 184 }
        ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (t1 u1 t2 u2 scr : List UInt8), t1.length = 8 ∧ u1.length = 16 ∧ t2.length = 8 ∧ u2.length = 16
          ∧ scr.length = S ∧
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 90)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 192))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (root.At rp)
          ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq (ix.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
          ⋆ Eq (root.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  refine eventually_trans _ _ _ _ (Encode.head_slot k hk hf s ra guard sl fp a8 b16 ta tb hsl hfp ha8 hb16 hta htb
    (Eq (tc.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (td.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (q48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (q120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (q128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
      ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At rp)
      ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (cast (congrFun (by ac_rfl) _) h_mem) hguard (by omega) hcap63) ?_
  rintro ⟨st1, pc1⟩ ⟨hpc1, hrax1, hrbx1, hrcx1, hrdx1, hrdi1, hrsp1, hrbp1, hr141, t1, u1, ht1, hu1, Hm1⟩
  dsimp only at hpc1 hrax1 hrbx1 hrcx1 hrdx1 hrdi1 hrsp1 hrbp1 hr141 Hm1
  subst hpc1
  refine eventually_trans _ _ _ _ (Encode.head_index k hk hf s.regs.rsp.toBitVec st1 sl ix d0 tc td hsl hix hd0 htc htd
    hrsp1 (by apply UInt64.toBitVec_inj.mp; rw [hrdx1, hrcx1])
    (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (q48.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (q120.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (q128.At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 192)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 192 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 rp.toInt).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (root.At rp)
      ⋆ Eq (d1.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq (d2.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16)) ⋆ R)
    (by
      rw [hrax1, hrbx1, hrcx1]
      exact cast (congrFun (by ac_rfl) _) Hm1)
    (by rw [hrcx1, hrdi1]; omega) (by rw [hrdi1]; exact hcap63)) ?_
  rintro ⟨st2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrdx2, hr82, hrdi2, hrsp2, hrbp2, hr142, t2, u2, ht2, hu2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrdx2 hr82 hrdi2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  rw [hrcx1] at hr82 Hm2
  rw [hrax1] at hrax2
  rw [hrbx1] at hrbx2
  rw [hrdi1] at hrdi2
  rw [hrsp1] at hrsp2
  rw [hrbp1] at hrbp2
  rw [hr141] at hr142
  refine eventually_mono (Encode.head_root k hk hf s.regs.rsp.toBitVec s.regs.rcx.toBitVec st2 rp ix root d1 d2
    q48 q120 q128 rslot hix hroot hd1 hd2 h48 h120 h128 hrs S scratch hsc hrsp2
    (by rw [hrdx2]; apply UInt64.toBitVec_inj.mp; rw [hrdx1])
    (by apply UInt64.toBitVec_inj.mp; rw [hr82])
    (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rsp.toBitVec - 80)) ⋆ Eq (t1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (u1.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (t2.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (u2.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (ix.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (sl.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (by
      rw [hrax2, hrbx2]
      simp only [hrax1, hrbx1] at Hm2
      exact cast (congrFun (by ac_rfl) _) Hm2)
    (by rw [hrdi2, UInt64.toNat_toBitVec]; omega) (by rw [hrdi2]; exact hcap63) hmm) ?_
  rintro st3 ⟨hpc3, hrsp3, hrbp3, hr143, scr, hscr, Hm3⟩
  refine ⟨hpc3, by rw [hrsp3, hrsp2], by rw [hrbp3, hrbp2], by rw [hr143, hr142], t1, u1, t2, u2, scr,
    ht1, hu1, ht2, hu2, hscr, ?_⟩
  rw [hrax2, hrbx2, hrdi2] at Hm3
  exact cast (congrFun (by ac_rfl) _) Hm3

end Prysm.AttestationData
