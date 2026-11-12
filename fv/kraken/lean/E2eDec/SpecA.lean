import E2eDec.Accept
import E2eEnc.SpecD

/-!
# Decoder accept path against EthLib (`dcd_accept_spec_stmt`)

An input that EthLib accepts against `prysmDcDesc` is `pdcEnc g` for a `g : PDc` with `g.toValue = v`
(`pdc_accepted_is_enc`); its bytes are `root ‖ dcOff ‖ u64Bytes cols` (`pdc_enc_toList`), and the machine code decodes it
into `g` (`dcd_e2e_accept_main` with `n = g.cols.length`). The text of `E2eList/IaSpecA.lean`.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eDec.Code E2eEnc
variable [Host]

namespace E2eDec

theorem dcd_in_split (a : BitVec 64) (root ib : List UInt8) (hroot : root.length = 32)
    (hl : 36 + ib.length < 2 ^ 64) :
    Eq ((root ++ dcOff ++ ib).At a) = Eq (root.At a) ⋆ Eq (dcOff.At (a + 32)) ⋆ Eq (ib.At (a + 36)) := by
  rw [List.append_assoc, at_app root _ (b := a + 32) (by rw [hroot]; rfl) (by simp [hroot, dcOff]; omega),
    at_app dcOff ib (b := a + 36) (by rw [show dcOff.length = 4 from rfl]; bv_omega) (by simp [dcOff]; omega),
    ← Std.ExtHashMap.sep_assoc]

theorem dcd_e2e_accept_spec : dcd_accept_spec_stmt := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2 S hlo R Heap avail h_mem
    hguard hlen hcap hcap63 hav hms hmsU hmm
  obtain ⟨g, rfl, hb⟩ := pdc_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz := pdc_enc_size g
  have hn := g.hcols
  have hcb : (Spec.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Spec.u64Bytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  rw [hb, hsz] at hlen hav
  rw [hb, pdc_enc_toList, dcd_in_split _ _ _ hroot (by rw [hcb]; omega)] at h_mem
  have hq : (36 + 8 * g.cols.length - 36) / 8 = g.cols.length := by omega
  rw [hq] at hav
  refine eventually_mono (dcd_e2e_accept_main k hk hf g.cols.length hn _ _ hroot hcb s ra guard fp s1 s2 s3 s4 l28 l30
    l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2
    haL2 haC2 S hlo R Heap avail (by ecancel) hguard hlen hcap hcap63 hav hms hmsU hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, -, -, -, pb, A, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  refine ⟨hpc, hrax, hrbx, pb, A, ?_⟩
  rw [hb, pdc_enc_toList, dcd_in_split _ _ _ hroot (by rw [hcb]; omega)]
  exact sep_true (by ecancel)

end E2eDec
