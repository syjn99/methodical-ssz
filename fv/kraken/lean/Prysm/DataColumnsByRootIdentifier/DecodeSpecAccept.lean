import Prysm.DataColumnsByRootIdentifier.DecodeAccept
import Prysm.DataColumnsByRootIdentifier.SpecDecodeBridge

/-!
# Decoder accept path against EthLib (`Decode.accept_spec_statement`)

An input that EthLib accepts against `desc` is `SszValue.encode g` for a `g : SszValue` with `g.toValue = v`
(`accepted_is_encode`); its bytes are `root ‖ offsetBytes ‖ u64Bytes cols` (`encode_toList`), and the machine code decodes it
into `g` (`Decode.accept` with `n = g.cols.length`). The text of `Prysm/IndexedAttestation/DecodeSpecAccept.lean`.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz Prysm.DataColumnsByRootIdentifier.Code
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Decode.input_split (a : BitVec 64) (root ib : List UInt8) (hroot : root.length = 32)
    (hl : 36 + ib.length < 2 ^ 64) :
    Eq ((root ++ offsetBytes ++ ib).At a) = Eq (root.At a) ⋆ Eq (offsetBytes.At (a + 32)) ⋆ Eq (ib.At (a + 36)) := by
  rw [List.append_assoc, at_app root _ (b := a + 32) (by rw [hroot]; rfl) (by simp [hroot, offsetBytes]; omega),
    at_app offsetBytes ib (b := a + 36) (by rw [show offsetBytes.length = 4 from rfl]; bv_omega) (by simp [offsetBytes]; omega),
    ← Std.ExtHashMap.sep_assoc]

theorem Decode.accept_spec : Decode.accept_spec_statement := by
  intro k hk hf bsA v hd s ra guard fp s1 s2 s3 s4 l28 l30 l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2
    hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2 haL2 haC2 S hlo R Heap avail h_mem
    hguard hlen hcap hcap63 hav hms hmsU hmm
  obtain ⟨g, rfl, hb⟩ := accepted_is_encode hd
  refine ⟨g, rfl, hb, ?_⟩
  have hsz := encode_size g
  have hn := g.hcols
  have hcb : (Spec.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Spec.u64Bytes_size]
  have hroot : g.root.toList.length = 32 := by simp
  rw [hb, hsz] at hlen hav
  rw [hb, encode_toList, Decode.input_split _ _ _ hroot (by rw [hcb]; omega)] at h_mem
  have hq : (36 + 8 * g.cols.length - 36) / 8 = g.cols.length := by omega
  rw [hq] at hav
  refine eventually_mono (Decode.accept k hk hf g.cols.length hn _ _ hroot hcb s ra guard fp s1 s2 s3 s4 l28 l30
    l38 l40 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 hfp h1 h2 h3 h4 hl28 hl30 hl38 hl40 hspl hrs haP1 haL1 haC1 haP2
    haL2 haC2 S hlo R Heap avail (by ecancel) hguard hlen hcap hcap63 hav hms hmsU hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, -, -, -, pb, A, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  refine ⟨hpc, hrax, hrbx, pb, A, ?_⟩
  rw [hb, encode_toList, Decode.input_split _ _ _ hroot (by rw [hcb]; omega)]
  exact sep_true (by ecancel)

end Prysm.DataColumnsByRootIdentifier
