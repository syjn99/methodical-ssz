import Prysm.DataColumnsByRootIdentifier.EncodeGrowFirstSite
import Prysm.DataColumnsByRootIdentifier.Spec
import Runtime.CopyModel

/-!
# Grow path at site 1 against EthLib (`Encode.grow_first_site_spec_statement`)

From `Encode.grow_first_site`: the new block starts with `pre ‖ serialize desc g.toValue`.
-/

open Machine Runtime Prysm.DataColumnsByRootIdentifier.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Encode.grow_first_site_spec : Encode.grow_first_site_spec_statement := by
  intro k hk hf s ra guard pr pc nb g hnb pre hpre fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot hfp h1 h2 h3 hl16
    hl24 hl32 hl40 hl56 hl64 hspl hrs S scratch hsc Heap avail R h_mem hguard hlc hgrow hfit hbud hmax hgs hmm
  refine ⟨SszValue.encode g, toValue_serialize g, ?_⟩
  have hroot : g.root.toList.length = 32 := by simp
  have hcb : (Spec.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Spec.u64Bytes_size]
  refine eventually_mono (Encode.grow_first_site k hk hf s ra guard pr pc nb g.cols.length hnb g.hcols _ _ pre
    hroot hcb hpre fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot hfp h1 h2 h3 hl16 hl24 hl32 hl40 hl56 hl64 hspl hrs
    S scratch hsc Heap avail R h_mem hguard hlc hgrow hfit hbud hmax hgs hmm) ?_
  rintro st ⟨hpc, hrbx, hnc, hrdi, hrsi, -, -, -, _, _, _, _, _, _, _, _, _, rest, _, _, _, _, _, _, _, _, _, _,
    hrest, _, hm⟩
  refine ⟨hpc, by rw [hrbx, encode_size]; omega, by rw [encode_size]; omega, hrdi, hrsi, ?_⟩
  rw [encode_toList, show pre ++ (g.root.toList ++ offsetBytes ++ (Spec.u64Bytes g.cols).toList)
    = pre ++ g.root.toList ++ offsetBytes ++ (Spec.u64Bytes g.cols).toList by simp]
  have hl : (pre ++ g.root.toList ++ offsetBytes ++ (Spec.u64Bytes g.cols).toList).length + rest.length ≤ 2 ^ 64 := by
    have := st.data.regs.rcx.toNat_lt_size; simp only [UInt64.size] at this
    simp [hpre, offsetBytes, Spec.u64Bytes_size] at hrest ⊢; omega
  rw [Mem.At_append_sep _ rest _ hl] at hm
  exact sep_true (by ecancel)

end Prysm.DataColumnsByRootIdentifier
