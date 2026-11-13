import Prysm.DataColumnsByRootIdentifier.EncodeFastPath
import Prysm.DataColumnsByRootIdentifier.Spec
import Runtime.CopyModel

/-!
# Encoder fast path against EthLib (`Encode.fast_path_spec_statement`)

The shape of `Prysm.Checkpoint.Encode.fast_path_spec`: for a receiver holding the Go layout of `g : SszValue`, the fast path writes
`pre ‖ serialize desc g.toValue` at `dst.ptr`. The full frame accounting is `Encode.fast_path`.
-/

open Machine Runtime TestTarget Prysm.DataColumnsByRootIdentifier.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.DataColumnsByRootIdentifier

theorem Encode.fast_path_spec : Encode.fast_path_spec_statement := by
  intro k hk hf s ra guard pr pc nb g hnb pre d hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot hfp h1 h2 hl24 hl32 hl40
    hl56 hl64 hrs S scratch hsc R h_mem hguard hcap hmm
  refine ⟨SszValue.encode g, toValue_serialize g, ?_⟩
  have hroot : g.root.toList.length = 32 := by simp
  have hcb : (Spec.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Spec.u64Bytes_size]
  refine eventually_mono (Encode.fast_path k hk hf s ra guard pr pc nb g.cols.length hnb g.hcols _ _ pre d
    hroot hcb hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot hfp h1 h2 hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc R
    h_mem hguard hcap hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, -, -, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  refine ⟨hpc, hrax, by rw [hrbx, encode_size]; omega, hrcx, hrdi, hrsi, ?_⟩
  rw [encode_toList]
  simp only [List.append_assoc] at hm ⊢
  exact sep_true (by ecancel)

end Prysm.DataColumnsByRootIdentifier
