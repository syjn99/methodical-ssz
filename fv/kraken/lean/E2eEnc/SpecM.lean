import E2eEnc.Fast
import E2eEnc.Spec
import Runtime.CopyModel

/-!
# Encoder fast path against EthLib (`dc_marshal_spec_stmt`)

The shape of `E2e.cp_e2e_marshal_spec_k`: for a receiver holding the Go layout of `g : PDc`, the fast path writes
`pre ‖ serialize prysmDcDesc g.toValue` at `dst.ptr`. The full frame accounting is `dc_e2e_marshal_fast_main`.
-/

open Machine Runtime TestTarget E2eEnc.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2eEnc

theorem dc_e2e_marshal_spec : dc_marshal_spec_stmt := by
  intro k hk hf s ra guard pr pc nb g hnb pre d hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot hfp h1 h2 hl24 hl32 hl40
    hl56 hl64 hrs S scratch hsc R h_mem hguard hcap hmm
  refine ⟨pdcEnc g, pdc_serialize g, ?_⟩
  have hroot : g.root.toList.length = 32 := by simp
  have hcb : (Spec.u64Bytes g.cols).toList.length = 8 * g.cols.length := by simp [Spec.u64Bytes_size]
  refine eventually_mono (dc_e2e_marshal_fast_main k hk hf s ra guard pr pc nb g.cols.length hnb g.hcols _ _ pre d
    hroot hcb hpre hd fp s1 s2 l24 l32 l40 l56 l64 rslot hfp h1 h2 hl24 hl32 hl40 hl56 hl64 hrs S scratch hsc R
    h_mem hguard hcap hmm) ?_
  rintro st ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, -, -, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  refine ⟨hpc, hrax, by rw [hrbx, pdc_enc_size]; omega, hrcx, hrdi, hrsi, ?_⟩
  rw [pdc_enc_toList]
  simp only [List.append_assoc] at hm ⊢
  exact sep_true (by ecancel)

end E2eEnc
