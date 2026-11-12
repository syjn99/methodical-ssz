import E2eList.IaRejectCall
import E2eList.IaSpec

/-!
# Spec alignment of the IndexedAttestation alignment reject and overflow reject

Statements: the corrected `ia_reject_misaligned_spec_nz_stmt` and `ia_reject_toobig_spec_nz_stmt` (`StmtIaNz.lean`):
EthLib rejects (`pia_spec_rejects`: the Go check that fails is one of `iaChecks`) and the machine code returns the
`fmt.errorf` error (`ia_e2e_reject_misaligned_nz`, `ia_e2e_reject_toobig_nz`). The text of `IaSpecR.lean`.
-/

open Fk E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

theorem ia_e2e_reject_misaligned_spec_nz : ia_reject_misaligned_spec_nz_stmt := by
  intro k hk hf bs hbs hoff hmis s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl
    hrs S hlo Heap avail R h_mem hguard hlen hav hcv hfe
  exact ⟨pia_spec_rejects bs (fun h => hmis h.2.2.1),
    ia_e2e_reject_misaligned_nz k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw
      hspl hrs S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hmis) hav hcv hfe⟩

theorem ia_e2e_reject_toobig_spec_nz : ia_reject_toobig_spec_nz_stmt := by
  intro k hk hf bs hbs hoff hal hbig s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw hspl
    hrs S hlo Heap avail R h_mem hguard hlen hav hcv hfe
  exact ⟨pia_spec_rejects bs (fun h => by have := h.2.2.2; omega),
    ia_e2e_reject_toobig_nz k hk hf s ra guard e0 e1 esp msg ity he0 he0nz hity fp s2 aw spl rslot lo hfp h2 haw
      hspl hrs S hlo Heap avail R h_mem hguard (by omega) (by rw [hlen]; exact hal) (by rw [hlen]; exact hbig) hav hcv
      hfe⟩

end E2eList
