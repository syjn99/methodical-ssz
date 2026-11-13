import Prysm.HistoricalBatch.DecodeRejectSize
import Prysm.HistoricalBatch.DecodeAccept
import Prysm.HistoricalBatch.DecodeSpec
import Prysm.HistoricalBatch.SpecEquivalence
import Prysm.HistoricalBatch.WitnessDecodeAccept

/-! Hand list for `gen/e2e/hbaxioms_gate.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms Prysm.HistoricalBatch.Decode.reject_size
#print axioms Prysm.HistoricalBatch.Decode.block_roots_iter
#print axioms Prysm.HistoricalBatch.Decode.block_roots_exit
#print axioms Prysm.HistoricalBatch.Decode.block_roots_loop
#print axioms Prysm.HistoricalBatch.Decode.state_roots_iter
#print axioms Prysm.HistoricalBatch.Decode.state_roots_exit
#print axioms Prysm.HistoricalBatch.Decode.state_roots_loop
#print axioms Prysm.HistoricalBatch.Decode.accept
#print axioms Prysm.HistoricalBatch.Decode.accept_spec
#print axioms Prysm.HistoricalBatch.Decode.reject_size_spec
#print axioms Prysm.HistoricalBatch.Decode.reject_complete
#print axioms Prysm.HistoricalBatch.spec_accepts_iff
#print axioms Prysm.HistoricalBatch.desc_deserialize_checker
#print axioms Prysm.HistoricalBatch.Witness.DecodeAccept.runs
