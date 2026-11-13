import Codec.Segment.ByteSliceListInstances
import Codec.Segment.FixedBytesAnySizeInstances
import Codec.Segment.Bytes32LoopHistoricalBatch
import Codec.Segment.SizeRejectInstances
import Prysm.Deposit.DecodeRejectSize
import Prysm.Deposit.DecodeAccept

/-! Hand list for `gen/checks/axioms_gate.py` ("must exist" names; every name also gets the axiom check). -/

#print axioms Codec.Segment.flat_len
#print axioms Codec.Segment.in_split
#print axioms Codec.Segment.backing_array_split
#print axioms Codec.Segment.backing_array_join
#print axioms Codec.Segment.input_split_sync_committee
#print axioms Codec.Segment.array_join_historical_batch
#print axioms Codec.Segment.bytesdec_seg_any_size
#print axioms Codec.Segment.bytesdec_seg_offset_zero_any_size
#print axioms Codec.Segment.bytesdec_seg_nop_any_size
#print axioms Codec.Segment.bytesdec_seg_inst
#print axioms Codec.Segment.bytesdec_seg_offset_zero_inst
#print axioms Codec.Segment.bytesdec_seg_offset_zero_size64_inst
#print axioms Codec.Segment.bytes96dec_seg_nop_inst
#print axioms Codec.Segment.bytes32dec_seg_nop_inst
#print axioms Codec.Segment.glue_nop
#print axioms Codec.Segment.glue_src
#print axioms Codec.Segment.bytes32_loop_iteration
#print axioms Codec.Segment.bytes32_loop_exit
#print axioms Codec.Segment.bytes32_loop
#print axioms Codec.Segment.historical_batch_block_roots_loop
#print axioms Codec.Segment.historical_batch_state_roots_loop
#print axioms Codec.Segment.reject_size_any_frame
#print axioms Codec.Segment.sync_committee_reject_size
#print axioms Codec.Segment.historical_batch_reject_size
#print axioms Prysm.Deposit.Decode.reject_size
#print axioms Prysm.Deposit.Decode.accept
