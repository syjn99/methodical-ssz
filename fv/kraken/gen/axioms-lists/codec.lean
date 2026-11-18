import Codec.SegmentTemplate
import Codec.Uint64Decoder
import Codec.Kind.FieldPatterns
import Codec.StackGuard
import Codec.EncodeMemmove
import Codec.EncodeRejectTail
import Codec.InlineUint64
import Codec.FixedBytesDecode
import Codec.DecoderHeadEpilogue
import Codec.CalleeDecode
import Codec.InlineUint64RegisterBase
import Codec.Kind.FixedBytesDecodeWindow
import Codec.Kind.FixedBytesDecodeWindowOffsetZero
import Codec.FixedBytesDecodeWindow
import Codec.FixedBytesDecodeWindowOffsetZero
import Codec.FixedBytesDecodeInline
import Codec.Kind.FixedBytesDecodeInline
import Codec.EncodeInlineCopy
import Codec.Kind.CalleeDecodeWindow
import Codec.CalleeDecodeWindow
import Codec.DecoderPrologue
import Codec.NopWindow
import Codec.WindowSteps
import Codec.Kind.WindowSteps
import Codec.Kind.DecodeAcceptAnyFrame
import Codec.DecodeRejectSizeAnyFrame
import Codec.Kind.DecodeRejectAnyFrame
import Codec.FieldFrame
import Codec.Kind.EncodeFastPathAnyFrame
import Codec.EncodeSteps
import Codec.EncodeFrameTest
import Codec.EncodeFieldHelpers
import Codec.Segment.ByteSliceList
import Codec.Segment.Bytes32Loop
import Codec.Segment.Bytes32LoopProof
import Codec.Segment.SizeReject
import Codec.Segment.Bytes32VectorSpec

/-! Hand list of the declarations of the library `Codec` for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Codec.infix_sub
#print axioms Codec.uint64_decode_accept
#print axioms Codec.uint64DecodeAcceptKind_of
#print axioms Codec.lea_cmp_be_false
#print axioms Codec.encode32_memmove_call
#print axioms Codec.encode_reject_tail
#print axioms Codec.Uint64InlineReg
#print axioms Codec.bytesDecodeHead
#print axioms Codec.bytesDecodeMiddle
#print axioms Codec.bytesDecodeMiddleOffsetZero
#print axioms Codec.bytesDecodeTailReloadJump
#print axioms Codec.bytesDecodeTailPointerStore
#print axioms Codec.bytes_decode_segment
#print axioms Codec.bytes_decode_segment_offset_zero
#print axioms Codec.bytes_decode_tail_segment
#print axioms Codec.decodeEpilogue
#print axioms Codec.decodeHead
#print axioms Codec.decode_epilogue_segment
#print axioms Codec.decode_head_segment
#print axioms Codec.uint64DecodeInline
#print axioms Codec.uint64_decode_inline_segment
#print axioms Codec.call_argument_first_segment
#print axioms Codec.call_argument_lea_segment
#print axioms Codec.call_argument_mov_segment
#print axioms Codec.call_decode_segment
#print axioms Codec.uint64_decode_scratch_register_segment
#print axioms Codec.bytesDecodeSegmentKindWindow_of
#print axioms Codec.bytesDecodeSegmentOffsetZeroKindWindow_of
#print axioms Codec.bytes_decode_window_32_rdx_rax
#print axioms Codec.bytes_decode_window_32_rdx_rcx
#print axioms Codec.bytes_decode_window_32_rdx_rdi
#print axioms Codec.bytes_decode_window_32_rdx_rdx
#print axioms Codec.bytes_decode_window_32_rdx_rsi
#print axioms Codec.bytes_decode_window_32_rsi_rax
#print axioms Codec.bytes_decode_window_32_rsi_rcx
#print axioms Codec.bytes_decode_window_32_rsi_rdi
#print axioms Codec.bytes_decode_window_32_rsi_rdx
#print axioms Codec.bytes_decode_window_32_rsi_rsi
#print axioms Codec.bytes_decode_window_48_rdx_rax
#print axioms Codec.bytes_decode_window_48_rdx_rcx
#print axioms Codec.bytes_decode_window_48_rdx_rdi
#print axioms Codec.bytes_decode_window_48_rdx_rdx
#print axioms Codec.bytes_decode_window_48_rdx_rsi
#print axioms Codec.bytes_decode_window_48_rsi_rax
#print axioms Codec.bytes_decode_window_48_rsi_rcx
#print axioms Codec.bytes_decode_window_48_rsi_rdi
#print axioms Codec.bytes_decode_window_48_rsi_rdx
#print axioms Codec.bytes_decode_window_48_rsi_rsi
#print axioms Codec.bytes_decode_window_96_rdx_rax
#print axioms Codec.bytes_decode_window_96_rdx_rcx
#print axioms Codec.bytes_decode_window_96_rdx_rdi
#print axioms Codec.bytes_decode_window_96_rdx_rdx
#print axioms Codec.bytes_decode_window_96_rdx_rsi
#print axioms Codec.bytes_decode_window_96_rsi_rax
#print axioms Codec.bytes_decode_window_96_rsi_rcx
#print axioms Codec.bytes_decode_window_96_rsi_rdi
#print axioms Codec.bytes_decode_window_96_rsi_rdx
#print axioms Codec.bytes_decode_window_96_rsi_rsi
#print axioms Codec.bytes_decode_window_20_rdx_rax
#print axioms Codec.bytes_decode_window_20_rdx_rcx
#print axioms Codec.bytes_decode_window_20_rdx_rdi
#print axioms Codec.bytes_decode_window_20_rdx_rdx
#print axioms Codec.bytes_decode_window_20_rdx_rsi
#print axioms Codec.bytes_decode_window_20_rsi_rax
#print axioms Codec.bytes_decode_window_20_rsi_rcx
#print axioms Codec.bytes_decode_window_20_rsi_rdi
#print axioms Codec.bytes_decode_window_20_rsi_rdx
#print axioms Codec.bytes_decode_window_20_rsi_rsi
#print axioms Codec.bytes_decode_window_offset_zero_32_rdx_rax
#print axioms Codec.bytes_decode_window_offset_zero_32_rdx_rcx
#print axioms Codec.bytes_decode_window_offset_zero_32_rdx_rdi
#print axioms Codec.bytes_decode_window_offset_zero_32_rdx_rdx
#print axioms Codec.bytes_decode_window_offset_zero_32_rdx_rsi
#print axioms Codec.bytes_decode_window_offset_zero_32_rsi_rax
#print axioms Codec.bytes_decode_window_offset_zero_32_rsi_rcx
#print axioms Codec.bytes_decode_window_offset_zero_32_rsi_rdi
#print axioms Codec.bytes_decode_window_offset_zero_32_rsi_rdx
#print axioms Codec.bytes_decode_window_offset_zero_32_rsi_rsi
#print axioms Codec.bytes_decode_window_offset_zero_48_rdx_rax
#print axioms Codec.bytes_decode_window_offset_zero_48_rdx_rcx
#print axioms Codec.bytes_decode_window_offset_zero_48_rdx_rdi
#print axioms Codec.bytes_decode_window_offset_zero_48_rdx_rdx
#print axioms Codec.bytes_decode_window_offset_zero_48_rdx_rsi
#print axioms Codec.bytes_decode_window_offset_zero_48_rsi_rax
#print axioms Codec.bytes_decode_window_offset_zero_48_rsi_rcx
#print axioms Codec.bytes_decode_window_offset_zero_48_rsi_rdi
#print axioms Codec.bytes_decode_window_offset_zero_48_rsi_rdx
#print axioms Codec.bytes_decode_window_offset_zero_48_rsi_rsi
#print axioms Codec.bytes_decode_window_offset_zero_96_rdx_rax
#print axioms Codec.bytes_decode_window_offset_zero_96_rdx_rcx
#print axioms Codec.bytes_decode_window_offset_zero_96_rdx_rdi
#print axioms Codec.bytes_decode_window_offset_zero_96_rdx_rdx
#print axioms Codec.bytes_decode_window_offset_zero_96_rdx_rsi
#print axioms Codec.bytes_decode_window_offset_zero_96_rsi_rax
#print axioms Codec.bytes_decode_window_offset_zero_96_rsi_rcx
#print axioms Codec.bytes_decode_window_offset_zero_96_rsi_rdi
#print axioms Codec.bytes_decode_window_offset_zero_96_rsi_rdx
#print axioms Codec.bytes_decode_window_offset_zero_96_rsi_rsi
#print axioms Codec.bytes_decode_window_offset_zero_20_rdx_rax
#print axioms Codec.bytes_decode_window_offset_zero_20_rdx_rcx
#print axioms Codec.bytes_decode_window_offset_zero_20_rdx_rdi
#print axioms Codec.bytes_decode_window_offset_zero_20_rdx_rdx
#print axioms Codec.bytes_decode_window_offset_zero_20_rdx_rsi
#print axioms Codec.bytes_decode_window_offset_zero_20_rsi_rax
#print axioms Codec.bytes_decode_window_offset_zero_20_rsi_rcx
#print axioms Codec.bytes_decode_window_offset_zero_20_rsi_rdi
#print axioms Codec.bytes_decode_window_offset_zero_20_rsi_rdx
#print axioms Codec.bytes_decode_window_offset_zero_20_rsi_rsi
#print axioms Codec.bytes_decode_segment_window
#print axioms Codec.bytes_decode_segment_offset_zero_window
#print axioms Codec.bytes_decode_inline_window_rdx_rsi_rdi
#print axioms Codec.bytes_decode_inline_window_rdx_rbx_rsi
#print axioms Codec.bytes_decode_inline_segment_window
#print axioms Codec.bytesDecodeInlineSegmentKindWindow_of
#print axioms Codec.callDecodeSegmentKindWindow_of
#print axioms Codec.call_decode_segment_window
#print axioms Codec.decode_prologue_segment
#print axioms Codec.decode_return_segment
#print axioms Codec.eraseNop_cons
#print axioms Codec.eraseNop_cons_nop
#print axioms Codec.eventually_index_congr
#print axioms Codec.infix_head
#print axioms Codec.infix_tail
#print axioms Codec.step_add_immediate
#print axioms Codec.step_jump
#print axioms Codec.step_label
#print axioms Codec.step_load_bytes
#print axioms Codec.step_load_value
#print axioms Codec.step_lea
#print axioms Codec.step_move_register
#print axioms Codec.step_move_immediate
#print axioms Codec.step_nil_check
#print axioms Codec.step_nops
#print axioms Codec.step_store
#print axioms Codec.nil_infix
#print axioms Codec.nonNopIndex_cons_nop
#print axioms Codec.nonNopIndex_cons_succ
#print axioms Codec.nonNopIndex_cons_zero
#print axioms Codec.nonNopIndex_length
#print axioms Codec.nop_step
#print axioms Codec.stepAddKind_of
#print axioms Codec.stepJumpKind_of
#print axioms Codec.stepLabelKind_of
#print axioms Codec.stepLoadBytesKind_of
#print axioms Codec.stepLoadValueKind_of
#print axioms Codec.stepLeaKind_of
#print axioms Codec.stepMoveImmediateKind_of
#print axioms Codec.stepMoveRegisterKind_of
#print axioms Codec.stepNopsKind_of
#print axioms Codec.stepStoreKind_of
#print axioms Codec.window_directive_at
#print axioms Codec.window_directive_at_aux
#print axioms Codec.window_infix_at
#print axioms Codec.window_skip_after_last
#print axioms Codec.window_only_nops
#print axioms Codec.window_skip_between
#print axioms Codec.window_skip_leading
#print axioms Codec.window_skip_aux
#print axioms Codec.AllPlaced
#print axioms Codec.Conjunctions
#print axioms Codec.DecoderFrameLayout
#print axioms Codec.DecoderFrameLayout.callees
#print axioms Codec.DecoderFrameLayout.existentials
#print axioms Codec.DecoderFrameLayout.frame
#print axioms Codec.DecoderFrameLayout.guardAddend
#print axioms Codec.DecoderFrameLayout.stackChunkLengths
#print axioms Codec.DecoderFrameLayout.stackChunkCount
#print axioms Codec.DecoderFrameLayout.post
#print axioms Codec.DecoderFrameLayout.pre
#print axioms Codec.DecoderFrameLayout.runtime
#print axioms Codec.DecoderFrameLayout.stateWord
#print axioms Codec.ExistsChunks
#print axioms Codec.ExistentialLength
#print axioms Codec.ExistentialLength.len
#print axioms Codec.ExistentialLength.low
#print axioms Codec.ExistentialLength.low.elim
#print axioms Codec.ExistentialLength.fixed
#print axioms Codec.ExistentialLength.fixed.elim
#print axioms Codec.DecodeRegisterValue
#print axioms Codec.DecodeRegisterValue.buffer
#print axioms Codec.DecodeRegisterValue.buffer.elim
#print axioms Codec.DecodeRegisterValue.receiver
#print axioms Codec.DecodeRegisterValue.receiver.elim
#print axioms Codec.DecodeRegisterValue.val
#print axioms Codec.DecodeRegisterValue.zero
#print axioms Codec.DecodeRegisterValue.zero.elim
#print axioms Codec.RuntimeConfig
#print axioms Codec.RuntimeConfig.scratchBound
#print axioms Codec.RuntimeConfig.lowOffset
#print axioms Codec.RuntimeConfig.lowOffsetOf
#print axioms Codec.RuntimeConfig.lowIndex
#print axioms Codec.RuntimeConfig.lowExtra
#print axioms Codec.RuntimeConfig.lowExtraOf
#print axioms Codec.StackOffset
#print axioms Codec.StackOffset.addr
#print axioms Codec.StackOffset.below
#print axioms Codec.StackOffset.below.elim
#print axioms Codec.StackOffset.above
#print axioms Codec.StackOffset.above.elim
#print axioms Codec.StackSlot
#print axioms Codec.StackSlot.at
#print axioms Codec.StackSlot.at.elim
#print axioms Codec.StackSlot.chunk
#print axioms Codec.StackSlot.low
#print axioms Codec.StackSlot.low.elim
#print axioms Codec.StackValue
#print axioms Codec.StackValue.bytes
#print axioms Codec.StackValue.existential
#print axioms Codec.StackValue.existential.elim
#print axioms Codec.StackValue.original
#print axioms Codec.StackValue.original.elim
#print axioms Codec.StackValue.ptr
#print axioms Codec.StackValue.ptr.elim
#print axioms Codec.StackValue.reg
#print axioms Codec.StackValue.reg.elim
#print axioms Codec.StackValue.ret
#print axioms Codec.StackValue.ret.elim
#print axioms Codec.StackValue.zero
#print axioms Codec.StackValue.zero.elim
#print axioms Codec.DecodeBoundaryState
#print axioms Codec.DecodeBoundaryState.done
#print axioms Codec.DecodeBoundaryState.existentials
#print axioms Codec.DecodeBoundaryState.pc
#print axioms Codec.DecodeBoundaryState.regs
#print axioms Codec.DecodeBoundaryState.stackSlots
#print axioms Codec.addExtra
#print axioms Codec.chunkLengthFacts
#print axioms Codec.decodeAcceptKindAnyFrame
#print axioms Codec.decodeBinders
#print axioms Codec.decodeEpilogueKindAnyFrame
#print axioms Codec.decodeErrorBlock
#print axioms Codec.decodeFieldKindAnyFrame
#print axioms Codec.decodeFinalStatePredicate
#print axioms Codec.decodeHeadKindAnyFrame
#print axioms Codec.decodeMem
#print axioms Codec.decodeRejectKindAnyFrame
#print axioms Codec.decodeBoundaryStatePredicate
#print axioms Codec.decode_epilogue_any_frame
#print axioms Codec.decode_reject_segment
#print axioms Codec.existentialLengthFacts
#print axioms Codec.frame_join_three_words
#print axioms Codec.frame_low_address_with_calls
#print axioms Codec.frame_low_address_without_calls
#print axioms Codec.decode_stack_low_eq
#print axioms Codec.frame_low_stack_split
#print axioms Codec.decodeRegisterFacts
#print axioms Codec.runtimeBinders
#print axioms Codec.scratchBoundFacts
#print axioms Codec.ForallWords
#print axioms Codec.EncodeRegisterValue
#print axioms Codec.EncodeRegisterValue.cap
#print axioms Codec.EncodeRegisterValue.cap.elim
#print axioms Codec.EncodeRegisterValue.len
#print axioms Codec.EncodeRegisterValue.len.elim
#print axioms Codec.EncodeRegisterValue.ptr
#print axioms Codec.EncodeRegisterValue.ptr.elim
#print axioms Codec.EncodeRegisterValue.receiver
#print axioms Codec.EncodeRegisterValue.receiver.elim
#print axioms Codec.EncodeRegisterValue.val
#print axioms Codec.EncodeStackSlot
#print axioms Codec.EncodeStackSlot.at
#print axioms Codec.EncodeStackSlot.at.elim
#print axioms Codec.EncodeStackSlot.chunk
#print axioms Codec.EncodeStackSlot.low
#print axioms Codec.EncodeStackSlot.low.elim
#print axioms Codec.EncodeStackValue
#print axioms Codec.EncodeStackValue.bytes
#print axioms Codec.EncodeStackValue.existential
#print axioms Codec.EncodeStackValue.existential.elim
#print axioms Codec.EncodeStackValue.field
#print axioms Codec.EncodeStackValue.field.elim
#print axioms Codec.EncodeStackValue.len
#print axioms Codec.EncodeStackValue.len.elim
#print axioms Codec.EncodeStackValue.original
#print axioms Codec.EncodeStackValue.original.elim
#print axioms Codec.EncodeStackValue.reg
#print axioms Codec.EncodeStackValue.reg.elim
#print axioms Codec.EncodeStackValue.ret
#print axioms Codec.EncodeStackValue.ret.elim
#print axioms Codec.EncodeStackValue.scratch
#print axioms Codec.EncodeStackValue.scratch.elim
#print axioms Codec.EncoderFrameLayout
#print axioms Codec.EncoderFrameLayout.existentials
#print axioms Codec.EncoderFrameLayout.frame
#print axioms Codec.EncoderFrameLayout.guardAddend
#print axioms Codec.EncoderFrameLayout.stackChunkLengths
#print axioms Codec.EncoderFrameLayout.mk
#print axioms Codec.EncoderFrameLayout.stackChunkCount
#print axioms Codec.EncoderFrameLayout.post
#print axioms Codec.EncoderFrameLayout.pre
#print axioms Codec.EncoderFrameLayout.callsMemmove
#print axioms Codec.EncoderFrameLayout.stateWord
#print axioms Codec.EncodeBoundaryState
#print axioms Codec.EncodeBoundaryState.done
#print axioms Codec.EncodeBoundaryState.existentials
#print axioms Codec.EncodeBoundaryState.mk
#print axioms Codec.EncodeBoundaryState.pc
#print axioms Codec.EncodeBoundaryState.regs
#print axioms Codec.EncodeBoundaryState.stackSlots
#print axioms Codec.cmp_c_false
#print axioms Codec.cmp_nc_true
#print axioms Codec.cmp_nz_false
#print axioms Codec.contentLengthFacts
#print axioms Codec.encodeBinders
#print axioms Codec.encodeContentChunks
#print axioms Codec.encodeEpilogueKindAnyFrame
#print axioms Codec.encodeFastPathKindAnyFrame
#print axioms Codec.encodeFieldKindAnyFrame
#print axioms Codec.encodeFinalStatePredicate
#print axioms Codec.encodeHeadKindAnyFrame
#print axioms Codec.encodeLengthFacts
#print axioms Codec.encodeMem
#print axioms Codec.encodeBinderCount
#print axioms Codec.encodeOutputChunks
#print axioms Codec.encoderPrologueLargeFrame
#print axioms Codec.encoderPrologueSmallFrame
#print axioms Codec.encodeReceiverChunks
#print axioms Codec.encodeRuntimeBinders
#print axioms Codec.encodeBoundaryStatePredicate
#print axioms Codec.encode_memmove_call
#print axioms Codec.encoder_prologue_large_frame
#print axioms Codec.encoder_prologue_small_frame
#print axioms Codec.encodeRegisterFacts
#print axioms Codec.fieldValues
#print axioms Codec.frame50_pointer_apart
#print axioms Codec.int64_neg_toBitVec
#print axioms Codec.instrAddRegisters
#print axioms Codec.instrCompareMemoryImmediate
#print axioms Codec.instrCompareRegisters
#print axioms Codec.instrConditionalJump
#print axioms Codec.instrLeaIndexed
#print axioms Codec.instrStoreXmm15
#print axioms Codec.instrStoreIndexed
#print axioms Codec.instrSubImmediate
#print axioms Codec.instrSubRegisters
#print axioms Codec.instrXor32
#print axioms Codec.register_value_rewrite
#print axioms Codec.step_add_registers
#print axioms Codec.step_cmp_jae_taken
#print axioms Codec.step_cmp_jb_not_taken
#print axioms Codec.step_lea_indexed
#print axioms Codec.step_length_check
#print axioms Codec.step_store_xmm15
#print axioms Codec.step_store_indexed
#print axioms Codec.step_load_bytes32
#print axioms Codec.step_store_indexed32
#print axioms Codec.step_sub_immediate
#print axioms Codec.step_sub_registers
#print axioms Codec.step_xor32
#print axioms Codec.countUint64Fields
#print axioms Codec.separated_chunks_apart
#print axioms Codec.bindersCapacity
#print axioms Codec.bindersContent
#print axioms Codec.bindersOverwritten
#print axioms Codec.bindersPrefix
#print axioms Codec.bindersUint64
#print axioms _aux_Codec_EncodeFieldHelpers___macroRules_tacticEncoder_address_equation_1
#print axioms tacticEncoder_address_equation
#print axioms Codec.Segment.flat_len
#print axioms Codec.Segment.in_split
#print axioms Codec.Segment.backing_array_split
#print axioms Codec.Segment.backing_array_join
#print axioms Codec.Segment.glue_nop
#print axioms Codec.Segment.glue_source
#print axioms Codec.Segment.glue_of
#print axioms Codec.Segment.bytes32_loop_iteration
#print axioms Codec.Segment.bytes32_loop_exit
#print axioms Codec.Segment.bytes32_loop
#print axioms Codec.Segment.reject_size_any_frame
#print axioms Codec.Segment.bytes32_vector_serialize
#print axioms Codec.Segment.bytes32_vector_of_bytes
