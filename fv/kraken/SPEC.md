# SPEC: EthLib specification, Go value abstraction and error mapping of the 1a and 1b target types

The specification is in `lean/Fv1/Spec*.lean` (it uses only EthLib `Desc`), and the connection theorems are in `lean/Fk/*Spec.lean` and `*Err.lean`.

On 2026-11-12, commit `84a4747` removed most connection theorems and `semtest/`. Tag `archive/fv-before-workflow` holds them.
The specification files `lean/Fv1/Spec*.lean` stay. In the tables below, "(removed)" marks a theorem that is not in the current tree.
A type, Go check or range without a kept theorem is a description of the Go 1.26.3 target code only.

Terms:
- **Desc**: the SSZ type descriptor of EthLib.
- **Abstraction**: the function `toValue` that maps a Go value `g` to an EthLib `Value`. It is injective, and it is surjective onto all values that fit the Desc (the theorem names are in the table).
- **enc**: the Go encoder output written as a function of the Go value. We prove `serialize d (toValue g) = .ok (enc g)`. Then every input that EthLib accepts is `enc g` for some `g` (`Transfer.accepted_is_enc`).

## 1. Targets and fixed commits

| Type | Go definition | Generated code | Notes |
| --- | --- | --- | --- |
| Scalars, FixedVec, ListU64 | `target/types.go` | `target/types.ssz.go` | 1a target |
| BitVec, Nested, ListC, BitL | `target/types1b.go` | `target/types1b.ssz.go` (`go run ./cmd/ssz gen --type-names BitVec,Nested,ListC,BitL`) | 1b target |
| Checkpoint, AttestationData | `target/prysm/types.go` | `target/prysm/types.ssz.go` | Prysm v7.1.8, commit `51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`, `proto/prysm/v1alpha1/attestation.pb.go`. We copied the field names, Go kinds and ssz tags without change. We did not copy the protobuf fields (`state`, `unknownFields`, `sizeCache`). Thus the Go struct layout is different from Prysm. The SSZ schema is the same. |

The hashes of the generated files are in `link/out/build-ids.txt`.

## 2. Specification for each type

| Type | Desc (`lean/Fv1`) | Go value abstraction | enc | Injective, surjective, serialize |
| --- | --- | --- | --- | --- |
| Scalars | `scDesc = container [uint 1, uint 2, uint 4, uint 8, bool]` | `Scalars` (UInt8, UInt16, UInt32, UInt64, Bool) | `scEncode` (16 bytes) | `sc_toValue_injective`, `sc_toValue_surjective`, `sc_serialize` |
| FixedVec | `fvDesc = container [byteVector 32, vector (uint 8) 4]` | `FixedVecG` (Vector UInt8 32, Vector UInt64 4) | `fvEncode` (64) | `fv_toValue_injective`, `fv_toValue_surjective`, `fv_serialize` |
| ListU64 | `luDesc = container [list (uint 8) 16]` | `ListU64` (List UInt64), `ok` = length ≤ 16 | `luEncode` = offset 4 ‖ elements | `lu_toValue_injective`, `lu_toValue_surjective`, `lu_serialize` |
| BitVec | `bvDesc = container [bitVector 4]` | `BitVecG` (byte b, b < 16) | `#[b]` | `bv_toValue_injective`, `bv_toValue_surjective`, `bv_serialize` |
| Nested | `neDesc = container [uint 8, scDesc, luDesc]` | `NestedG` (UInt64, Scalars, ListU64), `ok` = `l.ok` | `neEncode` = A ‖ S ‖ offset 28 ‖ `luEncode l` | `ne_toValue_injective`, `ne_toValue_surjective`, `ne_serialize` |
| ListC | `lcDesc = container [list luDesc 4]` | `ListCG` (List ListU64), `ok` = length ≤ 4 and `ok` for each element | `lcEncode` = offset 4 ‖ offset table (first value 4n) ‖ element encodings | `lc_toValue_injective` (removed, `Fk/RoundTrip1b.lean`), `lc_toValue_surjective`, `lc_serialize` |
| Checkpoint | `cpDesc = container [uint 8, byteVector 32]` | `CheckpointG` (UInt64, Vector UInt8 32) | `cpEncode` (40) | `cp_toValue_injective`, `cp_toValue_surjective`, `cp_serialize` |
| AttestationData | `adDesc = container [uint 8, uint 8, byteVector 32, cpDesc, cpDesc]` | `AttestationDataG` | `adEncode` (128) | `ad_toValue_injective`, `ad_toValue_surjective`, `ad_serialize` |
| BitL | `blDesc = container [bitList 2048]` | `BitLG` (Array Bool, size ≤ 2048) | `blEncode` = offset 4 ‖ `packBitsDelimited` | `bl_toValue_surjective`, `bl_serialize`, injectivity is proved in `bl_roundtrip` (removed) |

Cases where a Go value does not map to an EthLib value (outside the domain of the abstraction):
- FixedVec `len(W) ≠ 4`, Checkpoint and AttestationData `len(Root) ≠ 32`: the encoder returns `ssz.ErrBytesLength`.
- ListU64 elements > 16, ListC elements > 4: the encoder returns `ssz.ErrListTooBig`.
- BitVec byte with a padding bit set (b ≥ 16): the decoder accepts it (finding F1).
- BitL `len(c.B)` is 258 to 2048 bytes: the encoder accepts it (finding F2).

## 3. Decoder error mapping (in the Go check order)

"EthLib" is a theorem that shows that EthLib also rejects when that check fails. "Machine code" is a Kraken theorem that shows that the Go code returns that error.

| Type | Go check | Go error | EthLib | Machine code |
| --- | --- | --- | --- | --- |
| Scalars | len ≠ 16 | `ErrSize` | `sc_serialize` + fixed size | `sc_reject_size_main` (removed) |
| Scalars | bool byte > 1 | `ErrInvalidSerialization` | `sc_spec_rejects_bool` (removed) | `sc_reject_bool_main` (removed) |
| FixedVec | len ≠ 64 | `ErrSize` | `fv_reject_spec` (removed) | `fv_reject_size_main` (removed) |
| ListU64 | len < 4 | `ErrSize` | `lu_spec_rejects` | `lu_reject_short_main` |
| ListU64 | offset ≠ 4 | `ErrInvalidVariableOffset` | `lu_spec_rejects` | `lu_reject_offset_main` |
| ListU64 | (len − 4) mod 8 ≠ 0 | `fmt.Errorf(… %w, ErrIncorrectListSize)` | `lu_spec_rejects` | `lu_reject_misaligned_main` (rax ≠ 0) |
| ListU64 | (len − 4) / 8 > 16 | `fmt.Errorf(… %w, ErrListTooBig)` | `lu_spec_rejects` | `lu_reject_toobig_main` (rax ≠ 0) |
| BitVec | len ≠ 1 | `ErrSize` | `bv_reject_spec` (removed) | `bv_reject_size_main` (removed) |
| BitVec | padding bits (`ssz.ValidateBitvector`) | `fmt.Errorf("J: %w")` | `bv_spec_one` (removed), `bv_spec_accepts_iff` (removed) | `bv_reject_padding_main` (removed) (rax ≠ 0) |
| Nested | len < 28 | `ErrSize` | `ne_spec_rejects` (removed) | `ne_reject_short_spec` (removed) |
| Nested | offset (24..27) ≠ 28 | `ErrInvalidVariableOffset` | `ne_spec_rejects` (removed) | `ne_reject_offset_spec` (removed) |
| Nested | S decoder fails (bool) | `fmt.Errorf("S: %w")` | `ne_spec_accepts_iff` (removed) | None |
| Nested | L decoder fails | `fmt.Errorf("L: %w")` | `ne_spec_accepts_iff` (removed) | None |
| ListC | len < 4 | `ErrSize` | `lc_spec_rejects` (removed) | `lc_reject_short_spec` (removed) |
| ListC | offset ≠ 4 | `ErrInvalidVariableOffset` | `lc_spec_rejects` (removed) | `lc_reject_offset_spec` (removed) |
| ListC | list bytes 1 to 3 | `fmt.Errorf` (not wrapped) | `lc_spec_rejects` (removed) | `lc_reject_tail_spec` (removed) (rax ≠ 0) |
| ListC | first element offset 0 | `fmt.Errorf` | `lc_spec_rejects` (removed) | `lc_reject_zero_spec` (removed) (rax ≠ 0) |
| ListC | first offset mod 4 ≠ 0 | `fmt.Errorf` (%d, convT64) | `lc_shape` (removed) (first offset = 4n) | None |
| ListC | first offset / 4 > 4 | `fmt.Errorf(… %w, ErrListTooBig)` | `lc_shape` (removed) | None |
| ListC | first offset > list length | `fmt.Errorf` | `lc_spec_rejects` (removed) | `lc_reject_past_spec` (removed) (rax ≠ 0) |
| ListC | next offset > length, offset decreases | `fmt.Errorf` | None | None |
| ListC | element decoder fails | `fmt.Errorf("Items: %w")` | None | None |
| Checkpoint | len ≠ 40 | `ErrSize` | `cp_reject_size_spec` (removed) (`cp_spec_accepts_iff` (removed)) | `cp_reject_size_main` (removed) |
| AttestationData | len ≠ 128 | `ErrSize` | `ad_reject_size_spec` (removed) (`ad_spec_accepts_iff` (removed)) | `ad_reject_size_main` (removed) |
| BitL | len < 4 | `ErrSize` | `bl_spec_rejects` (removed) | `bl_reject_short_main` (removed) |
| BitL | offset ≠ 4 | `ErrInvalidVariableOffset` | `bl_spec_rejects` (removed) | `bl_reject_offset_main` (removed) |
| BitL | `ValidateBitlist` fails | `fmt.Errorf("B: %w")` | `bl_spec_rejects` (removed) (`blValid` false) | `bl_reject_invalid_main` (removed) (rax ≠ 0, after the contract `ValidateBitlistErrC` (removed)) |

Accept side: `*_unmarshal_accept_spec_k` says "if EthLib accepts, the machine code returns nil and the receiver holds that value" (Scalars, ListU64, FixedVec, Nested, ListC, Checkpoint, AttestationData, BitL). Only the Scalars and ListU64 theorems are in the current tree. For BitVec, `bv_unmarshal_accept_spec_k` (removed) said only a byte equation (`bs = #[g.b]`). The theorem that included machine execution was `bv_unmarshal_accept_machine` (removed). The table in section 7 keeps the two apart. ListC has two theorems: input with 1 or more elements (`lc_unmarshal_accept_spec_k` (removed), `len(buf) > 4`) and the empty list (`lc_unmarshal_accept_empty_spec_k` (removed), `len(buf) = 4`, result `c.Items` = (`runtime.zerobase`, 0, 0), premise X15 = 0).

### 3.1 The first offset `> size` check

The generator does not emit an `off > size` check after the first offset of ListU64, Nested, ListC and BitL (generator fix G3).
The first offset is equal to the fixed size and the fixed size ≤ len, so the code cannot reach that check.
`lc_reject_past_main` (removed) was the theorem for the case where the first **element** offset is larger than the list length. It is not related to G3.

## 4. Range of offset reads and writes

`ssz.ReadOffset(buf) = uint64(binary.LittleEndian.Uint32(buf))`, `ssz.WriteOffset(dst, i int) = AppendUint32(dst, uint32(i))`.

| Call site | Machine code | Range |
| --- | --- | --- |
| ListU64 decoder `ReadOffset(buf[0:4])` | `mov (%rbx),%edx` (32-bit load, zero extension) | Value < 2^32. `lu_off4` shows that it is equal to the `Int.ofBytes` value |
| Nested decoder `ReadOffset(buf[24:28])` | `mov 0x18(%rbx),%edx` | Same. `ne_off28` (removed) |
| ListC decoder `ReadOffset(buf[0:4])`, first element offset | `mov (%rbx),%edx`, `mov (%rbx,%rdx,1),%ebx` | Same. `lu_off4`, `zx_o` (removed) |
| ListC decoder next element offset | 32-bit load in the loop | Same. `lcl_iter` (removed) |
| BitL decoder `ReadOffset(buf[0:4])` | `mov (%rbx),%edx` | Same. `lu_off4` |
| ListU64 encoder `WriteOffset(dst, 4)` | `movl $0x4,…` | Constant. `lu_marshal_main` (removed) |
| BitL encoder `WriteOffset(dst, 4)` | `movl $0x4,-0x4(%rdx,%rbx,1)` | Constant. `bl_marshal_main` (removed) |
| Nested encoder `WriteOffset(dst, 28)` | Constant | Constant. `ne_marshal_main` (removed) |
| ListC encoder `WriteOffset(dst, 4)`, element offset `4n + Σ size` | `movl $0x4`, `mov %r8d,-0x4(%rdx,%rbx,1)` (`int` → `uint32` truncation) | Fast-path proof: shows that the 4 bytes that `lcm2_loop` (removed) writes are equal to `offTab` (removed) (EthLib `uintBytes 4`). Each element has length ≤ 16 (`g.ok`), so the value ≤ 544 < 2^32 and the truncation does not change the value (`lc_marshal_main` (removed)). Go-level basis (outside the fast path): on the success path, each element has length ≤ 16, so the offset ≤ 16 + 4·132 = 544 < 2^32. If an element has a length larger than 2^29, the code writes the truncated value, then the encoder of that element returns `ErrListTooBig`, and the function returns `nil, err` (the written bytes are discarded). EthLib `offsetOverflow` (total ≥ 2^32) does not occur on this success path |

On the decoder side, the reads are 4-byte loads, so there is no int→uint32 conversion. On the write side, the only truncation is in the ListC encoder.

## 5. Negative inputs

This section described the negative inputs of each type in `semtest/cases.why`, the Go reference results in `semtest/expected.txt` and the hardware comparison script `semtest/run.sh`.
`semtest/` was removed on 2026-11-12. Tag `archive/fv-before-workflow` holds it.

## 6. Bitlist validation

In the `GOAMD64=v1` build, `ssz.ValidateBitlist` does not read a rodata table.
`bits.Len8` compiles to `bsr %r8d,%r8d`.
Kraken cannot parse `bsr`, so the full function was the contracts `ValidateBitlistC` and `ValidateBitlistErrC` (`Fk/Vbl.lean`).
**The core bitlist checks (empty input, last byte 0, more than 2048 bits) were behind the contract.**
The contract was "rax = 0 ⟺ EthLib `unpackDelimited (some 2048)` accepts".
`Fk/Vbl.lean` was removed on 2026-11-12. If Kraken gets `bsr`, a proof of the function can replace the contract.

## 7. Completion table: theorems that include machine execution and byte equation theorems

"Machine code" is a theorem that has `Eventually (step1 Host.exe) …` in its conclusion.
"Byte equation" is a theorem that speaks only about equations of EthLib `serialize`/`deserialize` and Go values.
A byte equation theorem does not speak about machine execution.
A round-trip theorem (`*_roundtrip`) is a byte equation theorem that reads `enc g` again in EthLib.
There is no theorem about a continuous machine execution that runs the decoder after the encoder.

| Type | Encoder: machine code | Encoder: byte equation | Decoder accept: machine code + EthLib | Decoder accept: byte equation only |
| --- | --- | --- | --- | --- |
| Scalars | `sc_marshal_main`, `sc_marshal_spec_k` | `sc_serialize` | `sc_unmarshal_accept_spec_k` | |
| FixedVec | `fv_marshal_main` | `fv_marshal_spec_k` (removed), `fv_serialize` | `fv_unmarshal_accept_spec_k` (removed) | |
| ListU64 | `lu_marshal_main` (removed) | `lu_serialize` | `lu_unmarshal_accept_spec_k` | |
| BitVec | `bv_marshal_main` (removed) | `bv_serialize` | `bv_unmarshal_accept_machine` (removed) | `bv_unmarshal_accept_spec_k` (removed) |
| Nested | `ne_marshal_main` (removed) | `ne_marshal_bytes` (removed), `ne_serialize` | `ne_unmarshal_accept_spec_k` (removed) | |
| ListC | `lc_marshal_main` (removed) | `lc_marshal_spec_k` (removed), `lc_serialize` | `lc_unmarshal_accept_spec_k` (removed), `lc_unmarshal_accept_empty_spec_k` (removed) | |
| Checkpoint | `cp_marshal_main` (removed), `cp_marshal_spec_k` (removed) | `cp_serialize` | `cp_unmarshal_accept_spec_k` (removed) | |
| AttestationData | `ad_marshal_main` (removed) | `ad_marshal_bytes` (removed), `ad_serialize` | `ad_unmarshal_accept_spec_k` (removed) | |
| BitL | `bl_marshal_main` (removed) | `bl_serialize` | `bl_unmarshal_accept_spec_k` (removed) (after `ValidateBitlistC` (removed)) | |

This table speaks only about the form of the theorems.
The gate 1 table in section 2 of `REPORT.md` said whether premise witnesses existed. The table and the witnesses were removed on 2026-11-12.
