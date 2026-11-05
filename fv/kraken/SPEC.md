# SPEC: 1a·1b 대상 타입의 EthLib 명세, Go 값 추상화, 오류 대응

작성 2026-11-05. 명세는 `lean/Fv1/Spec*.lean`(EthLib `Desc`만 쓴다), 연결 정리는 `lean/Fk/*Spec.lean`, `*Err.lean`이다.

용어:
- **Desc**: EthLib의 SSZ 타입 기술자.
- **추상화**: Go 값 `g`를 EthLib `Value`로 보내는 함수 `toValue`. 단사이고, Desc에 맞는 값 전체로 전사다(정리 이름은 표에).
- **enc**: Go 인코더 출력을 Go 값의 함수로 적은 것. `serialize d (toValue g) = .ok (enc g)`를 증명한다. 그러면 EthLib가 받는 입력은 모두 어떤 `g`의 `enc g`다(`Transfer.accepted_is_enc`).

## 1. 대상과 고정 커밋

| 타입 | Go 정의 | 생성 코드 | 비고 |
| --- | --- | --- | --- |
| Scalars, FixedVec, ListU64 | `target/types.go` | `target/types.ssz.go` | 1a 대상 |
| BitVec, Nested, ListC, BitL | `target/types1b.go` | `target/types1b.ssz.go` (`go run ./cmd/ssz gen --type-names BitVec,Nested,ListC,BitL`) | 1b 대상 |
| Checkpoint, AttestationData | `target/prysm/types.go` | `target/prysm/types.ssz.go` | Prysm v7.1.8, 커밋 `51b5a75ebbadf05af22bd2601b5baf7a9e99b66d`, `proto/prysm/v1alpha1/attestation.pb.go`. 필드 이름, Go 종류, ssz 태그를 그대로 옮겼다. protobuf 필드(`state`, `unknownFields`, `sizeCache`)는 옮기지 않았다. 그래서 Go 구조체 배치는 Prysm과 다르다(REPORT-1b 이견). SSZ 스키마는 같다. |

생성 파일 해시는 `link/out/build-ids.txt`에 있다.

## 2. 타입별 명세

| 타입 | Desc (`lean/Fv1`) | Go 값 추상화 | enc | 단사·전사·serialize |
| --- | --- | --- | --- | --- |
| Scalars | `scDesc = container [uint 1, uint 2, uint 4, uint 8, bool]` | `Scalars` (UInt8, UInt16, UInt32, UInt64, Bool) | `scEncode` (16바이트) | `sc_toValue_injective`, `sc_toValue_surjective`, `sc_serialize` |
| FixedVec | `fvDesc = container [byteVector 32, vector (uint 8) 4]` | `FixedVecG` (Vector UInt8 32, Vector UInt64 4) | `fvEncode` (64) | `fv_toValue_injective`, `fv_toValue_surjective`, `fv_serialize` |
| ListU64 | `luDesc = container [list (uint 8) 16]` | `ListU64` (List UInt64), `ok` = 길이 ≤ 16 | `luEncode` = 오프셋 4 ‖ 원소 | `lu_toValue_injective`, `lu_toValue_surjective`, `lu_serialize` |
| BitVec | `bvDesc = container [bitVector 4]` | `BitVecG` (바이트 b, b < 16) | `#[b]` | `bv_toValue_injective`, `bv_toValue_surjective`, `bv_serialize` |
| Nested | `neDesc = container [uint 8, scDesc, luDesc]` | `NestedG` (UInt64, Scalars, ListU64), `ok` = `l.ok` | `neEncode` = A ‖ S ‖ 오프셋 28 ‖ `luEncode l` | `ne_toValue_injective`, `ne_toValue_surjective`, `ne_serialize` |
| ListC | `lcDesc = container [list luDesc 4]` | `ListCG` (List ListU64), `ok` = 길이 ≤ 4이고 원소마다 `ok` | `lcEncode` = 오프셋 4 ‖ 오프셋 표(첫 값 4n) ‖ 원소 인코딩 | `lc_toValue_surjective`, `lc_serialize` (단사는 하지 않았다: 왕복 정리에 필요하다) |
| Checkpoint | `cpDesc = container [uint 8, byteVector 32]` | `CheckpointG` (UInt64, Vector UInt8 32) | `cpEncode` (40) | `cp_toValue_injective`, `cp_toValue_surjective`, `cp_serialize` |
| AttestationData | `adDesc = container [uint 8, uint 8, byteVector 32, cpDesc, cpDesc]` | `AttestationDataG` | `adEncode` (128) | `ad_toValue_injective`, `ad_toValue_surjective`, `ad_serialize` |
| BitL | `blDesc = container [bitList 2048]` | `BitLG` (Array Bool, 크기 ≤ 2048) | `blEncode` = 오프셋 4 ‖ `packBitsDelimited` | `bl_toValue_surjective`, `bl_serialize` |

Go 값이 EthLib 값으로 가지 못하는 경우(추상화의 정의역 밖):
- FixedVec `len(W) ≠ 4`, Checkpoint·AttestationData `len(Root) ≠ 32`: 인코더가 `ssz.ErrBytesLength`를 반환한다.
- ListU64 원소 > 16, ListC 원소 > 4: 인코더가 `ssz.ErrListTooBig`를 반환한다.
- BitVec 패딩 비트가 선 바이트(b ≥ 16): 디코더가 받는다(발견 F1).
- BitL `len(c.B)`가 258~2048바이트: 인코더가 받는다(발견 F2).

## 3. 디코더 오류 대응 (Go 검사 순서대로)

"EthLib"는 그 검사가 실패하면 EthLib도 거부함을 보이는 정리다. "기계어"는 Go 코드가 그 오류를 반환함을 보이는 Kraken 정리다.

| 타입 | Go 검사 | Go 오류 | EthLib | 기계어 |
| --- | --- | --- | --- | --- |
| Scalars | len ≠ 16 | `ErrSize` | `sc_serialize` + 고정 크기 | `sc_reject_size_main` |
| Scalars | bool 바이트 > 1 | `ErrInvalidSerialization` | `ne_spec_accepts_iff`(Nested 안에서) | 없음 |
| FixedVec | len ≠ 64 | `ErrSize` | `fv_reject_spec` | `fv_reject_size_main` |
| ListU64 | len < 4 | `ErrSize` | `lu_spec_rejects` | `lu_reject_short_main` |
| ListU64 | 오프셋 ≠ 4 | `ErrInvalidVariableOffset` | `lu_spec_rejects` | `lu_reject_offset_main` |
| ListU64 | (len − 4) mod 8 ≠ 0 | `fmt.Errorf(… %w, ErrIncorrectListSize)` | `lu_spec_rejects` | `lu_reject_misaligned_main` (rax ≠ 0) |
| ListU64 | (len − 4) / 8 > 16 | `fmt.Errorf(… %w, ErrListTooBig)` | `lu_spec_rejects` | `lu_reject_toobig_main` (rax ≠ 0) |
| BitVec | len ≠ 1 | `ErrSize` | `bv_reject_spec` | `bv_reject_size_main` |
| BitVec | (검사 없음) 패딩 비트 | nil | `bv_spec_rejects_padding` | `bv_padding_counterexample` (F1) |
| Nested | len < 28 | `ErrSize` | `ne_spec_rejects` | `ne_reject_short_spec` |
| Nested | 오프셋(24..27) ≠ 28 | `ErrInvalidVariableOffset` | `ne_spec_rejects` | `ne_reject_offset_spec` |
| Nested | 오프셋 > len | `ErrOffset` | 도달 불가(오프셋 = 28 ≤ len) | 코드에 분기가 없다 |
| Nested | S 디코더 실패(bool) | `fmt.Errorf("S: %w")` | `ne_spec_accepts_iff` | 없음 |
| Nested | L 디코더 실패 | `fmt.Errorf("L: %w")` | `ne_spec_accepts_iff` | 없음 |
| ListC | len < 4 | `ErrSize` | `lc_spec_rejects` | `lc_reject_short_spec` |
| ListC | 오프셋 ≠ 4 | `ErrInvalidVariableOffset` | `lc_spec_rejects` | `lc_reject_offset_spec` |
| ListC | 목록 바이트 1~3 | `fmt.Errorf`(감싸지 않음) | `lc_spec_rejects` | `lc_reject_tail_spec` (rax ≠ 0) |
| ListC | 첫 원소 오프셋 0 | `fmt.Errorf` | `lc_spec_rejects` | `lc_reject_zero_spec` (rax ≠ 0) |
| ListC | 첫 오프셋 mod 4 ≠ 0 | `fmt.Errorf`(%d, convT64) | `lc_shape`(첫 오프셋 = 4n) | 없음 |
| ListC | 첫 오프셋 / 4 > 4 | `fmt.Errorf(… %w, ErrListTooBig)` | `lc_shape` | 없음 |
| ListC | 첫 오프셋 > 목록 길이 | `fmt.Errorf` | `lc_spec_rejects` | `lc_reject_past_spec` (rax ≠ 0) |
| ListC | 다음 오프셋 > 길이, 오프셋 감소 | `fmt.Errorf` | 없음 | 없음 |
| ListC | 원소 디코더 실패 | `fmt.Errorf("Items: %w")` | 없음 | 없음 |
| Checkpoint | len ≠ 40 | `ErrSize` | `cp_reject_size_spec` (`cp_spec_accepts_iff`) | `cp_reject_size_main` |
| AttestationData | len ≠ 128 | `ErrSize` | `ad_reject_size_spec` (`ad_spec_accepts_iff`) | `ad_reject_size_main` |
| BitL | len < 4 | `ErrSize` | `bl_spec_rejects` | `bl_reject_short_main` |
| BitL | 오프셋 ≠ 4 | `ErrInvalidVariableOffset` | `bl_spec_rejects` | `bl_reject_offset_main` |
| BitL | `ValidateBitlist` 실패 | `fmt.Errorf("B: %w")` | `bl_spec_rejects` (`blValid` 거짓) | 계약 `ValidateBitlistC` 뒤. 오류 경로는 없음 |

수용 쪽: `*_unmarshal_accept_spec_k`가 "EthLib가 받으면 기계어가 nil을 반환하고 수신자가 그 값을 담는다"를 말한다(Scalars, ListU64, FixedVec, BitVec, Nested, ListC, Checkpoint, AttestationData, BitL). ListC는 원소가 1개 이상인 입력(`len(buf) > 4`)만 다룬다. 빈 리스트(`len(buf) = 4`)의 수용 경로는 증명하지 않았다.

## 4. 오프셋 읽기·쓰기의 범위 (B3.4)

`ssz.ReadOffset(buf) = uint64(binary.LittleEndian.Uint32(buf))`, `ssz.WriteOffset(dst, i int) = AppendUint32(dst, uint32(i))`.

| 호출 지점 | 기계어 | 범위 |
| --- | --- | --- |
| ListU64 디코더 `ReadOffset(buf[0:4])` | `mov (%rbx),%edx` (32비트 적재, 0 확장) | 값 < 2^32. `lu_off4`가 `Int.ofBytes` 값과 같음을 보인다 |
| Nested 디코더 `ReadOffset(buf[24:28])` | `mov 0x18(%rbx),%edx` | 같음. `ne_off28` |
| ListC 디코더 `ReadOffset(buf[0:4])`, 첫 원소 오프셋 | `mov (%rbx),%edx`, `mov (%rbx,%rdx,1),%ebx` | 같음. `lu_off4`, `zx_o` |
| ListC 디코더 다음 원소 오프셋 | 루프 안 32비트 적재 | 같음. `lcl_iter` |
| BitL 디코더 `ReadOffset(buf[0:4])` | `mov (%rbx),%edx` | 같음. `lu_off4` |
| ListU64 인코더 `WriteOffset(dst, 4)` | `movl $0x4,…` | 상수. `lu_marshal_main` |
| BitL 인코더 `WriteOffset(dst, 4)` | `movl $0x4,-0x4(%rdx,%rbx,1)` | 상수. `bl_marshal_main` |
| Nested 인코더 `WriteOffset(dst, 28)` | 상수 | 상수. `ne_marshal_main` |
| ListC 인코더 `WriteOffset(dst, 4)`, 원소 오프셋 `4n + Σ size` | `movl $0x4`, `mov %r8d,-0x4(%rdx,%rbx,1)` (`int` → `uint32` 자르기) | 빠른 경로 증명: `lcm2_loop`가 쓴 4바이트가 `offTab`(EthLib `uintBytes 4`)과 같음을 보인다. 원소마다 길이 ≤ 16(`g.ok`)이므로 값 ≤ 544 < 2^32이고 자르기가 값을 바꾸지 않는다(`lc_marshal_main`). Go 수준 근거(빠른 경로 밖): 성공 경로에서는 원소마다 길이 ≤ 16이므로 오프셋 ≤ 16 + 4·132 = 544 < 2^32. 길이가 2^29를 넘는 원소가 있으면 자른 값을 쓴 뒤 그 원소의 인코더가 `ErrListTooBig`를 반환하고 함수는 `nil, err`를 반환한다(쓴 바이트는 버려진다). EthLib `offsetOverflow`(전체 ≥ 2^32)는 이 성공 경로에서 일어나지 않는다 |

디코더 쪽 읽기는 4바이트 적재라서 int→uint32 변환이 없다. 쓰기 쪽 자르기는 ListC 인코더 한 곳이다.

## 5. 부정 입력

타입마다 빈 값, 최소, 최대, 초과, 잘못된 오프셋(0, 작음, 큼, 정렬 안 됨)의 입력과 그 결과를 보장하는 정리는 `semtest/cases.why`에 있다. Go 기준 결과는 `semtest/expected.txt`다(x86-64 하드웨어에서는 `semtest/run.sh`가 비교한다). 증명이 없는 줄은 "not proved"로 표시했다.

## 6. bitlist 검증과 rodata 표 (B3.3)

브리프는 `bits.Len8`의 표 조회(rodata)를 C5 방식으로 두라고 했다. `GOAMD64=v1` 빌드에서 `ssz.ValidateBitlist`는 표를 읽지 않는다. `bits.Len8`은 `bsr %r8d,%r8d`로 컴파일된다(`link/out/FUNCS.md`: 이 함수의 전역 참조는 없다). 그래서 표 상수는 만들지 않았다. 함수 전체를 계약 `ValidateBitlistC`로 두었다. **bitlist의 핵심 검사(빈 입력, 끝 바이트 0, 2048비트 초과)는 계약 뒤에 있다.** 계약은 "rax = 0 ⟺ EthLib `unpackDelimited (some 2048)`가 받는다"이다. Kraken에 `bsr`이 들어오면 이 계약을 증명으로 바꿀 수 있다(REPORT-1b Kraken 요청 목록).
