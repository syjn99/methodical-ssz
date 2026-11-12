# SELECTION-ENC: 첫 가변 길이 인코더 손 증명 대상 (ENC 스트림)

이 파일은 증명 전에 커밋한다.
대상과 경로는 이 커밋 뒤에 바꾸지 않는다.

## 1. 기준

| 항목 | 값 |
| --- | --- |
| 기준 커밋 | `1b5f524` (`claude/ssz-fv-list-vector-20261112`의 머리) |
| 브랜치 | `syjn99/ssz-fv-enc` |
| 대상 ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e` (LV 스트림과 같은 ELF) |
| objdump sha256 | `580b0da9…` (`build-ids.txt`와 같다) |
| 작성 모델 | `claude-opus-5-5` (구현 담당) |

## 2. 기준 조건 (작업 지시)

- 가변 길이 필드가 정확히 하나다.
- 그 필드는 uint64 목록이나 고정 크기 바이트 벡터 목록이 좋다.
- `MarshalSSZTo`가 금지 함수를 부르지 않는다.
- 금지 타입이 아니다.

## 3. 후보 표 (`MarshalSSZTo`만)

명령어 수와 호출은 `gen/e2e/enclink.py callgraph`의 출력이다(`lv/callgraph-enc.json`).

| 타입 | 필드 | 명령어 | 호출 | 판정 |
| --- | --- | --- | --- | --- |
| `DataColumnsByRootIdentifier` (fulu) | `block_root` Bytes32, `columns` List[uint64, 128] | 107 | growslice 3, memmove 1, morestack 1 | **선정** |
| `DataColumnSidecarsByRangeRequest` (fulu) | uint64 둘, `columns` List[uint64, 128] | 126 | growslice 4, morestack 1 | 예비. 선정 대상과 같은 꼴이다 |
| `IndexedAttestation` (phase0) | List[uint64, 2048], AttestationData, Bytes96 | 173 | `AttestationData.MarshalSSZTo` 1, growslice 3, newobject 2, fmt.errorf 1, gcWriteBarrier2 1, memmove 1, morestack 1 | 제외 |

`IndexedAttestation` 확인:

- `AttestationData.MarshalSSZTo`는 인라인되지 않았다.
- objdump에 `CALL …(*AttestationData).MarshalSSZTo(SB)`가 한 번 있다.
- 그래서 작업 지시에 따라 제외한다.

`DataColumnsByRootIdentifier`는 금지 타입 목록에 없다.
이 타입의 `.S`, IR, 증명 밖의 금지 타입 파일은 열지 않았다.

## 4. 선정 대상의 Go 소스

`prysm/_generated/mainnet/fulu.ssz.go` 1754–1776행:

    func (c *DataColumnsByRootIdentifier) MarshalSSZTo(dst []byte) ([]byte, error) {
        offset := 36
        if len(c.BlockRoot) != 32 { return nil, ssz.ErrBytesLength }
        dst = append(dst, c.BlockRoot...)
        dst = ssz.WriteOffset(dst, offset)
        offset += len(c.Columns) * 8
        if len(c.Columns) > 128 { return nil, ssz.ErrListTooBig }
        for _, o := range c.Columns { dst = binary.LittleEndian.AppendUint64(dst, o) }
        return dst, err
    }

`ssz.WriteOffset`와 `AppendUint64`는 인라인되었다.
그래서 `append` 자리 셋이 각각 `runtime.growslice`를 부를 수 있다.

## 5. 피호출자와 계약 인스턴스

| 지시어 | 대상 | 경로 | 분류 | 인스턴스 |
| --- | --- | --- | --- | --- |
| 23 | `runtime.growslice` | `append(dst, BlockRoot...)`, 용량 부족 | (b) | `GrowsliceC Heap e2eU8Type_addr 1 S`, num 32 |
| 36 | `runtime.memmove` | BlockRoot 32바이트 복사 | (b) | `MemmoveC S`, n = 32 |
| 49 | `runtime.growslice` | `WriteOffset`, 용량 부족 | (b) | 같은 꼴, num 4 |
| 94 | `runtime.growslice` | 루프의 `AppendUint64`, 용량 부족 | (b) | 같은 꼴, num 8 |
| 112 | `runtime.morestack_noctxt.abi0` | 스택 부족 | (c) | 전제 `guard + 8 < rsp` |

- 세 growslice 자리의 형식 단어는 모두 `type__+387072`(uint8)다. `enclink.py data`가 확인한다.
- 그 단어는 Checkpoint 인코더의 형식 단어(`E2e.Data.e2eU8Type_addr`)와 같다.
- 원소 크기는 모두 1이다. 모델된 esz 1(`rt_growslice`)과 같다. 새 모델이 필요 없다.
- `fmt.errorf`, `newobject`, `panicBounds`, 쓰기 장벽 호출은 없다.
- 지시어 번호는 정규화 `.S`의 줄 번호에서 1을 뺀 값이다.

## 6. 경로 (목표)

| 경로 | 조건 | 목표 |
| --- | --- | --- |
| F 용량 충분 | `len + 36 + 8n ≤ cap` | K |
| G 첫 자리에서 늘림 | `cap < len + 32`, 새 용량이 나머지를 담는다 | K |
| G* 임의 자리에서 늘림 | 그 밖의 용량 경우 | 목표 밖. N으로 적는다 |
| RB 길이 거부 | `len(BlockRoot) ≠ 32` | K |
| RT 초과 거부 | `len(Columns) > 128`, 처음 두 자리는 용량 충분 | K |
| morestack | 스택 부족 | N, 전제가 막는다 |

## 7. 합성 (의무 7)

이 타입의 디코더 수용 명세는 레포에 없다.
그래서 디코드 뒤 인코드의 합성은 N이다.

## 8. 한계

- 이 표는 선정이다. 증명 가능성을 말하지 않는다.
- 호스트는 darwin/arm64다. x86-64 기계어를 실행하지 않았다.
