# SCOPE-P6: X5를 위한 잠정 분류 (phase1c P6)

**잠정이다.** 증명을 시도하지 않았다. 이 표는 증명 가능성을 말하지 않는다. `gen/scope6.py`가 JSON에서 만든다.

실패 이유 종류(먼저 걸리는 순서): 도구 빈틈(`%riz`) > 계약 부재 > 새 패턴(자동화) > 알려진 것 없음.
"피호출 포함"은 타입과 그 생성 피호출자 폐포 중 가장 먼저 걸리는 종류다. 타입 혼자 "알려진 것 없음"이어도 피호출자가 막으면 막힌다.
Prysm 타입 135개 중 123개는 protobuf 구조체다. 손 사례의 축약 타입과 Go 배치가 다르다(`ir/*.json` `go_fields`).
생성기 결함은 종류에 있지만 출력 코드 결함이 알려지지 않아 해당 타입이 없다.
손 사례의 가장 큰 함수는 명령어 395개다. 크기 띠는 그 기준이다(시간을 외삽하지 않는다).

## 1. 수치

| 항목 | 값 |
| --- | --- |
| `first_class` | {"missing contract": 61, "new pattern (automation)": 23, "none known": 38, "tool gap": 13} |
| `first_class_transitive` | {"missing contract": 77, "new pattern (automation)": 8, "none known": 8, "tool gap": 42} |
| `first_class_transitive_in_B` | {"missing contract": 28, "new pattern (automation)": 2, "none known": 6, "tool gap": 9} |
| `first_class_p1_in_only` | {"missing contract": 58, "new pattern (automation)": 23, "none known": 38, "tool gap": 13} |
| `has_class` | {"tool gap": 13, "missing contract": 74, "new pattern (automation)": 91, "none known": 38} |
| `size_band` | {"over 3x hand max": 17, "up to 3x hand max": 23, "within hand range": 95} |
| `missing_contract_kinds` | {"fmt shape '%d%d'": 15, "fmt shape '%d'": 15, "hand-written primitives SSZ methods (no spec)": 52, "runtime call moveSlice* (stack-backed result to heap)": 8} |
| `new_pattern_kinds` | {"byte list (BitL without ValidateBitlist)": 12, "hand-written delegate CommitteeIndex": 2, "hand-written delegate Epoch": 10, "hand-written delegate Gwei": 2, "hand-written delegate Slot": 38, "hand-written delegate ValidatorIndex": 28, "list of byte lists (deep)": 3, "list of fixed byte vectors": 22, "list of fixed-size containers": 21, "vector of byte slices": 27, "vector of hand-written delegates": 1} |
| `p1_in_split` | {"types": 132, "calls_hand_written": 52, "bitlist_via_contract": 5, "list_container": 20, "list_container_variable_elements_ListC": 12, "list_container_fixed_elements_new": 19, "vector_of_container_forms": 1, "vector_of_byte_slices": 27, "three_functions_parse": 119, "some_function_does_not_parse": 13} |
| `in_B_first_class` | {"missing contract": 20, "new pattern (automation)": 7, "none known": 15, "tool gap": 3} |

## 2. 타입 표

| 타입 | B | P1 범위 | 첫 실패 종류 | 피호출 포함 첫 종류 | 모든 종류 | 손 패턴 | 새 패턴 | 없는 계약 | 파서 M/S/U | 최대 명령어 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `BeaconBlockBody` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1505 |
| `BeaconBlockBodyAltair` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1554 |
| `BeaconBlockBodyBellatrix` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1629 |
| `BeaconBlockBodyCapella` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1832 |
| `BeaconBlockBodyDeneb` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed byte vectors, list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 2014 |
| `BeaconBlockBodyElectra` | B | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed byte vectors, list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 2023 |
| `BeaconState` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListC, ListU64, Scalars | hand-written delegate Slot, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | fmt shape '%d%d', fmt shape '%d', hand-written primitives SSZ methods (no spec) | ERR/OK/OK | 2099 |
| `BeaconStateElectra` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Nested.L, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Epoch, hand-written delegate Gwei, hand-written delegate Slot, hand-written delegate ValidatorIndex, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | hand-written primitives SSZ methods (no spec) | ERR/OK/OK | 2806 |
| `BeaconStateFulu` | B | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Nested.L, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Epoch, hand-written delegate Gwei, hand-written delegate Slot, hand-written delegate ValidatorIndex, list of fixed byte vectors, list of fixed-size containers, vector of byte slices, vector of hand-written delegates | hand-written primitives SSZ methods (no spec) | ERR/OK/OK | 2890 |
| `BlindedBeaconBlockBodyBellatrix` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1629 |
| `BlindedBeaconBlockBodyCapella` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 1832 |
| `BlindedBeaconBlockBodyDeneb` |  | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed byte vectors, list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 2014 |
| `BlindedBeaconBlockBodyElectra` | B | in | tool gap | tool gap | tool gap, missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root, ListC, Nested.L | list of fixed byte vectors, list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | ERR/OK/OK | 2023 |
| `AggregateAttestationAndProof` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 164 |
| `AggregateAttestationAndProofElectra` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 164 |
| `AttestationData` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root | hand-written delegate CommitteeIndex, hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 220 |
| `BLSToExecutionChange` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 130 |
| `BeaconBlock` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockAltair` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockBellatrix` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockCapella` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockDeneb` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockElectra` | B | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BeaconBlockHeader` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 198 |
| `BeaconStateAltair` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Slot, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 1746 |
| `BeaconStateBellatrix` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Nested.L, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Slot, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 1818 |
| `BeaconStateCapella` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Nested.L, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Slot, hand-written delegate ValidatorIndex, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 2066 |
| `BeaconStateDeneb` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, BitVec, Checkpoint.root, FixedVec.W, ListU64, Nested.L, Scalars | byte list (BitL without ValidateBitlist), hand-written delegate Slot, hand-written delegate ValidatorIndex, list of fixed byte vectors, list of fixed-size containers, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 2066 |
| `BlindedBeaconBlockBellatrix` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BlindedBeaconBlockCapella` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BlindedBeaconBlockDeneb` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BlindedBeaconBlockElectra` |  | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `BlindedBeaconBlockFulu` | B | in | missing contract | tool gap | missing contract, new pattern (automation) | Checkpoint.root, Nested.L | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 228 |
| `Checkpoint` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Epoch | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 98 |
| `ConsolidationRequest` | B | in | missing contract | missing contract | missing contract | Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 139 |
| `ContributionAndProof` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 142 |
| `ENRForkID` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Epoch | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 116 |
| `ExecutionPayload` |  | out | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist), list of byte lists (deep) | fmt shape '%d%d', fmt shape '%d' | OK/OK/OK | 714 |
| `ExecutionPayloadCapella` |  | out | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist), list of byte lists (deep), list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | OK/OK/OK | 919 |
| `ExecutionPayloadDeneb` | B | out | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist), list of byte lists (deep), list of fixed-size containers | fmt shape '%d%d', fmt shape '%d' | OK/OK/OK | 924 |
| `Fork` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Epoch | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 116 |
| `ForkData` |  | in | missing contract | missing contract | missing contract | Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 102 |
| `HistoricalBatch` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | - | vector of byte slices | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 164 |
| `HistoricalSummary` | B | in | missing contract | missing contract | missing contract | Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 105 |
| `LightClientFinalityUpdateAltair` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 344 |
| `LightClientFinalityUpdateCapella` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 432 |
| `LightClientFinalityUpdateDeneb` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 432 |
| `LightClientFinalityUpdateElectra` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 432 |
| `LightClientOptimisticUpdateAltair` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 227 |
| `LightClientOptimisticUpdateCapella` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 268 |
| `LightClientOptimisticUpdateDeneb` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 268 |
| `LightClientUpdateAltair` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 543 |
| `LightClientUpdateCapella` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 641 |
| `LightClientUpdateDeneb` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 641 |
| `LightClientUpdateElectra` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Nested.L | hand-written delegate Slot, vector of byte slices | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 641 |
| `PartialDataColumnSidecar` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | BitL, ListC | list of fixed byte vectors | fmt shape '%d%d', fmt shape '%d' | OK/OK/OK | 771 |
| `PendingAttestation` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, BitL | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 233 |
| `PendingConsolidation` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | - | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 97 |
| `PendingDeposit` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 168 |
| `PendingPartialWithdrawal` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Scalars | hand-written delegate Epoch, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 99 |
| `PowBlock` |  | in | missing contract | missing contract | missing contract | Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 140 |
| `SigningData` |  | in | missing contract | missing contract | missing contract | Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 106 |
| `SingleAttestation` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | AttestationData.source, Checkpoint.root | hand-written delegate CommitteeIndex, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 180 |
| `Status` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Epoch, hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 192 |
| `StatusV2` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Epoch, hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 227 |
| `SyncAggregate` | B | in | missing contract | missing contract | missing contract | BitVec, Checkpoint.root | - | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 105 |
| `SyncAggregatorSelectionData` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Scalars | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 67 |
| `SyncCommittee` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | vector of byte slices | runtime call moveSlice* (stack-backed result to heap) | OK/OK/OK | 133 |
| `SyncCommitteeContribution` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | BitVec, Checkpoint.root, Scalars | hand-written delegate Slot | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 162 |
| `SyncCommitteeMessage` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root | hand-written delegate Slot, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 163 |
| `Validator` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | hand-written delegate Epoch | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 249 |
| `ValidatorBalance` |  | in | missing contract | missing contract | missing contract, new pattern (automation) | Scalars | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 67 |
| `VoluntaryExit` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | - | hand-written delegate Epoch, hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 97 |
| `Withdrawal` | B | in | missing contract | missing contract | missing contract, new pattern (automation) | Checkpoint.root, Scalars | hand-written delegate ValidatorIndex | hand-written primitives SSZ methods (no spec) | OK/OK/OK | 117 |
| `BeaconBlockContentsDeneb` |  | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `BeaconBlockContentsElectra` |  | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `BeaconBlockContentsFulu` | B | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `BlobSidecar` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Checkpoint.root, Scalars | vector of byte slices | - | OK/OK/OK | 255 |
| `BlobSidecars` |  | in | new pattern (automation) | missing contract | new pattern (automation) | - | list of fixed-size containers | - | OK/OK/OK | 229 |
| `BuilderBidDeneb` |  | in | new pattern (automation) | new pattern (automation) | new pattern (automation) | Checkpoint.root, Nested.L | list of fixed byte vectors | - | OK/OK/OK | 341 |
| `BuilderBidElectra` |  | in | new pattern (automation) | missing contract | new pattern (automation) | Checkpoint.root, Nested.L | list of fixed byte vectors | - | OK/OK/OK | 406 |
| `DataColumnSidecar` | B | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Scalars | list of fixed byte vectors, vector of byte slices | - | OK/OK/OK | 667 |
| `Deposit` | B | in | new pattern (automation) | new pattern (automation) | new pattern (automation) | AttestationData.source | vector of byte slices | - | OK/OK/OK | 257 |
| `ExecutionPayloadHeader` |  | in | new pattern (automation) | new pattern (automation) | new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist) | - | OK/OK/OK | 432 |
| `ExecutionPayloadHeaderCapella` |  | in | new pattern (automation) | new pattern (automation) | new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist) | - | OK/OK/OK | 465 |
| `ExecutionPayloadHeaderDeneb` | B | in | new pattern (automation) | new pattern (automation) | new pattern (automation) | Checkpoint.root, Scalars | byte list (BitL without ValidateBitlist) | - | OK/OK/OK | 491 |
| `ExecutionRequests` | B | in | new pattern (automation) | missing contract | new pattern (automation) | - | list of fixed-size containers | - | OK/OK/OK | 677 |
| `LightClientBootstrapAltair` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source | vector of byte slices | - | OK/OK/OK | 287 |
| `LightClientBootstrapCapella` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Nested.L | vector of byte slices | - | OK/OK/OK | 327 |
| `LightClientBootstrapDeneb` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Nested.L | vector of byte slices | - | OK/OK/OK | 327 |
| `LightClientBootstrapElectra` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Nested.L | vector of byte slices | - | OK/OK/OK | 327 |
| `LightClientHeaderCapella` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Nested.L | vector of byte slices | - | OK/OK/OK | 208 |
| `LightClientHeaderDeneb` |  | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source, Nested.L | vector of byte slices | - | OK/OK/OK | 208 |
| `PartialDataColumnHeader` | B | in | new pattern (automation) | missing contract | new pattern (automation) | AttestationData.source | list of fixed byte vectors, vector of byte slices | - | OK/OK/OK | 316 |
| `SignedBeaconBlockContentsDeneb` |  | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `SignedBeaconBlockContentsElectra` |  | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `SignedBeaconBlockContentsFulu` | B | in | new pattern (automation) | tool gap | new pattern (automation) | Nested.L | list of fixed byte vectors | - | OK/OK/OK | 444 |
| `Attestation` |  | in | none known | missing contract | none known | AttestationData.source, BitL, Checkpoint.root | - | - | OK/OK/OK | 198 |
| `AttestationElectra` | B | in | none known | missing contract | none known | AttestationData.source, BitL, BitVec, Checkpoint.root | - | - | OK/OK/OK | 234 |
| `AttesterSlashing` |  | in | none known | missing contract | none known | Nested.L | - | - | OK/OK/OK | 177 |
| `AttesterSlashingElectra` | B | in | none known | missing contract | none known | Nested.L | - | - | OK/OK/OK | 177 |
| `BlobIdentifier` |  | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 72 |
| `BuilderBidCapella` |  | in | none known | new pattern (automation) | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 168 |
| `DataColumnsByRootIdentifier` | B | in | none known | none known | none known | Checkpoint.root, ListU64 | - | - | OK/OK/OK | 208 |
| `DepositMessage` |  | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 107 |
| `DepositRequest` | B | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 160 |
| `Deposit_Data` | B | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 144 |
| `Eth1Data` | B | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 110 |
| `IndexedAttestation` |  | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root, ListU64 | - | - | OK/OK/OK | 253 |
| `IndexedAttestationElectra` | B | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root, ListU64 | - | - | OK/OK/OK | 253 |
| `LightClientHeaderAltair` |  | in | none known | missing contract | none known | AttestationData.source | - | - | OK/OK/OK | 77 |
| `PartialDataColumnPartsMetadata` | B | in | none known | none known | none known | BitL | - | - | OK/OK/OK | 211 |
| `ProposerSlashing` | B | in | none known | missing contract | none known | AttestationData.source | - | - | OK/OK/OK | 136 |
| `SignedAggregateAttestationAndProof` |  | in | none known | missing contract | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 158 |
| `SignedAggregateAttestationAndProofElectra` |  | in | none known | missing contract | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 158 |
| `SignedBLSToExecutionChange` | B | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root | - | - | OK/OK/OK | 115 |
| `SignedBeaconBlock` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockAltair` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockBellatrix` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockCapella` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockDeneb` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockElectra` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockFulu` | B | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBeaconBlockHeader` | B | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root | - | - | OK/OK/OK | 115 |
| `SignedBlindedBeaconBlockBellatrix` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBlindedBeaconBlockCapella` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBlindedBeaconBlockDeneb` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBlindedBeaconBlockElectra` |  | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBlindedBeaconBlockFulu` | B | in | none known | tool gap | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 153 |
| `SignedBuilderBidCapella` |  | in | none known | new pattern (automation) | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 158 |
| `SignedBuilderBidDeneb` |  | in | none known | new pattern (automation) | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 158 |
| `SignedBuilderBidElectra` |  | in | none known | missing contract | none known | Checkpoint.root, Nested.L | - | - | OK/OK/OK | 138 |
| `SignedContributionAndProof` |  | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root | - | - | OK/OK/OK | 115 |
| `SignedVoluntaryExit` | B | in | none known | missing contract | none known | AttestationData.source, Checkpoint.root | - | - | OK/OK/OK | 115 |
| `WithdrawalRequest` | B | in | none known | none known | none known | Checkpoint.root, Scalars | - | - | OK/OK/OK | 107 |
