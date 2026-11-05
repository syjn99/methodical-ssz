// Package prysm holds the SSZ fields of two Prysm types, copied from
// github.com/OffchainLabs/prysm v7.1.8 (commit 51b5a75ebbadf05af22bd2601b5baf7a9e99b66d),
// proto/prysm/v1alpha1/attestation.pb.go. The field names, Go kinds and ssz
// tags are as in Prysm. The protobuf runtime fields (state, unknownFields,
// sizeCache) and the cast types of the primitives are not copied: this module
// has no protobuf or Prysm dependency (go.mod is outside fv/kraken). So the Go
// struct layout differs from Prysm's (field offsets); the SSZ schema is the same.
package prysm

// Slot, Epoch and CommitteeIndex are uint64 in Prysm (consensus-types/primitives).
type (
	Slot           uint64
	Epoch          uint64
	CommitteeIndex uint64
)

type Checkpoint struct {
	Epoch Epoch
	Root  []byte `ssz-size:"32"`
}

type AttestationData struct {
	Slot            Slot
	CommitteeIndex  CommitteeIndex
	BeaconBlockRoot []byte `ssz-size:"32"`
	Source          *Checkpoint
	Target          *Checkpoint
}
