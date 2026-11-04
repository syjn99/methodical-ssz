// Package target holds the phase 1a verification targets.
package target

// Scalars is a fixed-size container of the five scalar kinds. Size 16.
type Scalars struct {
	A uint8
	B uint16
	C uint32
	D uint64
	E bool
}

// FixedVec is a fixed-size container of two fixed vectors. Size 64.
type FixedVec struct {
	R [32]byte  `ssz-size:"32"`
	W []uint64 `ssz-size:"4"`
}

// ListU64 is a variable-size container with one List[uint64, 16] (one offset).
type ListU64 struct {
	L []uint64 `ssz-max:"16"`
}
