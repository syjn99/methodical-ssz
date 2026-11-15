package target

import bitfield "github.com/OffchainLabs/go-bitfield"

// BitVec is a fixed-size container with one Bitvector[4] (1 byte, 4 padding bits).
type BitVec struct {
	J bitfield.Bitvector4 `cast-type:"github.com/OffchainLabs/go-bitfield.Bitvector4" ssz-size:"1"`
}

// Nested is a variable-size container: a uint64, a fixed container inline, and a
// variable container behind an offset.
type Nested struct {
	A uint64
	S *Scalars
	L *ListU64
}

// ListC is List[ListU64, 4]: a list of variable-size containers (one offset per element).
type ListC struct {
	Items []*ListU64 `ssz-max:"4"`
}

// BitL is a container with one Bitlist[2048].
type BitL struct {
	B bitfield.Bitlist `cast-type:"github.com/OffchainLabs/go-bitfield.Bitlist" ssz-max:"2048"`
}
