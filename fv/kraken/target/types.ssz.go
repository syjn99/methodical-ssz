package target

import (
	binary "encoding/binary"
	"fmt"
	ssz "github.com/OffchainLabs/methodical-ssz/ssz"
)

func (c *Scalars) SizeSSZ() int {
	size := 16

	return size
}

func (c *Scalars) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *Scalars) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error

	// Field 0: A
	dst = append(dst, c.A)

	// Field 1: B
	dst = binary.LittleEndian.AppendUint16(dst, c.B)

	// Field 2: C
	dst = binary.LittleEndian.AppendUint32(dst, c.C)

	// Field 3: D
	dst = binary.LittleEndian.AppendUint64(dst, c.D)

	// Field 4: E
	if c.E {
		dst = append(dst, 1)
	} else {
		dst = append(dst, 0)
	}

	return dst, err
}

func (c *Scalars) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size != 16 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:1]   // c.A
	sszSlice1 := buf[1:3]   // c.B
	sszSlice2 := buf[3:7]   // c.C
	sszSlice3 := buf[7:15]  // c.D
	sszSlice4 := buf[15:16] // c.E

	// Field 0: A
	c.A = sszSlice0[0]

	// Field 1: B
	c.B = binary.LittleEndian.Uint16(sszSlice1)

	// Field 2: C
	c.C = binary.LittleEndian.Uint32(sszSlice2)

	// Field 3: D
	c.D = binary.LittleEndian.Uint64(sszSlice3)

	// Field 4: E
	if sszSlice4[0] > 1 {
		return ssz.ErrInvalidSerialization
	}
	if sszSlice4[0] == 1 {
		c.E = true
	} else {
		c.E = false
	}
	return err
}

func (c *Scalars) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *Scalars) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: A
	hh.PutUint8(c.A)
	// Field 1: B
	hh.PutUint16(c.B)
	// Field 2: C
	hh.PutUint32(c.C)
	// Field 3: D
	hh.PutUint64(c.D)
	// Field 4: E
	hh.PutBool(c.E)
	hh.Merkleize(indx)
	return nil
}

func (c *FixedVec) SizeSSZ() int {
	size := 64

	return size
}

func (c *FixedVec) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *FixedVec) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error

	// Field 0: R
	if len(c.R) != 32 {
		return nil, ssz.ErrBytesLength
	}
	dst = append(dst, c.R[:]...)

	// Field 1: W
	if len(c.W) != 4 {
		return nil, ssz.ErrBytesLength
	}
	for _, o := range c.W {
		dst = binary.LittleEndian.AppendUint64(dst, o)
	}

	return dst, err
}

func (c *FixedVec) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size != 64 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:32]  // c.R
	sszSlice1 := buf[32:64] // c.W

	// Field 0: R
	copy(c.R[:], sszSlice0)

	// Field 1: W
	{
		c.W = make([]uint64, 4)
		for i := 0; i < 4; i++ {
			var tmp uint64

			tmpSlice := sszSlice1[i*8 : (1+i)*8]
			tmp = binary.LittleEndian.Uint64(tmpSlice)
			c.W[i] = tmp
		}
	}
	return err
}

func (c *FixedVec) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *FixedVec) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: R
	if len(c.R) != 32 {
		return ssz.ErrBytesLength
	}
	hh.PutBytes(c.R[:])
	// Field 1: W
	{
		if len(c.W) != 4 {
			return ssz.ErrVectorLength
		}
		subIndx := hh.Index()
		for _, o := range c.W {
			hh.AppendUint64(o)
		}
		hh.Merkleize(subIndx)
	}
	hh.Merkleize(indx)
	return nil
}

func (c *ListU64) SizeSSZ() int {
	size := 4
	size += len(c.L) * 8
	return size
}

func (c *ListU64) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *ListU64) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error
	offset := 4

	// Field 0: L
	dst = ssz.WriteOffset(dst, offset)
	offset += len(c.L) * 8

	// Field 0: L
	if len(c.L) > 16 {
		return nil, ssz.ErrListTooBig
	}
	for _, o := range c.L {
		dst = binary.LittleEndian.AppendUint64(dst, o)
	}
	return dst, err
}

func (c *ListU64) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size < 4 {
		return ssz.ErrSize
	}

	sszVarOffset0 := ssz.ReadOffset(buf[0:4]) // c.L
	if sszVarOffset0 != 4 {
		return ssz.ErrInvalidVariableOffset
	}
	if sszVarOffset0 > size {
		return ssz.ErrOffset
	}
	sszSlice0 := buf[sszVarOffset0:] // c.L

	// Field 0: L
	{
		if len(sszSlice0)%8 != 0 {
			return fmt.Errorf("misaligned bytes: c.L length is %d, which is not a multiple of 8: %w", len(sszSlice0), ssz.ErrIncorrectListSize)
		}
		numElem := len(sszSlice0) / 8
		if numElem > 16 {
			return fmt.Errorf("ssz-max exceeded: c.L has %d elements, ssz-max is 16: %w", numElem, ssz.ErrListTooBig)
		}
		c.L = make([]uint64, numElem)
		for i := 0; i < numElem; i++ {
			var tmp uint64

			tmpSlice := sszSlice0[i*8 : (1+i)*8]
			tmp = binary.LittleEndian.Uint64(tmpSlice)
			c.L[i] = tmp
		}
	}
	return err
}

func (c *ListU64) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *ListU64) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: L
	{
		if len(c.L) > 16 {
			return ssz.ErrListTooBig
		}
		subIndx := hh.Index()
		for _, o := range c.L {
			hh.AppendUint64(o)
		}
		hh.FillUpTo32()
		numItems := uint64(len(c.L))
		hh.MerkleizeWithMixin(subIndx, numItems, ssz.CalculateLimit(16, numItems, 8))
	}
	hh.Merkleize(indx)
	return nil
}
