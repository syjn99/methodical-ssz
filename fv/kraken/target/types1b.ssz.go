package target

import (
	binary "encoding/binary"
	"fmt"
	go_bitfield "github.com/OffchainLabs/go-bitfield"
	ssz "github.com/OffchainLabs/methodical-ssz/ssz"
)

func (c *BitVec) SizeSSZ() int {
	size := 1

	return size
}

func (c *BitVec) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *BitVec) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error

	// Field 0: J
	if err = ssz.ValidateBitvector(c.J, 4); err != nil {
		return nil, fmt.Errorf("J: %w", err)
	}
	if len([]byte(c.J)) != 1 {
		return nil, ssz.ErrBytesLength
	}
	dst = append(dst, []byte(c.J)...)

	return dst, err
}

func (c *BitVec) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size != 1 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:1] // c.J

	// Field 0: J
	if err = ssz.ValidateBitvector(sszSlice0, 4); err != nil {
		return fmt.Errorf("J: %w", err)
	}
	c.J = make([]byte, 0, 1)
	c.J = append(c.J, go_bitfield.Bitvector4(sszSlice0)...)
	return err
}

func (c *BitVec) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *BitVec) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: J
	if len([]byte(c.J)) != 1 {
		return ssz.ErrBytesLength
	}
	hh.PutBytes([]byte(c.J))
	hh.Merkleize(indx)
	return nil
}

func (c *Nested) SizeSSZ() int {
	size := 28
	if c.L == nil {
		c.L = new(ListU64)
	}
	size += c.L.SizeSSZ()
	return size
}

func (c *Nested) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *Nested) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error
	offset := 28

	// Field 0: A
	dst = binary.LittleEndian.AppendUint64(dst, c.A)

	// Field 1: S
	if c.S == nil {
		c.S = new(Scalars)
	}
	if dst, err = c.S.MarshalSSZTo(dst); err != nil {
		return nil, fmt.Errorf("S: %w", err)
	}

	// Field 2: L
	if c.L == nil {
		c.L = new(ListU64)
	}
	dst = ssz.WriteOffset(dst, offset)
	offset += c.L.SizeSSZ()

	// Field 2: L
	if dst, err = c.L.MarshalSSZTo(dst); err != nil {
		return nil, fmt.Errorf("L: %w", err)
	}
	return dst, err
}

func (c *Nested) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size < 28 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:8]  // c.A
	sszSlice1 := buf[8:24] // c.S

	sszVarOffset2 := ssz.ReadOffset(buf[24:28]) // c.L
	if sszVarOffset2 != 28 {
		return ssz.ErrInvalidVariableOffset
	}
	sszSlice2 := buf[sszVarOffset2:] // c.L

	// Field 0: A
	c.A = binary.LittleEndian.Uint64(sszSlice0)

	// Field 1: S
	c.S = new(Scalars)
	if err = c.S.UnmarshalSSZ(sszSlice1); err != nil {
		return fmt.Errorf("S: %w", err)
	}

	// Field 2: L
	c.L = new(ListU64)
	if err = c.L.UnmarshalSSZ(sszSlice2); err != nil {
		return fmt.Errorf("L: %w", err)
	}
	return err
}

func (c *Nested) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *Nested) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: A
	hh.PutUint64(c.A)
	// Field 1: S
	if err := c.S.HashTreeRootWith(hh); err != nil {
		return fmt.Errorf("S: %w", err)
	}
	// Field 2: L
	if err := c.L.HashTreeRootWith(hh); err != nil {
		return fmt.Errorf("L: %w", err)
	}
	hh.Merkleize(indx)
	return nil
}

func (c *ListC) SizeSSZ() int {
	size := 4
	for _, o := range c.Items {
		size += 4
		size += o.SizeSSZ()
	}
	return size
}

func (c *ListC) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *ListC) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error
	offset := 4

	// Field 0: Items
	dst = ssz.WriteOffset(dst, offset)
	for _, o := range c.Items {
		offset += 4
		offset += o.SizeSSZ()
	}

	// Field 0: Items
	if len(c.Items) > 4 {
		return nil, ssz.ErrListTooBig
	}
	{
		offset = 4 * len(c.Items)
		for _, o := range c.Items {
			dst = ssz.WriteOffset(dst, offset)
			offset += o.SizeSSZ()
		}
	}
	for _, o := range c.Items {
		if dst, err = o.MarshalSSZTo(dst); err != nil {
			return nil, fmt.Errorf("Items: %w", err)
		}
	}
	return dst, err
}

func (c *ListC) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size < 4 {
		return ssz.ErrSize
	}

	sszVarOffset0 := ssz.ReadOffset(buf[0:4]) // c.Items
	if sszVarOffset0 != 4 {
		return ssz.ErrInvalidVariableOffset
	}
	sszSlice0 := buf[sszVarOffset0:] // c.Items

	// Field 0: Items
	{
		// empty lists are zero length, so make sure there is room for an offset
		// before attempting to unmarshal it
		if len(sszSlice0) > 3 {
			startOffset := ssz.ReadOffset(sszSlice0[0:4])
			if startOffset == 0 {
				return fmt.Errorf("encountered invalid offset of 0 when decoding c.Items")
			}
			if startOffset%4 != 0 {
				return fmt.Errorf("misaligned list bytes: when decoding c.Items, end-of-list offset is %d, which is not a multiple of 4 (offset size)", startOffset)
			}
			listLen := startOffset / 4
			if listLen > 4 {
				return fmt.Errorf("ssz-max exceeded: c.Items has %d elements, ssz-max is 4: %w", listLen, ssz.ErrListTooBig)
			}
			totalVarBytes := uint64(len(sszSlice0))
			if totalVarBytes < startOffset {
				return fmt.Errorf("list bytes too short to contain an offset when decoding c.Items")
			}
			c.Items = make([]*ListU64, listLen)
			var tmpSlice []byte
			for i := uint64(0); i < listLen; i++ {
				var tmp *ListU64
				tmp = new(ListU64)
				endOffset := totalVarBytes
				if i+1 != listLen {
					endOffset = ssz.ReadOffset(sszSlice0[(i+1)*4 : (i+2)*4])
					if totalVarBytes < endOffset {
						return fmt.Errorf("offset %d points past the end of buffer when decoding c.Items", endOffset)
					}
				}
				if endOffset < startOffset {
					return fmt.Errorf("offset %d is not greater than start offset %d when decoding c.Items", endOffset, startOffset)
				}
				tmpSlice = sszSlice0[startOffset:endOffset]
				if err = tmp.UnmarshalSSZ(tmpSlice); err != nil {
					return fmt.Errorf("Items: %w", err)
				}
				c.Items[i] = tmp
				startOffset = endOffset
			}
		} else {
			if len(sszSlice0) > 0 {
				return fmt.Errorf("list bytes too short to contain an offset when decoding c.Items")
			}
			c.Items = make([]*ListU64, 0)
		}
	}
	return err
}

func (c *ListC) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *ListC) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: Items
	{
		if len(c.Items) > 4 {
			return ssz.ErrListTooBig
		}
		subIndx := hh.Index()
		for _, o := range c.Items {
			if err := o.HashTreeRootWith(hh); err != nil {
				return fmt.Errorf("Items: %w", err)
			}
		}
		hh.MerkleizeWithMixin(subIndx, uint64(len(c.Items)), 4)
	}
	hh.Merkleize(indx)
	return nil
}

func (c *BitL) SizeSSZ() int {
	size := 4
	size += len(c.B)
	return size
}

func (c *BitL) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *BitL) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error
	offset := 4

	// Field 0: B
	dst = ssz.WriteOffset(dst, offset)
	offset += len(c.B)

	// Field 0: B
	if err = ssz.ValidateBitlist(c.B, 2048); err != nil {
		return nil, fmt.Errorf("B: %w", err)
	}
	dst = append(dst, c.B...)
	return dst, err
}

func (c *BitL) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size < 4 {
		return ssz.ErrSize
	}

	sszVarOffset0 := ssz.ReadOffset(buf[0:4]) // c.B
	if sszVarOffset0 != 4 {
		return ssz.ErrInvalidVariableOffset
	}
	sszSlice0 := buf[sszVarOffset0:] // c.B

	// Field 0: B
	if err = ssz.ValidateBitlist(sszSlice0, 2048); err != nil {
		return fmt.Errorf("B: %w", err)
	}
	c.B = append([]byte{}, go_bitfield.Bitlist(sszSlice0)...)
	return err
}

func (c *BitL) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *BitL) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: B
	if len(c.B) == 0 {
		return ssz.ErrEmptyBitlist
	}
	hh.PutBitlist(c.B, 2048)
	hh.Merkleize(indx)
	return nil
}
