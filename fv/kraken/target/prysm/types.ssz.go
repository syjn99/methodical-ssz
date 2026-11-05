package prysm

import (
	binary "encoding/binary"
	"fmt"
	ssz "github.com/OffchainLabs/methodical-ssz/ssz"
)

func (c *Checkpoint) SizeSSZ() int {
	size := 40

	return size
}

func (c *Checkpoint) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *Checkpoint) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error

	// Field 0: Epoch
	dst = binary.LittleEndian.AppendUint64(dst, uint64(c.Epoch))

	// Field 1: Root
	if len(c.Root) != 32 {
		return nil, ssz.ErrBytesLength
	}
	dst = append(dst, c.Root...)

	return dst, err
}

func (c *Checkpoint) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size != 40 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:8]  // c.Epoch
	sszSlice1 := buf[8:40] // c.Root

	// Field 0: Epoch
	c.Epoch = Epoch(binary.LittleEndian.Uint64(sszSlice0))

	// Field 1: Root
	c.Root = make([]byte, 0, 32)
	c.Root = append(c.Root, sszSlice1...)
	return err
}

func (c *Checkpoint) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *Checkpoint) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: Epoch
	hh.PutUint64(uint64(c.Epoch))
	// Field 1: Root
	if len(c.Root) != 32 {
		return ssz.ErrBytesLength
	}
	hh.PutBytes(c.Root)
	hh.Merkleize(indx)
	return nil
}

func (c *AttestationData) SizeSSZ() int {
	size := 128

	return size
}

func (c *AttestationData) MarshalSSZ() ([]byte, error) {
	buf := make([]byte, c.SizeSSZ())
	return c.MarshalSSZTo(buf[:0])
}

func (c *AttestationData) MarshalSSZTo(dst []byte) ([]byte, error) {
	var err error

	// Field 0: Slot
	dst = binary.LittleEndian.AppendUint64(dst, uint64(c.Slot))

	// Field 1: CommitteeIndex
	dst = binary.LittleEndian.AppendUint64(dst, uint64(c.CommitteeIndex))

	// Field 2: BeaconBlockRoot
	if len(c.BeaconBlockRoot) != 32 {
		return nil, ssz.ErrBytesLength
	}
	dst = append(dst, c.BeaconBlockRoot...)

	// Field 3: Source
	if c.Source == nil {
		c.Source = new(Checkpoint)
	}
	if dst, err = c.Source.MarshalSSZTo(dst); err != nil {
		return nil, fmt.Errorf("Source: %w", err)
	}

	// Field 4: Target
	if c.Target == nil {
		c.Target = new(Checkpoint)
	}
	if dst, err = c.Target.MarshalSSZTo(dst); err != nil {
		return nil, fmt.Errorf("Target: %w", err)
	}

	return dst, err
}

func (c *AttestationData) UnmarshalSSZ(buf []byte) error {
	var err error
	size := uint64(len(buf))
	if size != 128 {
		return ssz.ErrSize
	}

	sszSlice0 := buf[0:8]    // c.Slot
	sszSlice1 := buf[8:16]   // c.CommitteeIndex
	sszSlice2 := buf[16:48]  // c.BeaconBlockRoot
	sszSlice3 := buf[48:88]  // c.Source
	sszSlice4 := buf[88:128] // c.Target

	// Field 0: Slot
	c.Slot = Slot(binary.LittleEndian.Uint64(sszSlice0))

	// Field 1: CommitteeIndex
	c.CommitteeIndex = CommitteeIndex(binary.LittleEndian.Uint64(sszSlice1))

	// Field 2: BeaconBlockRoot
	c.BeaconBlockRoot = make([]byte, 0, 32)
	c.BeaconBlockRoot = append(c.BeaconBlockRoot, sszSlice2...)

	// Field 3: Source
	c.Source = new(Checkpoint)
	if err = c.Source.UnmarshalSSZ(sszSlice3); err != nil {
		return fmt.Errorf("Source: %w", err)
	}

	// Field 4: Target
	c.Target = new(Checkpoint)
	if err = c.Target.UnmarshalSSZ(sszSlice4); err != nil {
		return fmt.Errorf("Target: %w", err)
	}
	return err
}

func (c *AttestationData) HashTreeRoot() ([32]byte, error) {
	hh := ssz.DefaultHasherPool.Get()
	if err := c.HashTreeRootWith(hh); err != nil {
		ssz.DefaultHasherPool.Put(hh)
		return [32]byte{}, err
	}
	root, err := hh.HashRoot()
	ssz.DefaultHasherPool.Put(hh)
	return root, err
}

func (c *AttestationData) HashTreeRootWith(hh *ssz.Hasher) (err error) {
	indx := hh.Index()
	// Field 0: Slot
	hh.PutUint64(uint64(c.Slot))
	// Field 1: CommitteeIndex
	hh.PutUint64(uint64(c.CommitteeIndex))
	// Field 2: BeaconBlockRoot
	if len(c.BeaconBlockRoot) != 32 {
		return ssz.ErrBytesLength
	}
	hh.PutBytes(c.BeaconBlockRoot)
	// Field 3: Source
	if err := c.Source.HashTreeRootWith(hh); err != nil {
		return fmt.Errorf("Source: %w", err)
	}
	// Field 4: Target
	if err := c.Target.HashTreeRootWith(hh); err != nil {
		return fmt.Errorf("Target: %w", err)
	}
	hh.Merkleize(indx)
	return nil
}
