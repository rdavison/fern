module
public import FernImpl.Table

/-!
# Bit operations on 30-bit key masks

A set of keys is a `UInt64` whose bit `i` records key `i`. The highest set bit and the number of
set bits come from 15-bit lookup tables, which the spike measured as 25% faster than
`UInt64.log2`. `foldBits` visits the set bits from highest to lowest. Everything is proved correct
in `Fern.Solver.Proof.Bits`.
-/

@[expose] public section

namespace FernImpl

/-- The mask with only bit `i` set. -/
@[inline] def bit (i : UInt64) : UInt64 := (1 : UInt64) <<< i

/-- Number of set bits among the lowest `fuel` bits of `i`. -/
def natPop : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, i => i % 2 + natPop fuel (i / 2)

/-- Highest set bit of each 15-bit value. -/
def hibTable : ByteArray := mkBytes (2 ^ 15) fun i => (Nat.log2 i).toUInt8

/-- Number of set bits of each 15-bit value. -/
def popTable : ByteArray := mkBytes (2 ^ 15) fun i => (natPop 15 i).toUInt8

/-- Highest set bit of a 30-bit mask. -/
@[inline] def hibit (m : UInt64) : UInt64 :=
  if m >>> 15 == 0 then (hibTable.get! m.toNat).toUInt64
  else (15 : UInt64) + (hibTable.get! (m >>> 15).toNat).toUInt64

/-- Number of set bits of a 30-bit mask. -/
@[inline] def pop30 (m : UInt64) : UInt64 :=
  (popTable.get! (m &&& 0x7FFF).toNat).toUInt64 + (popTable.get! (m >>> 15).toNat).toUInt64

/-- Fold over the set bits of `r`, highest first. `fuel` must be at least the number of set bits. -/
@[specialize] def foldBits {β : Type} (f : β → UInt64 → β) : Nat → UInt64 → β → β
  | 0, _, acc => acc
  | fuel + 1, r, acc =>
    if r == 0 then acc
    else
      let b := hibit r
      foldBits f fuel (r ^^^ bit b) (f acc b)

end FernImpl
