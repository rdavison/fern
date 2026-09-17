module

/-!
# Packed 32-bit tables

A `ByteArray` holding little-endian `UInt32` cells, built by appending in index order. This is
executable code for the exact same-finger bigram solver. It imports no Mathlib, so the trusted
runtime code stays small, and every definition is proved correct in `Fern.Solver.Proof.Table`.
-/

@[expose] public section

namespace FernImpl

/-- Append one little-endian `UInt32` cell. -/
@[inline] def push32 (t : ByteArray) (v : UInt32) : ByteArray :=
  (((t.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

/-- Read cell `i`. -/
@[inline] def get32 (t : @& ByteArray) (i : Nat) : UInt32 :=
  (t.get! (4 * i)).toUInt32 + ((t.get! (4 * i + 1)).toUInt32 <<< 8) +
    ((t.get! (4 * i + 2)).toUInt32 <<< 16) + ((t.get! (4 * i + 3)).toUInt32 <<< 24)

/-- Append `fuel` cells, computing cell `i` from the table built so far. -/
@[specialize] def tabulate32Aux (f : ByteArray → Nat → UInt32) : Nat → Nat → ByteArray → ByteArray
  | 0, _, t => t
  | fuel + 1, i, t => tabulate32Aux f fuel (i + 1) (push32 t (f t i))

/-- A table of `n` cells, each computed from the cells before it. -/
@[inline] def tabulate32 (n : Nat) (f : ByteArray → Nat → UInt32) : ByteArray :=
  tabulate32Aux f n 0 (ByteArray.emptyWithCapacity (4 * n))

/-- Append `fuel` bytes, computing byte `i` from its index. -/
def mkBytesAux (f : Nat → UInt8) : Nat → Nat → ByteArray → ByteArray
  | 0, _, t => t
  | fuel + 1, i, t => mkBytesAux f fuel (i + 1) (t.push (f i))

/-- A byte table of `n` entries. -/
def mkBytes (n : Nat) (f : Nat → UInt8) : ByteArray :=
  mkBytesAux f n 0 (ByteArray.emptyWithCapacity n)

end FernImpl
