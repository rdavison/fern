module
public import FernImpl.Bits

/-!
# The exact same-finger bigram search

The fast search that `Fern.Solver.Theorem` proves computes `Fern.Solver.optimumRef`: the least
same-finger weight over every layout of thirty keys.

`fill` tabulates, for every key set of size at most fifteen, its cheapest partition into triples.
For each twelve-key index set `S`, `indexCost` finds its cheapest split into two blocks of six, and
the eighteen remaining keys are costed with one more `step` against the table. `solve` scans every
index set, in parallel chunks, and returns the minimum.

Shapes follow the S0 spike: structural recursion on fuel, no `for`/`mut`, and a table built by
appending. Weights are counts of ordered bigrams, so a pair of keys weighs both directions.
-/

@[expose] public section

namespace FernImpl

set_option compiler.extract_closed false

/-- "No value yet": larger than any reachable cost. -/
def SENTINEL : UInt64 := (1 : UInt64) <<< 62

/-- All thirty keys. -/
def FULL : UInt64 := ((1 : UInt64) <<< 30) - 1

/-- The weight table: cell `30 * a + b` holds both directions of the pair `a`, `b`. -/
def swTable (cnt : Nat → Nat → Nat) : ByteArray :=
  tabulate32 900 fun _ k => (cnt (k / 30) (k % 30) + cnt (k % 30) (k / 30)).toUInt32

/-- Both directions of the pair `a`, `b`. -/
@[inline] def sw32 (sw : @& ByteArray) (a b : UInt64) : UInt64 :=
  (get32 sw (a.toNat * 30 + b.toNat)).toUInt64

/-- Cheapest partition of mask `m` into triples, reading smaller key sets from `t`. The highest key
is placed with each possible pair. -/
def step (sw t : @& ByteArray) (m : UInt64) : UInt64 :=
  let a := hibit m
  let r := m ^^^ bit a
  foldBits (fun acc b =>
    let rb := r &&& (bit b - 1)
    let r2 := r ^^^ bit b
    let wab := sw32 sw a b
    foldBits (fun acc c =>
      let v := wab + sw32 sw a c + sw32 sw b c + (get32 t (r2 ^^^ bit c).toNat).toUInt64
      if v < acc then v else acc) 30 rb acc) 30 r SENTINEL

/-- Whether mask `m` is tabulated: a nonempty key set of size three, six, nine, twelve or fifteen. -/
@[inline] def tabulated (m : UInt64) : Bool :=
  let p := pop30 m
  p != 0 && p % 3 == 0 && p ≤ 15

/-- The cheapest triple partition of every tabulated key set, indexed by mask. -/
def fill (sw : @& ByteArray) : ByteArray :=
  tabulate32 (2 ^ 30) fun t i =>
    let m := i.toUInt64
    if tabulated m then (step sw t m).toUInt32 else 0

/-- Both directions of every pair between key `x` and the keys of `A`. -/
def rowSum (sw : @& ByteArray) (x A : UInt64) : UInt64 :=
  foldBits (fun acc y => acc + sw32 sw x y) 30 A 0

/-- Cheapest way to distribute the keys of `rest` so that block `A` gains `nA` of them and block `C`
the other `nC`, where `wA` and `wC` are the blocks' current weights. -/
def splitMin (sw : @& ByteArray) :
    Nat → UInt64 → UInt64 → UInt64 → Nat → UInt64 → UInt64 → Nat → UInt64
  | 0, _, _, wA, _, _, wC, _ => wA + wC
  | fuel + 1, rest, A, wA, nA, C, wC, nC =>
    if rest == 0 then wA + wC
    else
      let x := hibit rest
      let rest' := rest ^^^ bit x
      let viaA := match nA with
        | 0 => SENTINEL
        | nA' + 1 => splitMin sw fuel rest' (A ||| bit x) (wA + rowSum sw x A) nA' C wC nC
      let viaC := match nC with
        | 0 => SENTINEL
        | nC' + 1 => splitMin sw fuel rest' A wA nA (C ||| bit x) (wC + rowSum sw x C) nC'
      if viaA < viaC then viaA else viaC

/-- Cheapest split of the twelve index keys `S` into two blocks of six. The highest key starts
block `A`. -/
@[inline] def indexCost (sw : @& ByteArray) (S : UInt64) : UInt64 :=
  let a := hibit S
  splitMin sw 11 (S ^^^ bit a) (bit a) 0 5 0 0 6

/-- Fold `f` over the masks `m, m + 1, …, m + fuel - 1`. -/
@[specialize] def scanWith (f : UInt64 → UInt64 → UInt64) : Nat → UInt64 → UInt64 → UInt64
  | 0, _, acc => acc
  | fuel + 1, m, acc => scanWith f fuel (m + 1) (f m acc)

/-- Keep the cheaper of `best` and the total for mask `m`, when `m` holds exactly twelve keys. -/
@[inline] def scanStep (sw t : @& ByteArray) (m best : UInt64) : UInt64 :=
  if pop30 m == 12 then
    let v := indexCost sw m + step sw t (FULL ^^^ m)
    if v < best then v else best
  else best

/-- The best total over the masks in `[m, m + fuel)` that hold exactly twelve keys. The loop is
generic in its step: with the table lookups inside a recursive definition, the kernel cannot check
its unfolding lemmas. -/
def scanRange (sw t : @& ByteArray) (fuel : Nat) (m best : UInt64) : UInt64 :=
  scanWith (scanStep sw t) fuel m best

/-- Scan all 2^30 masks in 1024 parallel chunks of 2^20. -/
def solveValue (sw t : @& ByteArray) : UInt64 :=
  let tasks := (List.range 1024).map fun c =>
    Task.spawn fun _ => scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL
  tasks.foldl (fun acc tk => let v := tk.get; if v < acc then v else acc) SENTINEL

/-- `f 0 + ⋯ + f (n - 1)`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

/-- Total weight of all ordered pairs of the thirty keys. -/
def totalWeight (cnt : Nat → Nat → Nat) : Nat := sumBelow (fun a => sumBelow (cnt a) 30) 30

/-- The least same-finger weight over every layout of thirty keys, or `none` when the weights are
too large for the 32-bit table. -/
def solve (cnt : Nat → Nat → Nat) : Option Nat :=
  if totalWeight cnt < 2 ^ 32 then
    let sw := swTable cnt
    some (solveValue sw (fill sw)).toNat
  else none

end FernImpl
