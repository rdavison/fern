# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Fern formalizes keyboard layout theory in Lean 4 with machine-checked proofs. There is no
application logic to speak of and no test framework: the theorems *are* the tests, so
`lake build` succeeding is the only correctness signal. CI (`.github/workflows/lean_action_ci.yml`)
runs `leanprover/lean-action@v1`, which is just a build.

## Commands

```sh
lake exe cache get     # fetch prebuilt mathlib oleans — do this before the first build
lake build             # build the Fern library (default target); the real "test suite"
lake build Fern.Ortholinear   # build one module and its deps
lake build fern-exe    # native build; `lake build` alone leaves the binary stale
lake exe fern-exe      # prints Ortho3x10 and ANSI as ASCII art
lake env lean Fern/Ortholinear.lean   # elaborate one file directly, ~10s; fastest edit loop
```

`lean-toolchain` pins `leanprover/lean4:v4.29.0-rc4` and elan selects it automatically.
mathlib is required at `rev = "master"` in `lakefile.toml` but resolved to a fixed commit in
`lake-manifest.json` — do not run `lake update` casually, as it moves mathlib to current master
and can break every proof at once.

## The experimental module system

`lakefile.toml` sets `weakLeanOptions = {"experimental.module" = true}` on the `Fern` lib. This
changes the surface syntax in ways that will not match most Lean code you have seen:

- Every file under `Fern/` (and `Fern.lean`) opens with a bare `module` line.
- Imports that re-export must be `public import` (see `Fern.lean`, which is the library root and
  does nothing but `public import` each module). A plain `import` is private to that file — e.g.
  `import Mathlib.Logic.Equiv.Prod` in `Fern/OrtholinearExamples.lean`.
- Declarations are private by default. Two styles coexist, both valid:
  - `Fern/Model.lean` annotates each declaration `public` or `private`.
  - `Fern/Ngram.lean`, `Fern/Ortholinear.lean`, the `Fern/Ortholinear/` modules and
    `Fern/OrtholinearExamples.lean` open an `@[expose] public section` after the imports, so
    everything below it is public *and* definitionally transparent.

`@[expose]` is load-bearing, not decoration. Dropping it from `Fern/Ortholinear.lean` breaks that
file's own build: `Layout.equivalent_refl` stops closing by `rfl` and the `Decidable (IsSFB L b)`
instance no longer type-checks, because `Layout.sfbs` and `IsSFB` are opaque without it. The
`decide`-based proofs in `Fern/OrtholinearExamples.lean` depend on the same transparency.

`Main.lean` is the executable root and is *not* a module — plain `import Fern`.

## Architecture

Two independent models live side by side. They share `Hand` and `Finger` from `Fern/Model.lean`
and nothing else. Do not assume a keycode in one is a `KeyId` in the other.

**Physical keyboards — `Fern/Model.lean`.** Concrete millimetre geometry. `KeyId` is a flat
84-constructor enum covering a full keyboard; `KeyId.toNat` gives it a `LinearOrder` via
`LinearOrder.lift'` and `KeyId.toNat_injective` (which needs `set_option maxHeartbeats 800000`
for its 84×84 case split). `Key` bundles id, `Position` (ℚ millimetres) and width, ordered
lexicographically by `keyOrd` as (y, x) then (width, id) so that `Finset.sort` yields reading
order. `Keyboard` is a `Finset Key`. The renderer (`groupRows` → `renderRow` → `reprKeyboard`,
all `private` except the last) turns a sorted key set into ASCII art at 5 characters per 1u,
where 1u = 19.05 mm. `Ortho3x10` and `ANSI` are built by the `rowKeys` helper from (id, width-in-u)
rows and prove their `Finset` nodup obligation with `by native_decide`.

**Abstract layout theory — `Fern/Ortholinear.lean`.** This is where the actual mathematics is,
and it is deliberately position-free at the top. `Position` is `Fin 3 × Fin 10` (grid coordinates,
unrelated to `Model.Position`). A `Layout Keycode` is an injective `keyAt : Position → Keycode`;
`Keycode` is an arbitrary type, not necessarily characters, so the ambient type may be far larger
than the 30 keys used.

The central distinction is *geometric column* (one of ten grid coordinates) versus *finger
column* (`ColumnId`, one of eight regions). Six `ColumnKind.simple` columns hold 3 keys; the two
`.index` columns hold 6, spanning two geometric columns. `columnAt : Fin 10 → ColumnId` is the
mapping, and `ColumnId.positions` is proved to be a rectangle (`positions_rectangle`), to cover
the grid (`positions_cover`), and to be pairwise disjoint (`positions_disjoint`).

Same-finger bigrams are the key definition. They are **ordered** pairs (`ab ≠ ba`) with repeats
excluded — `Finset.offDiag` over a column's keys. `Layout.sfbs` unions this over
`Layout.columns`, and two results anchor the file:

- `Layout.sfbs_card` : every layout has exactly 96 SFBs, proved by transporting
  `positionSFBs_card` (a `decide` over positions, needing `maxRecDepth 4096`) along the injection
  `Layout.bigramAt`.
- `Layout.equivalent_iff_sfbs_eq` : layouts are equivalent (same set of column key-sets) exactly
  when their SFB sets agree. The forward direction is trivial; the reverse goes through
  `Layout.recover_column`, which rebuilds a whole finger column from any one key plus its
  outgoing SFBs. `Layout.match_column_of_sfbs_eq` wraps that step in a section with
  `attribute [local irreducible] Layout.sfbs` to stop the elaborator unfolding the enumerated
  set during the transfer.

Equivalence therefore forgets row order, hand, finger identity, and inner-vs-outer index
placement. That is a theorem about the model's resolution, not a bug.

**Lookup and repertoires — `Fern/Ortholinear/Lookup.lean`.** `Repertoire` fixes thirty keycodes
so that layouts over an infinite ambient type form a finite collection; `LayoutOn R` is the
layouts using exactly those. `Layout.positionOf` is a computable inverse of `keyAt` (searching
`allPositions`, a hand-rolled list — `Finset.univ.toList` is noncomputable). `UsedKey L` bundles
a keycode with the proof that `L` uses it, and `Layout.posEquiv : Position ≃ UsedKey L` makes
position, column, hand, finger, row and inner-index lookup total. `SameColumn` is proved to be
an equivalence relation that holds exactly on equal-or-SFB pairs, and a key has `3 * width - 1`
same-finger partners: two in a simple column, five in an index column.

**Bigram classification — `Fern/Ortholinear/Classify.lean`.** `BigramKind` and a total
classifier on `UsedKey L × UsedKey L`. The counts (30 repeated, 96 same-finger, 324 same-hand,
450 opposite-hand, 900 total) are proved once at the position level by `decide`, then
transported to every layout along `posEquiv` — `Layout.classify_atPosition` is the bridge.

**Counting — `Fern/Ortholinear/Symmetry.lean`.** The largest module. `Layout.reindex` moves a
layout along a grid permutation and is injective in the permutation, which is what makes the
group action free. `ColumnSymmetry` is the subgroup of `Equiv.Perm Position` preserving the
same-column relation; `inducedPerm` extracts the column permutation it induces (read off
`ColumnId.rep`, a canonical position per column) and `fiberEquiv` its restriction to each
column. The order `D = 34828517376000` comes from a bijection `ColumnData ≃ ColumnSymmetry`,
where `ColumnData` is a kind-preserving `KindPerm` paired with a bijection per column;
`permPreservingEquiv` splits `KindPerm` into permutations of the six simple and two index
columns. `layoutOnEquiv` identifies `LayoutOn R` with bijections `Position ≃ R.keys`, giving
`30!`; `classEquiv` identifies each equivalence class with `ColumnSymmetry`, giving `D`; the
quotient `LayoutClass R` then has `30!/D` members. Nothing is enumerated.

**Swaps — `Fern/Ortholinear/Swap.lean`.** A swap is `reindex (Equiv.swap p q)`. The analysis
happens at the position level and transfers along `Layout.sfbs_eq_image` and
`Layout.bigramAt_injective`. The key decomposition is `swapLostPositions p q = sfbsAt p ∪ sfbsAt q`
for cross-column swaps — the lost pairs are exactly the same-finger pairs touching a swapped
position — which reduces the count to `card_sfbsAt`, a single 30-case `decide`. The symmetric
difference is `4 * (m + n - 2)`: 16, 28 or 40, and 0 within a column.

**Worked examples — `Fern/OrtholinearExamples.lean`.** Instantiates `Layout Position` with
positions as their own keycodes (`identityLayout`) and permutes them via `rearrange (e : Position ≃ Position)`
to show `rowSwap` / `simpleColumnSwap` / `indexHalfSwap` are equivalent while `individualKeySwap`
is not. Every proof here is `by decide` under `set_option maxRecDepth 4096` — the file comment
states the intent explicitly: closed finite computations go through the kernel, **not**
`native_decide`. Keep it that way when adding examples; `native_decide` is reserved for the
`Finset` nodup obligations in `Fern/Model.lean`.

**N-grams — `Fern/Ngram.lean`.** The generic extractors live under `Fern.Ngram` and are defined
by `zip` (`bigrams l := l.zip l.tail`), so their cons equations hold by `rfl` and core's `zip`
lemmas apply. They are the single implementation. The top-level `unigrams`, `bigrams`,
`trigrams`, `skipgrams` and `trills` are `Char` wrappers rendering windows as strings; private
verbatim copies of their original recursions (`*Spec`) are proved equal, so any behaviour change
fails the build. `trills` takes only `BEq`, matching the original `==`, and reports the `AB` of
an `ABA`. The file needs `@[expose]`: `public` alone would export the names but not their
unfolding, and downstream `rfl`/`decide` over `Ngram.bigrams` would fail.

**Corpus metrics — `Fern/Ortholinear/Corpus.lean`.** `Corpus Keycode` is `List Keycode`, a
keystroke stream independent of any layout. Each count exists at two levels, over an explicit
list of bigrams (`sfbCountIn`, `kindCountIn`, …) where the inductions run, and over a corpus.
`Layout.equivalent_iff_sfbCount_eq` is the headline: the backward direction instantiates the
corpus at `[a, b]`, where `sfbCount_pair` makes the count an indicator of `IsSFB`. `classify?`
classifies raw keycodes through `positionOf` and `positionKind`, returning `none` for keycodes
the layout lacks, so the five-way partition (`kindCount_add_unmappedCount`) holds with no side
condition; `Layout.Supports` is only a hypothesis for the four-way corollary. The hand split is
**not** equivalence-invariant, by design. The swap bound is stated as two additive `Nat`
inequalities plus a `ℤ` absolute value, never with `Nat` subtraction, and `Touches` orders its
disjuncts to match `Layout.mem_sfbsChanged_touches` exactly. `Keymap.corpus` drops unmapped
characters, which joins their neighbours; that non-commutation is intended and documented.

**`Fern/Frequency.lean`** is reserved for frequency *weighting* (rates, weighted costs) and
declares nothing yet.

## Two traps that cost real time

**Downstream of `Fern/Ortholinear.lean`, make `Layout.sfbs` and `positionSFBs` locally
irreducible.** Both are `@[expose]`d definitions over concrete `Finset`s built from
`Finset.univ`. In an importing module the unifier will happily try to evaluate the whole
eight-column union just to check a membership hypothesis, and a one-line proof turns into a
`whnf` heartbeat timeout. Every new module wraps the affected proofs in

```lean
section
attribute [local irreducible] Layout.sfbs   -- and/or positionSFBs
...
end
```

and uses the stated lemmas (`isSFB_iff`, `Layout.mem_sfbs`, `mem_positionSFBs`) instead of
definitional unfolding. The attribute is local, so `decide`-based examples elsewhere still see
the definitions. Symptom: `(deterministic) timeout at 'whnf'` on a proof that looks trivial.

**A `Fintype` instance on a closed type is executable code that runs at module
initialisation.** `Fintype KindPerm`, `Fintype ColumnData`, `Fintype (LayoutOn R)` and
`Fintype (LayoutClass R)` exist only to state cardinalities, and `ColumnData` has
34,828,517,376,000 elements. Left computable, `Fintype ColumnData` is a closed constant, so
loading `Fern` hangs `fern-exe` forever before `main` prints anything. They are all
`noncomputable instance`. Symptom: the library builds fine and the executable hangs with no
output — check `lake build fern-exe` output, not `lake build`.

## Proof conventions

- Prefer `by decide` / `by cases c <;> decide` for the finite enumerations — most `ColumnId` and
  `Hand` facts are one line. Raise `maxRecDepth` (4096 is the established value) rather than
  reaching for `native_decide`.
- `revert p; decide` is the idiom for quantified statements over `Fin`-indexed positions
  (`reflect_hand`, `outer_to_inner_order`).
- Cardinality lemmas are stated in terms of `ColumnKind.width` (`3 * c.kind.width`) rather than
  hardcoded numbers, so simple and index columns share one proof.
- Where an explicit inverse would be painful, build the map and use `Equiv.ofBijective` (or
  `Finite.injective_iff_bijective` on a `Fintype`). It is noncomputable, which is fine for
  cardinality results but see the trap above before making it an instance.
- Exhaustive `decide` checks are budgeted. `Finset` operations reduce through `Quot` and are
  roughly two orders of magnitude slower in the kernel than `List` ones: recomputing
  `positionSFBs` for each of the 435 position pairs takes about nine minutes, while the
  `List`-based check in `Fern/OrtholinearExamples.lean` takes seconds. Prefer `List` for
  anything quantified over many cases, and prove the expensive statement structurally instead.
  That file is the slowest in the build at roughly 37s; the rest are a few seconds each.
- A concrete `sfbCount` should be computed as `rw [← Layout.kindCount_sameFinger]; decide`.
  `kindCount` classifies through `positionOf`, a 30-element list search, while `sfbCount`
  decides `IsSFB`, which rebuilds the `Layout.sfbs` `Finset` for every bigram.
