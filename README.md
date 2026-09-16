# Fern

Formalizing keyboard layout theory in Lean 4.

Fern aims to give keyboard layout analysis precise definitions and machine-checked
proofs: how physical keyboards, character assignments, finger assignments, and
text statistics combine to describe typing patterns and compare layouts.

## Current foundations

- `Fern.Model`: hands, fingers, key identifiers, physical positions and widths,
  keyboard geometry, and ASCII rendering. Includes 3×10 ortholinear and ANSI
  keyboard examples, with proofs supporting key ordering.
- `Fern.Ngram`: extraction of unigrams, bigrams, trigrams, skipgrams, and trill
  patterns. The generic forms under `Fern.Ngram` work on any list, including a
  stream of keycodes; the top-level `Char` versions render them as strings.
- `Fern.Frequency`: reserved for frequency weighting, which is not yet formalized.
- `Fern.Ortholinear`: a formal 3×10 grid model with unique keycodes, finger
  columns, mirrored hand assignments, inner index regions, ordered same-finger
  bigrams (SFBs), and layout equivalence by column membership.
- `Fern.Ortholinear.Lookup`: repertoires of exactly thirty keycodes, computable
  position lookup, used keycodes as a subtype with total geometric lookup, the
  same-column equivalence relation, and same-finger partner counts.
- `Fern.Ortholinear.Classify`: an exhaustive four-way classification of ordered
  bigrams and its cardinalities.
- `Fern.Ortholinear.Symmetry`: reindexing along grid permutations, the column
  symmetry group, and the exact count of layouts and equivalence classes.
- `Fern.Ortholinear.Swap`: single swaps, and exactly how many same-finger
  bigrams they change.
- `Fern.Ortholinear.Corpus`: measuring a layout against a keystroke stream, and
  reading text into one through a keymap.
- `Fern.OrtholinearExamples`: checked examples of equivalent rearrangements
  and a counterexample where exchanging individual keys changes the SFB set.

The ortholinear model has eight finger columns: six simple columns containing
three keys each, and two index columns containing six keys each. Bigrams are
ordered pairs, so `ab` and `ba` differ; repeated-key pairs are excluded from SFBs.
The model proves that every layout has 96 possible SFBs and that two layouts are
equivalent exactly when their SFB sets agree. Equivalence forgets row order,
hand, finger identity, and which keys occupy the inner index regions.

## Classifying bigrams

Every ordered pair of used keycodes falls into exactly one of four categories,
and the counts are the same for every layout:

| Category | Ordered pairs |
|---|---:|
| Repeated key | 30 |
| Same finger | 96 |
| Same hand, different fingers | 324 |
| Opposite hands | 450 |
| Total | 900 |

Reversing a bigram preserves its category, and the same-finger category agrees
with `IsSFB`.

## Counting layouts

A `Repertoire` fixes thirty keycodes, so layouts over an infinite ambient
keycode type still form a finite collection. `ColumnSymmetry` is the group of
grid permutations preserving the same-column relation. Each such permutation
induces a unique kind-preserving permutation of the eight finger columns
together with an arbitrary bijection inside each column, which gives its order

    D = (3!)^6 (6!)^2 6! 2! = 34,828,517,376,000.

Two layouts are equivalent exactly when one is a reindexing of the other by a
column symmetry, and that permutation is unique, so the action
`σ • L = L.reindex σ⁻¹` is free and its orbits are the equivalence classes.
Every repertoire carries `30!` layouts, each class contains exactly `D` of them,
and therefore

    |LayoutClass R| = 30! / D = 7,615,967,597,718,480,000.

These are structural finite-cardinality proofs; no layout is ever enumerated.

## Swapping keys

A swap is a reindexing along a transposition. Swapping a position with itself
does nothing and repeating a swap restores the original layout. A swap preserves
equivalence exactly when its two positions share a finger column. Otherwise, for
columns of sizes `m` and `n`, exactly `2 (m + n - 2)` ordered SFBs disappear and
the same number appear, so the symmetric difference has `4 (m + n - 2)` members:
16 for two simple columns, 28 for a simple and an index column, and 40 for two
index columns. Every changed bigram contains one of the two swapped keycodes.
All 435 distinct position pairs are checked.

## Measuring a corpus

Everything above is structural: every layout has the same 96 possible SFBs. A
corpus is where layouts differ. `Corpus Keycode` is a keystroke stream that does
not depend on any layout, so two layouts can be measured on the same text.
`Layout.sfbCount` counts the same-finger bigrams in it, and `Layout.kindCount`
splits its bigrams into the four categories, with `Layout.unmappedCount` for
bigrams using a keycode the layout lacks. Those five counts always sum to the
number of bigrams.

Corpus counts see exactly layout equivalence: two layouts are equivalent if and
only if they give the same same-finger bigram count on every corpus, and
two-keystroke corpora already suffice. The hand split is different, because
equivalence forgets hand; the examples include two equivalent layouts that
disagree on opposite-hand bigrams for the same text.

One swap moves the same-finger bigram count by at most the number of corpus
bigrams involving the two swapped keycodes, so a swap of keys the text never
uses changes nothing.

A `Keymap` reads text into a corpus, dropping unmapped characters. Their
neighbours then become adjacent, so reading text does not commute with n-gram
extraction; this is intended, and an example records it.

Keycodes are generic and need not be characters. Frequency *weighting* (rates
and weighted ergonomic costs) remains to be formalized. The physical keyboard
renderer is still a separate API.

## Build and run

With [elan](https://github.com/leanprover/elan) installed, the pinned Lean version
is selected automatically from `lean-toolchain`.

```sh
lake exe cache get
lake build
lake exe fern-exe
```

The executable prints the example keyboards as ASCII art. Dependency revisions
are pinned in `lake-manifest.json`.

## Use the library

```lean
import Fern

#check Keyboard
#check KeyId.toNat_injective
#eval bigrams "fern".toList

open Fern.Ortholinear

#check Layout.usedKeys_card
#check Layout.sfbs_card
#check Layout.equivalent_iff_sfbs_eq

#check Layout.positionOf_eq_some
#check Layout.card_outgoing
#check Layout.classify_card
#check card_columnSymmetry
#check card_layoutOn
#check card_layoutClass
#check Layout.card_sfbsChanged

#check Fern.Ngram.bigrams
#check Layout.equivalent_iff_sfbCount_eq
#check Layout.kindCount_add_unmappedCount
#check Layout.abs_sfbCount_sub_swap_le
```
