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
- `Fern.Ortholinear.Pieces`: layouts up to equivalence are piece-sets, and the
  same-finger cost is a sum over pieces.
- `Fern.Ortholinear.Text`: reading prose so that unmapped characters break bigrams,
  and spacegrams (key, space, key) kept apart from skipgrams.
- `Fern.Ortholinear.Hands`: the twenty ways to share pieces between the hands.
- `Fern.Solver`: an exact search for the fewest same-finger bigrams, proved correct,
  with kernel-checked certificates.
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

## Pieces

Up to equivalence, a layout is a *piece-set*: its thirty keys split into six unordered blocks
of three and two unordered blocks of six, with no memory of rows, fingers or hands.
`layoutClassEquiv` makes this exact, since equivalence classes and piece-sets are in bijection,
and `card_pieceSets` recovers the class count above. The same-finger weight of a layout is the
sum of its pieces' weights (`Layout.sfbWeight_eq_pieceCost`), and the count on a list of bigrams
is that weight under the bigram counts (`Layout.sfbCountIn_eq_sfbWeight`).

## Reading text

`Keymap.bigramsOf` takes a text's own adjacent character pairs and keeps those with both
characters mapped, so an unmapped character such as a space breaks the stream. The text splits
into segments of mapped keys, and every corpus theorem applies segment by segment. Skipgrams
(key, key, key) and spacegrams (key, space, key) are kept apart; only a literal space is a
spacegram's middle, so separate lines never join.

## The exact search

`FernImpl.solve` finds the least same-finger weight over all 30! layouts of thirty keys. It does
not enumerate layouts or classes. Instead it:

1. fills a 2^30-cell table with the cheapest partition of every key set of size at most fifteen
   into triples;
2. scans all C(30,12) = 86,493,225 choices of index keys in 1024 parallel chunks;
3. adds the cheapest six/six split of each choice to the best triples on its eighteen-key
   complement.

On an M4 Pro this takes about eight minutes and 4.3 GB.

It is proved, in the kernel, to agree with a plain `Finset` specification:

- `Fern.Solver.optimumRef_isLeast_layouts`: the specification is the least same-finger weight
  over every layout.
- `Fern.Solver.solve_eq`: whenever the weights fit its 32-bit table, `solve cnt` returns exactly
  that value.
- `Fern.Solver.solve_isLeast`, `Fern.Solver.solveText_isLeast`: any value it returns is the
  least over every layout, for weights or for a text's bigram counts.

The executable code in `FernImpl` imports no Mathlib and is compiled natively. Every theorem's
axioms are pinned in `FernAudit`, and CI rejects `implemented_by`, `extern`, `unsafe`,
`partial`, `native_decide` and `bv_decide` in solver code.

Certificates re-check results using only the standard axioms:

- `checkPieces_sound`: the reported pieces use every key once and cost the reported value, so
  some layout achieves it.
- `checkTieBreak_sound`: see below.

## Hands and spacegrams

Equivalence forgets hands, but the number of spacegrams typed by one hand does not. Each hand
holds three simple pieces and one index piece. With the first index piece fixed on one hand,
there are exactly twenty choices (`card_handSides`). They are exhaustive, every one is realised
by a layout, and mirroring the hands changes nothing (`sameHandWeights_eq`). `checkTieBreak`
evaluates all twenty with list functions for the kernel, and `checkTieBreak_sound` proves the
least same-hand spacegram weight among layouts with a given piece-set.

## Result: the fewest same-finger bigrams on monkeyracer

The corpus is `mr.txt` ("monkeyracer"), the AKL community's concatenation of the Typeracer and
Monkeytype quotes. It is read as follows:

- **Keys:** `a`–`z` and `, . ' ;`, with ASCII capitals folded to lower case.
- **Unmapped characters:** everything else, including spaces, digits and `-`. Each one breaks the
  stream, so no bigram spans it.

That gives 1,425,006 bigrams. `data/` holds the count tables and the corpus checksum; the text
itself is not redistributed.

**The least possible same-finger bigram count over every layout of those thirty keys is 6,701
(0.470%).** QWERTY's columns give 85,943 on the same counts, almost thirteen times as many.

This layout achieves it:

```
a v h g w   m k u . x
o s n c y   t d e i r
' b l f p   j q ; , z
```

Same-finger bigrams depend only on which keys share a finger, so rows, finger order and the
inner/outer index split can be rearranged freely. Each column's most frequent key is on the home
row, but nothing else about key placement is optimised. By finger:

| Finger | Left | SFBs | Right | SFBs |
|---|---|---:|---|---:|
| Pinky | `'oa` | 881 | `zxr` | 6 |
| Ring | `vsb` | 448 | `.,i` | 148 |
| Middle | `nlh` | 1,587 | `;ue` | 1,775 |
| Index | `ywpgfc` | 1,486 | `tqmkjd` | 370 |

Other measures of the same layout on the same corpus:

| Measure | Count | Total |
|---|---:|---:|
| Same-finger bigrams | 6,701 | 1,425,006 |
| Same-finger skipgrams | 65,383 | 1,020,952 |
| Same-finger spacegrams | 38,799 | 405,924 |
| Same-hand spacegrams | 193,879 | 405,924 |
| Alternating-hand spacegrams | 212,045 | 405,924 |

Hands do not affect same-finger bigrams, but they do affect spacegrams (key, space, key). With these
fingers there are exactly twenty ways to split the pieces between the hands, ranging from 193,879
to 209,665 same-hand spacegrams. The layout above uses the unique best.

What is proved, and how:

| Claim | Theorem | Trust |
|---|---|---|
| Some layout has 6,701 | `Fern.Solver.Data.mr_upper` | kernel, standard axioms |
| No layout has fewer | `mr_optimal` in `FernResults` | proved solver, run by `native_decide` |
| 193,879 is the fewest same-hand spacegrams with these fingers | `Fern.Solver.Data.mr_sameHand` | kernel, standard axioms |

`mr_optimal` combines `Fern.Solver.solve_isLeast` with `mr_solve : FernImpl.solve (tableFn
mrTable) = some 6701`. That equation is checked by native evaluation, so it trusts the Lean compiler,
which the pinned axioms show. Everything else in the table is kernel-checked. The search takes 8.4
minutes on an M4 Pro (210 s fill, 296 s scan) and 4.3 GB. Checks outside Lean:

- the bigram and spacegram tables match an independent Python count;
- the layout's same-finger bigram count was recomputed from the grid;
- the twenty spacegram costs were recomputed independently.

The search reports one optimal piece-set. Whether others tie it was not explored.

To reproduce, place the corpus at `data/mr.txt` (checksum in `data/README.md`), then run:

```sh
lake build fern-solve
.lake/build/bin/fern-solve count data/mr.txt > data/mr.tsv
.lake/build/bin/fern-solve solve data/mr.tsv > data/mr.result
lake build FernResults   # reruns the search under native_decide
```

## `fern-solve`

```sh
lake build fern-solve
.lake/build/bin/fern-solve count TEXT > TABLE.tsv        # --skipgrams, --spacegrams
.lake/build/bin/fern-solve check TEXT TABLE.tsv
.lake/build/bin/fern-solve solve TABLE.tsv > RESULT
.lake/build/bin/fern-solve cert NAME TABLE.tsv RESULT > Fern/Solver/Data/NAME.lean
.lake/build/bin/fern-solve tiecert NAME SPACEGRAMS.tsv RESULT > Fern/Solver/Data/NAMEHands.lean
```

`count` and `check` read text through `countLines`, which is proved equal to the text's bigram
counts. `solve` reports the proved optimum, then finds pieces achieving it and re-checks their
cost directly.

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

#check layoutClassEquiv
#check Layout.sfbWeight_eq_pieceCost
#check sameHandWeights_eq
#check Fern.Solver.solve_isLeast
#check Fern.Solver.solveText_isLeast
#check Fern.Solver.Data.mr_upper
#check Fern.Solver.Data.mr_sameHand
```
