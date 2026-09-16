# Fern

Formalizing keyboard layout theory in Lean 4.

Fern aims to give keyboard layout analysis precise definitions and machine-checked
proofs: how physical keyboards, character assignments, finger assignments, and
text statistics combine to describe typing patterns and compare layouts.

## Current foundations

- `Fern.Model`: hands, fingers, key identifiers, physical positions and widths,
  keyboard geometry, and ASCII rendering. Includes 3×10 ortholinear and ANSI
  keyboard examples, with proofs supporting key ordering.
- `Fern.Ngram`: extraction of unigrams, bigrams, trigrams, skipgrams, and
  character-based trill patterns.
- `Fern.Frequency`: a placeholder for corpus frequency analysis.
- `Fern.Ortholinear`: a formal 3×10 grid model with unique keycodes, finger
  columns, mirrored hand assignments, inner index regions, ordered same-finger
  bigrams (SFBs), and layout equivalence by column membership.
- `Fern.OrtholinearExamples`: checked examples of equivalent rearrangements
  and a counterexample where exchanging individual keys changes the SFB set.

The ortholinear model has eight finger columns: six simple columns containing
three keys each, and two index columns containing six keys each. Bigrams are
ordered pairs, so `ab` and `ba` differ; repeated-key pairs are excluded from SFBs.
The model proves that every layout has 96 possible SFBs and that two layouts are
equivalent exactly when their SFB sets agree. Equivalence forgets row order,
hand, finger identity, and which keys occupy the inner index regions.

Keycodes are generic and need not be characters. Corpus frequency analysis and
frequency-weighted ergonomic metrics remain to be formalized. The existing
physical keyboard renderer and character n-gram functions are separate APIs.

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

#check Fern.Ortholinear.Layout.usedKeys_card
#check Fern.Ortholinear.Layout.sfbs_card
#check Fern.Ortholinear.Layout.equivalent_iff_sfbs_eq
```
