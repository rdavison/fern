module
import Batteries

/-!
# Frequency weighting (not yet formalised)

Unweighted counting is done: `Fern.Ortholinear.Corpus` measures a layout against a keystroke
stream, giving same-finger bigram counts, the four-way bigram split, and swap deltas.

What remains is *weighting*: turning those counts into rates over a corpus, aggregating
frequency tables, and scoring layouts with weighted ergonomic costs. This module is reserved
for that work and currently declares nothing.
-/

open Std (HashMap)
