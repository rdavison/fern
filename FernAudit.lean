import Fern

/-!
# Axiom audit for the exact solver

Each headline theorem's axioms are pinned with `#guard_msgs`, so a new dependency such as
`sorryAx`, a custom axiom, or native evaluation fails the build instead of passing silently. The
separate `FernResults` library is the only place native evaluation is allowed.

This is its own non-module library because `#print axioms` cannot be used inside a `module`. It is
a default target, so `lake build` enforces it.
-/

/-- info: 'FernImpl.get32_push32_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.get32_push32_self

/-- info: 'FernImpl.get32_push32_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.get32_push32_of_lt

/-- info: 'FernImpl.get32_tabulate32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.get32_tabulate32

/-- info: 'FernImpl.get!_mkBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.get!_mkBytes

/-- info: 'FernImpl.pop30_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.pop30_eq

/-- info: 'FernImpl.hibit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.hibit_eq

/-- info: 'FernImpl.decode_clearHigh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.decode_clearHigh

/-- info: 'FernImpl.foldBits_eq_foldl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.foldBits_eq_foldl

/-- info: 'FernImpl.bitsDesc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.bitsDesc_spec

/-- info: 'FernImpl.sum_bitsDesc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.sum_bitsDesc
