import Fern

/-!
# Results that rely on native evaluation

`mr_solve` runs the proved exact search on the bigram counts of `mr.txt` (see `data/README.md`)
by `native_decide`, and `mr_optimal` combines it with `Fern.Solver.solve_isLeast`: 6701 is the
fewest same-finger bigrams of any layout of the thirty keys on that corpus.

Unlike everything in `Fern`, this trusts the compiler and runtime: `native_decide` records the
evaluation as an axiom of its own, `mr_solve._native.native_decide.ax_1_1`. The axiom pins below
confine it to these declarations. The kernel-checked upper bound
`Fern.Solver.Data.mr_upper` needs only the standard axioms.

This library is not a default target. Building it reruns the search: about eight minutes and
4.3 GB.
-/

open Fern.Ortholinear Fern.Solver Fern.Solver.Data

/-- The exact search, run natively on the `mr.txt` bigram counts. -/
theorem mr_solve : FernImpl.solve (tableFn mrTable) = some 6701 := by
  native_decide

/-- On `mr.txt`, every layout of the thirty keys types at least 6701 same-finger bigrams, and some
layout types exactly 6701. -/
theorem mr_optimal :
    IsLeast (Set.range fun L : LayoutOn fullRepertoire =>
      L.val.sfbWeight fun a b => tableFn mrTable a.val b.val) 6701 :=
  solve_isLeast mr_solve

/-- info: 'mr_optimal' depends on axioms: [propext, Classical.choice, Quot.sound, mr_solve._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms mr_optimal

/-- info: 'Fern.Solver.Data.mr_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mr_upper

/-- info: 'Fern.Solver.Data.mr_sameHand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mr_sameHand
