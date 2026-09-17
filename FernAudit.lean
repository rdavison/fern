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

/-- info: 'Fern.Ortholinear.Layout.sfbWeight_eq_pieceCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Layout.sfbWeight_eq_pieceCost

/-- info: 'Fern.Ortholinear.Layout.sfbCountIn_eq_sfbWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Layout.sfbCountIn_eq_sfbWeight

/-- info: 'Fern.Ortholinear.pieceCost_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.pieceCost_split

/-- info: 'Fern.Ortholinear.LayoutOn.columns_isPieceSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.LayoutOn.columns_isPieceSet

/-- info: 'Fern.Ortholinear.exists_layoutOn_columns_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.exists_layoutOn_columns_eq

/-- info: 'Fern.Ortholinear.layoutClassEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.layoutClassEquiv

/-- info: 'Fern.Ortholinear.card_pieceSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.card_pieceSets

/-- info: 'Fern.Ortholinear.Keymap.bigramsOf_eq_flatMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Keymap.bigramsOf_eq_flatMap

/-- info: 'Fern.Ortholinear.Keymap.flatten_segments' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Keymap.flatten_segments

/-- info: 'Fern.Ortholinear.Keymap.mem_bigramsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Keymap.mem_bigramsOf

/-- info: 'Fern.Ortholinear.Keymap.mem_spacegramsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Keymap.mem_spacegramsOf

/-- info: 'Fern.Ortholinear.Layout.sfbCountIn_bigramsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Layout.sfbCountIn_bigramsOf

/-- info: 'Fern.Ortholinear.Layout.abs_sfbCountIn_sub_swap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Ortholinear.Layout.abs_sfbCountIn_sub_swap_le

/-- info: 'Fern.Solver.bestTriplesRef_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.bestTriplesRef_isLeast

/-- info: 'Fern.Solver.bestTriplesRef_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.bestTriplesRef_step

/-- info: 'Fern.Solver.indexCostTop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.indexCostTop_le

/-- info: 'Fern.Solver.indexCostTop_achieved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.indexCostTop_achieved

/-- info: 'Fern.Solver.optimumRef_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.optimumRef_isLeast

/-- info: 'Fern.Solver.optimumRef_isLeast_layouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.optimumRef_isLeast_layouts

/-- info: 'FernImpl.sw32_swTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.sw32_swTable

/-- info: 'FernImpl.rowSum_swTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.rowSum_swTable

/-- info: 'FernImpl.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.step_spec

/-- info: 'FernImpl.fill_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.fill_spec

/-- info: 'FernImpl.splitMin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.splitMin_spec

/-- info: 'FernImpl.indexCost_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.indexCost_spec

/-- info: 'FernImpl.scanRange_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.scanRange_spec

/-- info: 'FernImpl.solveValue_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.solveValue_spec

/-- info: 'FernImpl.inf_maskCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FernImpl.inf_maskCost

/-- info: 'Fern.Solver.solve_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.solve_eq

/-- info: 'Fern.Solver.solve_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.solve_isLeast

/-- info: 'Fern.Solver.solveText_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fern.Solver.solveText_isLeast
