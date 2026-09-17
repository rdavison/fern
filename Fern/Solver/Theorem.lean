module
public import Fern.Solver.Proof.Scan
public import Fern.Ortholinear.Text

/-!
# What the exact solver guarantees

`FernImpl.solve` is the fast search: a 4 GiB table of triple partitions, then a parallel scan over
every choice of index keys. Whenever the weights fit its 32-bit table it returns the least
same-finger weight over every layout of the thirty keys, and any value it returns is that least
weight. For text, the weights are the counts of the text's own bigrams, so the value is the fewest
same-finger bigrams any layout can type the text with.
-/

@[expose] public section

namespace Fern.Solver

open Finset Fern.Ortholinear FernImpl

/-- The solver computes the reference optimum whenever the weights fit its table. -/
theorem solve_eq {cnt : ℕ → ℕ → ℕ} (h : totalWeight cnt < 2 ^ 32) :
    solve cnt = some (optimumRef fun a b => cnt a.val b.val) := by
  have hle : optimumRef (fun a b => cnt a.val b.val) ≤ 2 ^ 62 := by
    have := optimumRef_lt h
    omega
  have hv := solveValue_spec h
  rw [inf_maskCost, optimumTop_eq_ref, toNat_SENTINEL, min_eq_right (by exact_mod_cast hle)] at hv
  unfold solve
  rw [if_pos h]
  exact congrArg some (by exact_mod_cast hv)

/-- Any value the solver returns is the least same-finger weight over every layout. -/
theorem solve_isLeast {cnt : ℕ → ℕ → ℕ} {k : ℕ} (h : solve cnt = some k) :
    IsLeast (Set.range fun L : LayoutOn fullRepertoire => L.val.sfbWeight fun a b => cnt a.val b.val)
      k := by
  by_cases hb : totalWeight cnt < 2 ^ 32
  · rw [solve_eq hb, Option.some.injEq] at h
    exact h ▸ optimumRef_isLeast_layouts
  · unfold solve at h
    rw [if_neg hb] at h
    exact absurd h.symm (Option.some_ne_none k)

/-- Bigram counts indexed by key number, the form `solve` reads. -/
def natCount (bs : List (Bigram (Fin 30))) (a b : ℕ) : ℕ :=
  if h : a < 30 ∧ b < 30 then bigramCount bs ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem natCount_fin (bs : List (Bigram (Fin 30))) (a b : Fin 30) :
    natCount bs a.val b.val = bigramCount bs a b := by
  simp [natCount, a.isLt, b.isLt]

/-- Any value the solver returns on a text's bigram counts is the fewest same-finger bigrams any
layout of the thirty keys types that text with. -/
theorem solveText_isLeast (m : Keymap (Fin 30)) (cs : List Char) {k : ℕ}
    (h : solve (natCount (m.bigramsOf cs)) = some k) :
    IsLeast (Set.range fun L : LayoutOn fullRepertoire => L.val.sfbCountIn (m.bigramsOf cs)) k := by
  have hw : (fun a b : Fin 30 => natCount (m.bigramsOf cs) a.val b.val) =
      bigramCount (m.bigramsOf cs) :=
    funext fun a => funext fun b => natCount_fin _ a b
  have hfun : (fun L : LayoutOn fullRepertoire => L.val.sfbCountIn (m.bigramsOf cs)) =
      fun L => L.val.sfbWeight (bigramCount (m.bigramsOf cs)) :=
    funext fun L => Layout.sfbCountIn_eq_sfbWeight _ _
  rw [hfun, ← hw]
  exact solve_isLeast h

end Fern.Solver
