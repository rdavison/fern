module
public import Fern.Solver.Keys

/-!
# Kernel-checked cost certificates

A solver run reports its optimum together with the pieces achieving it. `checkPieces` re-checks
such a report with plain structural list functions, cheap enough for `decide`: the pieces use every
key once, six of them have three keys and two have six, and their same-finger weights sum to the
reported value. `checkPieces_sound` turns a successful check into a layout with exactly that
weight, so a certificate proves an upper bound on the optimum using only the standard axioms.
-/

@[expose] public section

namespace Fern.Solver

open Finset Fern.Ortholinear

/-- A count table given as 900 entries, read by key numbers. -/
def tableFn (tbl : List ℕ) (a b : ℕ) : ℕ := tbl.getD (a * 30 + b) 0

/-- The same-finger weight of a piece given as a list: every ordered pair of distinct keys. -/
def listPieceWeight (w : Fin 30 → Fin 30 → ℕ) (l : List (Fin 30)) : ℕ :=
  (l.map fun x => (l.map fun y => if x = y then 0 else w x y).sum).sum

theorem listPieceWeight_eq (w : Fin 30 → Fin 30 → ℕ) {l : List (Fin 30)} (hl : l.Nodup) :
    listPieceWeight w l = pieceWeight w l.toFinset := by
  have hoff : l.toFinset.offDiag = (l.toFinset ×ˢ l.toFinset).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag, and_assoc]
  rw [pieceWeight, hoff, Finset.sum_filter, Finset.sum_product, listPieceWeight,
    ← List.sum_toFinset _ hl]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← List.sum_toFinset _ hl]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : x = y <;> simp [h]

/-- The pieces use each of the thirty keys once, six have three keys and two have six, and their
same-finger weights sum to `n`. -/
def checkPieces (w : Fin 30 → Fin 30 → ℕ) (P : List (List (Fin 30))) (n : ℕ) : Bool :=
  decide P.flatten.Nodup && P.flatten.length == 30 &&
    P.all (fun p => p.length == 3 || p.length == 6) &&
    (P.filter (·.length == 3)).length == 6 && (P.filter (·.length == 6)).length == 2 &&
    (P.map (listPieceWeight w)).sum == n

theorem toFinset_filter_length {P : List (List (Fin 30))} (hnd : ∀ l ∈ P, l.Nodup) (k : ℕ) :
    ((P.map List.toFinset).toFinset).filter (·.card = k) =
      ((P.filter (·.length == k)).map List.toFinset).toFinset := by
  ext q
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨l, hl, rfl⟩, hk⟩
    exact ⟨l, ⟨hl, by rw [← List.toFinset_card_of_nodup (hnd l hl), hk]⟩, rfl⟩
  · rintro ⟨l, ⟨hl, hk⟩, rfl⟩
    exact ⟨⟨l, hl, rfl⟩, by rw [List.toFinset_card_of_nodup (hnd l hl), hk]⟩

/-- A successful check is a layout whose same-finger weight is exactly the reported value. -/
theorem checkPieces_sound {w : Fin 30 → Fin 30 → ℕ} {P : List (List (Fin 30))} {n : ℕ}
    (h : checkPieces w P n = true) : ∃ L : LayoutOn fullRepertoire, L.val.sfbWeight w = n := by
  simp only [checkPieces, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hflat, hlen⟩, hall⟩, h3⟩, h6⟩, hsum⟩ := h
  obtain ⟨hnd, hpw⟩ := List.nodup_flatten.mp hflat
  have hne : ∀ l ∈ P, l ≠ [] := fun l hl he => by
    rcases hall l hl with h | h <;> simp [he] at h
  -- Distinct pieces give distinct key sets.
  have hmapnd : (P.map List.toFinset).Nodup := by
    refine List.pairwise_map.mpr (hpw.imp_of_mem fun {a b} ha _ hd heq => ?_)
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a (hne a ha)
    have hxb : x ∈ b := by
      rw [← List.mem_toFinset, ← heq, List.mem_toFinset]
      exact hx
    exact hd hx hxb
  set Q := (P.map List.toFinset).toFinset with hQ
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ l ∈ P, l.toFinset = q := fun q => by
    simp [hQ, List.mem_map]
  have hcount : ∀ k, (Q.filter (·.card = k)).card = (P.filter (·.length == k)).length := fun k => by
    rw [toFinset_filter_length hnd, List.toFinset_card_of_nodup
      (hmapnd.sublist ((List.filter_sublist).map _)), List.length_map]
  have hP : IsPieceSet (univ : Finset (Fin 30)) Q := by
    refine ⟨fun p hp q hq hpq => ?_, ?_, fun q hq => ?_, by rw [hcount]; exact h3,
      by rw [hcount]; exact h6⟩
    · obtain ⟨l₁, hl₁, rfl⟩ := (hmemQ p).mp hp
      obtain ⟨l₂, hl₂, rfl⟩ := (hmemQ q).mp hq
      have hl : l₁ ≠ l₂ := fun he => hpq (by rw [he])
      exact List.disjoint_toFinset_iff_disjoint.mpr
        (hpw.forall (fun _ _ h => h.symm) hl₁ hl₂ hl)
    · have hcard : P.flatten.toFinset.card = 30 := by
        rw [List.toFinset_card_of_nodup hflat, hlen]
      have huniv : P.flatten.toFinset = univ :=
        Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
      rw [← huniv]
      ext x
      simp only [Finset.mem_biUnion, id, List.mem_toFinset, List.mem_flatten, hmemQ]
      constructor
      · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
        exact ⟨l, hl, List.mem_toFinset.mp hx⟩
      · rintro ⟨l, hl, hx⟩
        exact ⟨l.toFinset, ⟨l, hl, rfl⟩, List.mem_toFinset.mpr hx⟩
    · obtain ⟨l, hl, rfl⟩ := (hmemQ q).mp hq
      rw [List.toFinset_card_of_nodup (hnd l hl)]
      exact hall l hl
  have hcost : pieceCost w Q = n := by
    rw [pieceCost, hQ, List.sum_toFinset _ hmapnd, List.map_map, ← hsum]
    exact congrArg List.sum (List.map_congr_left fun l hl => (listPieceWeight_eq w (hnd l hl)).symm)
  obtain ⟨L, hL⟩ := exists_layoutOn_columns_eq fullRepertoire hP
  exact ⟨L, by rw [Layout.sfbWeight_eq_pieceCost, hL, hcost]⟩

end Fern.Solver
