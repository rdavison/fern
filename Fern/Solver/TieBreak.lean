module
public import Fern.Solver.Certificate
public import Fern.Ortholinear.Hands
public import Mathlib.Data.List.Sublists

/-!
# Kernel-checked spacegram tie-breaks

Among the layouts with a given piece-set, the same-hand spacegram count depends only on which three
simple pieces share a hand with the first index piece: twenty choices (`sameHandWeights_eq`).
`checkTieBreak` evaluates all twenty with structural list functions and checks that `n` is the
least; `checkTieBreak_sound` turns a successful check into the statement that `n` is the least
same-hand weight over every layout with those pieces. It uses only the standard axioms.
-/

@[expose] public section

namespace Fern.Solver

open Finset Fern.Ortholinear

/-- The weight of every ordered pair of keys in a list, each key paired with itself included. -/
def listSideWeight (w : Fin 30 → Fin 30 → ℕ) (l : List (Fin 30)) : ℕ :=
  (l.map fun x => (l.map (w x)).sum).sum

theorem listSideWeight_eq (w : Fin 30 → Fin 30 → ℕ) {l : List (Fin 30)} (hl : l.Nodup) :
    listSideWeight w l = sideWeight w l.toFinset := by
  rw [sideWeight, Finset.sum_product, listSideWeight, ← List.sum_toFinset _ hl]
  exact Finset.sum_congr rfl fun x _ => (List.sum_toFinset _ hl).symm

/-- The same-hand weight when one hand holds the index piece `I` with the simple pieces `C`, and
the other hand holds `J` with the remaining simple pieces. -/
def listSideCost (w : Fin 30 → Fin 30 → ℕ) (I J : List (Fin 30)) (simple C : List (List (Fin 30))) :
    ℕ :=
  listSideWeight w (I ++ C.flatten) + listSideWeight w (J ++ (simple.filter (· ∉ C)).flatten)

/-- The same-hand weights of the twenty ways to share the simple pieces between the hands. -/
def tieBreakCosts (w : Fin 30 → Fin 30 → ℕ) (I J : List (Fin 30)) (simple : List (List (Fin 30))) :
    List ℕ :=
  (simple.sublistsLen 3).map (listSideCost w I J simple)

/-- The pieces, index pieces first, use every key once with the right sizes, and `n` is the least of
the twenty same-hand weights. -/
def checkTieBreak (w : Fin 30 → Fin 30 → ℕ) : List (List (Fin 30)) → ℕ → Bool
  | I :: J :: simple, n =>
    decide (I :: J :: simple).flatten.Nodup && (I :: J :: simple).flatten.length == 30 &&
      I.length == 6 && J.length == 6 && simple.length == 6 && simple.all (·.length == 3) &&
      (tieBreakCosts w I J simple).all (n ≤ ·) && (tieBreakCosts w I J simple).contains n
  | _, _ => false

section Sound

variable {w : Fin 30 → Fin 30 → ℕ} {I J : List (Fin 30)} {simple : List (List (Fin 30))}

/-- Every key lies in exactly one of the pieces. -/
theorem mem_pieces_of_nodup (hflat : (I :: J :: simple).flatten.Nodup)
    (hlen : (I :: J :: simple).flatten.length = 30) (x : Fin 30) :
    x ∈ I ∨ x ∈ J ∨ ∃ l ∈ simple, x ∈ l := by
  have huniv : (I :: J :: simple).flatten.toFinset = univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hflat, hlen, Fintype.card_fin])
  have hx : x ∈ (I :: J :: simple).flatten := by
    rw [← List.mem_toFinset, huniv]
    exact Finset.mem_univ x
  simpa [List.mem_flatten, or_assoc] using hx

/-- A choice of three simple pieces for the first hand gives one side, and its cost is the list
cost. -/
theorem sideCost_of_choice (hflat : (I :: J :: simple).flatten.Nodup)
    (hlen : (I :: J :: simple).flatten.length = 30) {C : List (List (Fin 30))} (hC : C.Sublist simple) :
    (C.map List.toFinset).toFinset.biUnion id ∪ I.toFinset = (I ++ C.flatten).toFinset ∧
      sideCost w univ (I ++ C.flatten).toFinset = listSideCost w I J simple C := by
  obtain ⟨hnd, hpw⟩ := List.nodup_flatten.mp hflat
  have hpw' := List.pairwise_cons.mp hpw
  have hpw'' := List.pairwise_cons.mp hpw'.2
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, List.mem_map, id,
      List.mem_append, List.mem_flatten]
    constructor
    · rintro (⟨_, ⟨l, hl, rfl⟩, hx⟩ | hx)
      · exact Or.inr ⟨l, hl, List.mem_toFinset.mp hx⟩
      · exact Or.inl hx
    · rintro (hx | ⟨l, hl, hx⟩)
      · exact Or.inr hx
      · exact Or.inl ⟨l.toFinset, ⟨l, hl, rfl⟩, List.mem_toFinset.mpr hx⟩
  · have hflat' : (I :: J :: simple).flatten = I ++ (J ++ simple.flatten) := by
      simp [List.flatten_cons]
    have hA : (I ++ C.flatten).Nodup := by
      refine hflat.sublist ?_
      rw [hflat']
      exact (List.Sublist.refl I).append
        (hC.flatten.trans (List.sublist_append_right J simple.flatten))
    have hB : (J ++ (simple.filter (· ∉ C)).flatten).Nodup := by
      refine hflat.sublist ?_
      rw [hflat']
      exact ((List.Sublist.refl J).append (List.filter_sublist.flatten)).trans
        (List.sublist_append_right I _)
    have hcompl : univ \ (I ++ C.flatten).toFinset = (J ++ (simple.filter (· ∉ C)).flatten).toFinset := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_append,
        List.mem_flatten, List.mem_filter, decide_eq_true_eq, not_or, not_exists, not_and]
      constructor
      · rintro ⟨hxI, hxC⟩
        rcases mem_pieces_of_nodup hflat hlen x with hx | hx | ⟨l, hl, hx⟩
        · exact absurd hx hxI
        · exact Or.inl hx
        · exact Or.inr ⟨l, ⟨hl, fun hlC => hxC l hlC hx⟩, hx⟩
      · rintro (hx | ⟨l, ⟨hl, hlC⟩, hx⟩)
        · refine ⟨fun hxI => hpw'.1 J (List.mem_cons_self) hxI hx, fun l hlC hxl => ?_⟩
          exact hpw''.1 l (hC.subset hlC) hx hxl
        · refine ⟨fun hxI => hpw'.1 l (List.mem_cons_of_mem J hl) hxI hx, fun l' hl'C hxl' => ?_⟩
          have hne : l ≠ l' := fun e => hlC (e ▸ hl'C)
          exact hpw''.2.forall (fun _ _ h => h.symm) hl (hC.subset hl'C) hne hx hxl'
    rw [sideCost, hcompl, listSideCost, listSideWeight_eq w hA, listSideWeight_eq w hB]

/-- A successful check: `n` is the least same-hand weight over every layout with these pieces. -/
theorem checkTieBreak_sound {w : Fin 30 → Fin 30 → ℕ} {P : List (List (Fin 30))} {n : ℕ}
    (h : checkTieBreak w P n = true) :
    IsLeast (Set.range fun L : {L : LayoutOn fullRepertoire // L.val.columns = (P.map List.toFinset).toFinset} =>
      L.val.val.sameHandWeight w) n := by
  match P, h with
  | I :: J :: simple, h =>
    simp only [checkTieBreak, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hflat, hlen⟩, hI6⟩, hJ6⟩, hs6⟩, hsall⟩, hlow⟩, hcont⟩ := h
    have hall : ∀ p ∈ I :: J :: simple, p.length = 3 ∨ p.length = 6 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr hI6
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr hJ6
      · exact Or.inl (hsall p hp)
    have hf3 : simple.filter (·.length == 3) = simple :=
      List.filter_eq_self.mpr fun p hp => by simp [hsall p hp]
    have hf6 : simple.filter (·.length == 6) = [] :=
      List.filter_eq_nil_iff.mpr fun p hp => by simp [hsall p hp]
    have h3 : ((I :: J :: simple).filter (·.length == 3)).length = 6 := by
      simp only [List.filter_cons, hI6, hJ6, hf3]
      simpa using hs6
    have h6 : ((I :: J :: simple).filter (·.length == 6)).length = 2 := by
      simp [hI6, hJ6, hf6]
    obtain ⟨hP, hmapnd⟩ := isPieceSet_of_lists hflat hlen hall h3 h6
    have hnd := (List.nodup_flatten.mp hflat).1
    have hsimplend : (simple.map List.toFinset).Nodup :=
      (List.nodup_cons.mp (List.nodup_cons.mp hmapnd).2).2
    set Q := ((I :: J :: simple).map List.toFinset).toFinset with hQ
    have hI : I.toFinset ∈ Q.filter fun p : Finset (Fin 30) => p.card = 6 :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map_of_mem List.mem_cons_self),
        by rw [List.toFinset_card_of_nodup (hnd I List.mem_cons_self), hI6]⟩
    have hsimpleFin : (Q.filter fun p : Finset (Fin 30) => p.card = 3) = (simple.map List.toFinset).toFinset := by
      ext s
      simp only [hQ, Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_cons]
      constructor
      · rintro ⟨⟨l, hl, rfl⟩, hc⟩
        rw [List.toFinset_card_of_nodup (hnd l (by rcases hl with rfl | rfl | hl <;> simp [*]))] at hc
        rcases hl with rfl | rfl | hl
        · omega
        · omega
        · exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        refine ⟨⟨l, Or.inr (Or.inr hl), rfl⟩, ?_⟩
        rw [List.toFinset_card_of_nodup (hnd l (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)))]
        exact hsall l hl
    have hcosts : ∀ m, m ∈ (handSides Q I.toFinset).image (sideCost w univ) ↔
        m ∈ tieBreakCosts w I J simple := by
      intro m
      constructor
      · intro hm
        obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
        set C := simple.filter fun l => decide (l.toFinset ∈ S) with hCdef
        have hCsub : C.Sublist simple := List.filter_sublist
        have hSC : (C.map List.toFinset).toFinset = S := by
          ext s
          simp only [hCdef, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro ⟨l, ⟨-, hlS⟩, rfl⟩
            exact hlS
          · intro hs
            have hs' := (Finset.mem_powersetCard.mp hS).1 hs
            rw [hsimpleFin] at hs'
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs')
            exact ⟨l, ⟨hl, hs⟩, rfl⟩
        have hClen : C.length = 3 := by
          have hnd' : (C.map List.toFinset).Nodup := hsimplend.sublist (hCsub.map _)
          calc C.length = (C.map List.toFinset).length := (List.length_map _).symm
            _ = (C.map List.toFinset).toFinset.card := (List.toFinset_card_of_nodup hnd').symm
            _ = 3 := by rw [hSC]; exact (Finset.mem_powersetCard.mp hS).2
        obtain ⟨hside, hcost⟩ := sideCost_of_choice (w := w) hflat hlen hCsub
        rw [← hSC, hside, hcost]
        exact List.mem_map.mpr ⟨C, List.mem_sublistsLen.mpr ⟨hCsub, hClen⟩, rfl⟩
      · intro hm
        obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hm
        obtain ⟨hCsub, hClen⟩ := List.mem_sublistsLen.mp hC
        obtain ⟨hside, hcost⟩ := sideCost_of_choice (w := w) hflat hlen hCsub
        refine Finset.mem_image.mpr ⟨(I ++ C.flatten).toFinset, ?_, hcost⟩
        rw [← hside]
        refine Finset.mem_image.mpr ⟨(C.map List.toFinset).toFinset, ?_, rfl⟩
        rw [Finset.mem_powersetCard, hsimpleFin]
        refine ⟨fun s hs => ?_, ?_⟩
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
          exact List.mem_toFinset.mpr (List.mem_map_of_mem (hCsub.subset hl))
        · rw [List.toFinset_card_of_nodup (hsimplend.sublist (hCsub.map _)), List.length_map, hClen]
    refine tieBreak_isLeast fullRepertoire hP hI w ⟨?_, fun m hm => ?_⟩
    · exact Finset.mem_coe.mpr ((hcosts n).mpr hcont)
    · exact hlow m ((hcosts m).mp (Finset.mem_coe.mp hm))
  | [], h => simp [checkTieBreak] at h
  | [_], h => simp [checkTieBreak] at h

end Sound

end Fern.Solver
