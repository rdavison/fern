module
public import Fern.Ortholinear.Pieces
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Cast.WithTop

/-!
# Reference specification of the exact search

Plain `Finset` versions of the search the fast solver performs, with no concern for speed, each
proved to find the true minimum. The implementation in `FernImpl` is later proved equal to these.

Keys are `Fin 30`. Every search peels the *highest* remaining key first, the order in which the
implementation reads bits.
-/

@[expose] public section

namespace Fern.Solver

open Finset Fern.Ortholinear

/-- `Q` partitions `T` into blocks of three. -/
structure IsTriplePartition (T : Finset (Fin 30)) (Q : Finset (Finset (Fin 30))) : Prop where
  disjoint : (Q : Set (Finset (Fin 30))).PairwiseDisjoint id
  cover : Q.biUnion id = T
  sizes : ∀ q ∈ Q, q.card = 3

variable (w : Fin 30 → Fin 30 → ℕ)

/-- The cheapest partition of `T` into triples, or `⊤` when `T` has none. `fuel` bounds the number
of triples; the highest remaining key is always placed first. -/
def bestTriplesTop : ℕ → Finset (Fin 30) → WithTop ℕ
  | 0, T => if T = ∅ then 0 else ⊤
  | fuel + 1, T =>
    if h : T.Nonempty then
      ((T.erase (T.max' h)).powersetCard 2).inf fun bc =>
        (pieceWeight w (insert (T.max' h) bc) : WithTop ℕ) +
          bestTriplesTop fuel (T \ insert (T.max' h) bc)
    else 0

variable {w}

theorem IsTriplePartition.empty : IsTriplePartition ∅ ∅ where
  disjoint := by simp
  cover := by simp
  sizes := by simp

/-- The triple holding the highest key, and the partition of what remains. -/
theorem IsTriplePartition.split_max {T : Finset (Fin 30)} {Q : Finset (Finset (Fin 30))}
    (hQ : IsTriplePartition T Q) (h : T.Nonempty) :
    ∃ q ∈ Q, T.max' h ∈ q ∧ IsTriplePartition (T \ q) (Q.erase q) := by
  have ha : T.max' h ∈ Q.biUnion id := hQ.cover ▸ T.max'_mem h
  obtain ⟨q, hq, haq⟩ := Finset.mem_biUnion.mp ha
  refine ⟨q, hq, haq, ⟨?_, ?_, ?_⟩⟩
  · exact hQ.disjoint.subset (Finset.coe_subset.mpr (Finset.erase_subset q Q))
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_erase, id, Finset.mem_sdiff]
    constructor
    · rintro ⟨r, ⟨hrq, hr⟩, hxr⟩
      refine ⟨hQ.cover ▸ Finset.mem_biUnion.mpr ⟨r, hr, hxr⟩, fun hxq => ?_⟩
      exact Finset.disjoint_left.mp (hQ.disjoint (Finset.mem_coe.mpr hr) (Finset.mem_coe.mpr hq) hrq)
        hxr hxq
    · rintro ⟨hxT, hxq⟩
      obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp (hQ.cover.symm ▸ hxT)
      exact ⟨r, ⟨fun e => hxq (e ▸ hxr), hr⟩, hxr⟩
  · exact fun r hr => hQ.sizes r (Finset.mem_of_mem_erase hr)

theorem IsTriplePartition.subset {T : Finset (Fin 30)} {Q : Finset (Finset (Fin 30))}
    (hQ : IsTriplePartition T Q) {q : Finset (Fin 30)} (hq : q ∈ Q) : q ⊆ T :=
  hQ.cover ▸ Finset.subset_biUnion_of_mem id hq

theorem pieceCost_insert {Q : Finset (Finset (Fin 30))} {q : Finset (Fin 30)} (h : q ∉ Q) :
    pieceCost w (insert q Q) = pieceWeight w q + pieceCost w Q := by
  rw [pieceCost, Finset.sum_insert h]
  rfl

theorem pieceCost_erase {Q : Finset (Finset (Fin 30))} {q : Finset (Fin 30)} (h : q ∈ Q) :
    pieceCost w Q = pieceWeight w q + pieceCost w (Q.erase q) := by
  rw [pieceCost, pieceCost, Finset.add_sum_erase Q _ h]

/-- The cheapest triple partition is no dearer than any triple partition. -/
theorem bestTriplesTop_le : ∀ (fuel : ℕ) (T : Finset (Fin 30)) (Q : Finset (Finset (Fin 30))),
    T.card ≤ 3 * fuel → IsTriplePartition T Q → bestTriplesTop w fuel T ≤ pieceCost w Q
  | 0, T, Q, hfuel, _ => by
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [bestTriplesTop, hT]
  | fuel + 1, T, Q, hfuel, hQ => by
    by_cases h : T.Nonempty
    · rw [bestTriplesTop, dif_pos h]
      obtain ⟨q, hq, haq, hrest⟩ := hQ.split_max h
      have hqT := hQ.subset hq
      have hq3 := hQ.sizes q hq
      have hbc : q.erase (T.max' h) ∈ (T.erase (T.max' h)).powersetCard 2 := by
        rw [Finset.mem_powersetCard, Finset.card_erase_of_mem haq, hq3]
        exact ⟨Finset.erase_subset_erase _ hqT, rfl⟩
      have hins : insert (T.max' h) (q.erase (T.max' h)) = q := Finset.insert_erase haq
      have hcard : (T \ q).card ≤ 3 * fuel := by
        rw [Finset.card_sdiff_of_subset hqT, hq3]; omega
      refine le_trans (Finset.inf_le (f := fun bc =>
        (pieceWeight w (insert (T.max' h) bc) : WithTop ℕ) +
          bestTriplesTop w fuel (T \ insert (T.max' h) bc)) hbc) ?_
      show (pieceWeight w (insert (T.max' h) (q.erase (T.max' h))) : WithTop ℕ) +
          bestTriplesTop w fuel (T \ insert (T.max' h) (q.erase (T.max' h))) ≤ _
      rw [hins]
      calc (pieceWeight w q : WithTop ℕ) + bestTriplesTop w fuel (T \ q)
          ≤ (pieceWeight w q : WithTop ℕ) + (pieceCost w (Q.erase q) : WithTop ℕ) :=
            add_le_add le_rfl (bestTriplesTop_le fuel (T \ q) (Q.erase q) hcard hrest)
        _ = (pieceCost w Q : WithTop ℕ) := by rw [pieceCost_erase hq]; push_cast; rfl
    · rw [bestTriplesTop, dif_neg h]
      exact bot_le

/-- A finite value is the cost of an actual triple partition. -/
theorem bestTriplesTop_achieved : ∀ (fuel : ℕ) (T : Finset (Fin 30)) (n : ℕ),
    bestTriplesTop w fuel T = n → ∃ Q, IsTriplePartition T Q ∧ pieceCost w Q = n
  | 0, T, n, hn => by
    by_cases hT : T = ∅
    · subst hT
      have hn0 : n = 0 := by simp [bestTriplesTop] at hn; exact_mod_cast hn.symm
      exact ⟨∅, IsTriplePartition.empty, by rw [pieceCost, Finset.sum_empty, hn0]⟩
    · simp [bestTriplesTop, hT] at hn
  | fuel + 1, T, n, hn => by
    by_cases h : T.Nonempty
    · rw [bestTriplesTop, dif_pos h] at hn
      set a := T.max' h
      set S := (T.erase a).powersetCard 2
      have hS : S.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.inf_empty] at hn
        exact WithTop.top_ne_coe hn
      obtain ⟨bc, hbc, heq⟩ := Finset.exists_mem_eq_inf S hS fun bc =>
        (pieceWeight w (insert a bc) : WithTop ℕ) + bestTriplesTop w fuel (T \ insert a bc)
      rw [heq] at hn
      obtain ⟨hbcsub, hbc2⟩ := Finset.mem_powersetCard.mp hbc
      set q := insert a bc
      have hrest_ne : bestTriplesTop w fuel (T \ q) ≠ ⊤ := by
        intro htop
        rw [htop, WithTop.add_top] at hn
        exact WithTop.top_ne_coe hn
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hrest_ne
      obtain ⟨Q', hQ', hcost⟩ := bestTriplesTop_achieved fuel (T \ q) m hm.symm
      have haT : a ∈ T := T.max'_mem h
      have hanot : a ∉ bc := fun hab => by simpa using hbcsub hab
      have hqT : q ⊆ T := Finset.insert_subset haT (hbcsub.trans (Finset.erase_subset a T))
      have hq3 : q.card = 3 := by rw [Finset.card_insert_of_notMem hanot, hbc2]
      have hqnot : q ∉ Q' := fun hq => by
        have := hQ'.subset hq (Finset.mem_insert_self a bc)
        simp [q] at this
      refine ⟨insert q Q', ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [Finset.coe_insert]
        refine hQ'.disjoint.insert fun r hr _ => ?_
        exact Finset.disjoint_of_subset_right (hQ'.subset (Finset.mem_coe.mp hr))
          Finset.disjoint_sdiff
      · rw [Finset.biUnion_insert, hQ'.cover]
        exact Finset.union_sdiff_of_subset hqT
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hq3
        · exact hQ'.sizes r hr
      · rw [pieceCost_insert hqnot, hcost]
        rw [← hm] at hn
        simp only [Nat.cast_withTop] at hn
        rw [← WithTop.coe_add, WithTop.coe_eq_coe] at hn
        exact hn
    · rw [bestTriplesTop, dif_neg h] at hn
      have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst hT
      have hn0 : n = 0 := by exact_mod_cast hn.symm
      exact ⟨∅, IsTriplePartition.empty, by rw [pieceCost, Finset.sum_empty, hn0]⟩

/-- A set whose size is a multiple of three always has a finite cheapest triple partition. -/
theorem bestTriplesTop_ne_top : ∀ (fuel : ℕ) (T : Finset (Fin 30)),
    T.card ≤ 3 * fuel → 3 ∣ T.card → bestTriplesTop w fuel T ≠ ⊤
  | 0, T, hfuel, _ => by
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [bestTriplesTop, hT]
  | fuel + 1, T, hfuel, hdvd => by
    by_cases h : T.Nonempty
    · rw [bestTriplesTop, dif_pos h]
      have hpos := Finset.card_pos.mpr h
      have h3 : 3 ≤ T.card := by omega
      have herase : 2 ≤ (T.erase (T.max' h)).card := by
        rw [Finset.card_erase_of_mem (T.max'_mem h)]; omega
      obtain ⟨bc, hbc⟩ := Finset.powersetCard_nonempty.mpr herase
      obtain ⟨hbcsub, hbc2⟩ := Finset.mem_powersetCard.mp hbc
      have hanot : T.max' h ∉ bc := fun hab => by simpa using hbcsub hab
      have hqT : insert (T.max' h) bc ⊆ T :=
        Finset.insert_subset (T.max'_mem h) (hbcsub.trans (Finset.erase_subset _ T))
      have hq3 : (insert (T.max' h) bc).card = 3 := by
        rw [Finset.card_insert_of_notMem hanot, hbc2]
      have hrest := bestTriplesTop_ne_top fuel (T \ insert (T.max' h) bc)
        (by rw [Finset.card_sdiff_of_subset hqT, hq3]; omega)
        (by rw [Finset.card_sdiff_of_subset hqT, hq3]; omega)
      refine ne_top_of_le_ne_top ?_ (Finset.inf_le hbc)
      exact WithTop.add_ne_top.mpr ⟨WithTop.coe_ne_top, hrest⟩
    · rw [bestTriplesTop, dif_neg h]
      exact WithTop.coe_ne_top

theorem IsTriplePartition.card_eq {T : Finset (Fin 30)} {Q : Finset (Finset (Fin 30))}
    (hQ : IsTriplePartition T Q) : T.card = 3 * Q.card := by
  rw [← hQ.cover, Finset.card_biUnion hQ.disjoint,
    Finset.sum_congr rfl fun q hq => (hQ.sizes q hq : (id q).card = 3), Finset.sum_const,
    smul_eq_mul, Nat.mul_comm]

theorem exists_natCast_of_ne_top {x : WithTop ℕ} (h : x ≠ ⊤) : ∃ n : ℕ, x = (n : WithTop ℕ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨n, by rw [← hn, Nat.cast_withTop]⟩

theorem eq_untopD_of_ne_top {x : WithTop ℕ} (h : x ≠ ⊤) :
    x = ((WithTop.untopD 0 x : ℕ) : WithTop ℕ) := by
  obtain ⟨n, rfl⟩ := exists_natCast_of_ne_top h
  rw [Nat.cast_withTop, WithTop.untopD_coe]
  exact (Nat.cast_withTop n).symm

/-- Enough fuel always gives the same answer. -/
theorem bestTriplesTop_fuel_irrel {T : Finset (Fin 30)} {f₁ f₂ : ℕ} (h₁ : T.card ≤ 3 * f₁)
    (h₂ : T.card ≤ 3 * f₂) : bestTriplesTop w f₁ T = bestTriplesTop w f₂ T := by
  have claim : ∀ {f g : ℕ}, T.card ≤ 3 * f → T.card ≤ 3 * g →
      bestTriplesTop w f T ≠ ⊤ → bestTriplesTop w g T ≤ bestTriplesTop w f T := fun _ hg hne => by
    obtain ⟨n, hn⟩ := exists_natCast_of_ne_top hne
    obtain ⟨Q, hQ, hc⟩ := bestTriplesTop_achieved _ T n hn
    rw [hn, ← hc]
    exact bestTriplesTop_le _ T Q hg hQ
  by_cases h1 : bestTriplesTop w f₁ T = ⊤
  · by_cases h2 : bestTriplesTop w f₂ T = ⊤
    · rw [h1, h2]
    · have := claim h₂ h₁ h2
      rw [h1] at this
      exact absurd (top_le_iff.mp this) h2
  · by_cases h2 : bestTriplesTop w f₂ T = ⊤
    · have := claim h₁ h₂ h1
      rw [h2] at this
      exact absurd (top_le_iff.mp this) h1
    · exact le_antisymm (claim h₂ h₁ h2) (claim h₁ h₂ h1)

/-- The cost of the cheapest partition of `T` into triples, for `T` whose size is a multiple of
three. -/
def bestTriplesRef (w : Fin 30 → Fin 30 → ℕ) (T : Finset (Fin 30)) : ℕ :=
  WithTop.untopD 0 (bestTriplesTop w T.card T)

theorem bestTriplesTop_eq_ref {T : Finset (Fin 30)} {fuel : ℕ} (hfuel : T.card ≤ 3 * fuel)
    (h3 : 3 ∣ T.card) : bestTriplesTop w fuel T = bestTriplesRef w T := by
  rw [bestTriplesTop_fuel_irrel hfuel (by omega : T.card ≤ 3 * T.card), bestTriplesRef]
  exact eq_untopD_of_ne_top (bestTriplesTop_ne_top _ T (by omega) h3)

/-- `bestTriplesRef` is the least cost of a partition into triples. -/
theorem bestTriplesRef_isLeast {T : Finset (Fin 30)} (h3 : 3 ∣ T.card) :
    IsLeast {c | ∃ Q, IsTriplePartition T Q ∧ pieceCost w Q = c} (bestTriplesRef w T) := by
  have heq := bestTriplesTop_eq_ref (w := w) (fuel := T.card) (by omega) h3
  refine ⟨bestTriplesTop_achieved _ T _ heq, fun c ⟨Q, hQ, hc⟩ => ?_⟩
  have := bestTriplesTop_le (w := w) T.card T Q (by omega) hQ
  rw [heq, hc] at this
  exact_mod_cast this

/-- One step of the recurrence the implementation computes: place the highest key with its
cheapest pair, and recurse on the rest. -/
theorem bestTriplesRef_step {T : Finset (Fin 30)} (h : T.Nonempty) (h3 : 3 ∣ T.card) :
    (bestTriplesRef w T : WithTop ℕ) = ((T.erase (T.max' h)).powersetCard 2).inf fun bc =>
      ((pieceWeight w (insert (T.max' h) bc) + bestTriplesRef w (T \ insert (T.max' h) bc) : ℕ) :
        WithTop ℕ) := by
  have hpos := Finset.card_pos.mpr h
  obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
  rw [← bestTriplesTop_eq_ref (fuel := T.card) (by omega) h3, hk, bestTriplesTop, dif_pos h]
  refine Finset.inf_congr rfl fun bc hbc => ?_
  obtain ⟨hbcsub, hbc2⟩ := Finset.mem_powersetCard.mp hbc
  have hanot : T.max' h ∉ bc := fun hab => by simpa using hbcsub hab
  have hqT : insert (T.max' h) bc ⊆ T :=
    Finset.insert_subset (T.max'_mem h) (hbcsub.trans (Finset.erase_subset _ T))
  have hq3 : (insert (T.max' h) bc).card = 3 := by rw [Finset.card_insert_of_notMem hanot, hbc2]
  have hrest : (T \ insert (T.max' h) bc).card = T.card - 3 := by
    rw [Finset.card_sdiff_of_subset hqT, hq3]
  rw [bestTriplesTop_eq_ref (by rw [hrest]; omega) (by rw [hrest]; omega)]
  push_cast
  rfl

/-! ### Splitting the index keys -/

/-- `A` and `B` split `S` into two blocks of six. -/
structure IsSixSplit (S A B : Finset (Fin 30)) : Prop where
  disjoint : Disjoint A B
  union : A ∪ B = S
  card_left : A.card = 6
  card_right : B.card = 6

theorem IsSixSplit.symm {S A B : Finset (Fin 30)} (h : IsSixSplit S A B) : IsSixSplit S B A :=
  ⟨h.disjoint.symm, by rw [Finset.union_comm, h.union], h.card_right, h.card_left⟩

variable (w) in
/-- The cheapest split of `S` into two blocks of six. The block holding the highest key is chosen
by picking its other five keys, the order in which the implementation searches. -/
def indexCostTop (S : Finset (Fin 30)) : WithTop ℕ :=
  if h : S.Nonempty then
    ((S.erase (S.max' h)).powersetCard 5).inf fun A =>
      ((pieceWeight w (insert (S.max' h) A) + pieceWeight w (S \ insert (S.max' h) A) : ℕ) :
        WithTop ℕ)
  else ⊤

theorem indexCostTop_le_of_mem {S A B : Finset (Fin 30)} (hAB : IsSixSplit S A B)
    (h : S.Nonempty) (ha : S.max' h ∈ A) :
    indexCostTop w S ≤ ((pieceWeight w A + pieceWeight w B : ℕ) : WithTop ℕ) := by
  rw [indexCostTop, dif_pos h]
  have hAS : A ⊆ S := hAB.union ▸ Finset.subset_union_left
  have hmem : A.erase (S.max' h) ∈ (S.erase (S.max' h)).powersetCard 5 := by
    rw [Finset.mem_powersetCard, Finset.card_erase_of_mem ha, hAB.card_left]
    exact ⟨Finset.erase_subset_erase _ hAS, rfl⟩
  have hins : insert (S.max' h) (A.erase (S.max' h)) = A := Finset.insert_erase ha
  have hB : S \ A = B := by
    rw [← hAB.union, Finset.union_sdiff_cancel_left hAB.disjoint]
  refine le_trans (Finset.inf_le (f := fun A =>
    ((pieceWeight w (insert (S.max' h) A) + pieceWeight w (S \ insert (S.max' h) A) : ℕ) :
      WithTop ℕ)) hmem) ?_
  show (((pieceWeight w (insert (S.max' h) (A.erase (S.max' h))) +
    pieceWeight w (S \ insert (S.max' h) (A.erase (S.max' h))) : ℕ) : WithTop ℕ) ≤ _)
  rw [hins, hB]

/-- The cheapest index split is no dearer than any split. -/
theorem indexCostTop_le {S A B : Finset (Fin 30)} (hAB : IsSixSplit S A B) :
    indexCostTop w S ≤ ((pieceWeight w A + pieceWeight w B : ℕ) : WithTop ℕ) := by
  have h : S.Nonempty := by
    rw [← hAB.union]
    exact Finset.Nonempty.inl (Finset.card_pos.mp (by rw [hAB.card_left]; decide))
  have hmax : S.max' h ∈ A ∪ B := hAB.union ▸ S.max'_mem h
  rcases Finset.mem_union.mp hmax with ha | hb
  · exact indexCostTop_le_of_mem hAB h ha
  · rw [Nat.add_comm]
    exact indexCostTop_le_of_mem hAB.symm h hb

/-- A finite index cost is the cost of an actual split. -/
theorem indexCostTop_achieved {S : Finset (Fin 30)} (hS : S.card = 12) {n : ℕ}
    (hn : indexCostTop w S = n) :
    ∃ A B, IsSixSplit S A B ∧ pieceWeight w A + pieceWeight w B = n := by
  have h : S.Nonempty := Finset.card_pos.mp (by omega)
  rw [indexCostTop, dif_pos h] at hn
  set a := S.max' h
  set U := (S.erase a).powersetCard 5
  have hU : U.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.inf_empty] at hn
    exact WithTop.top_ne_coe (by rw [Nat.cast_withTop] at hn; exact hn)
  obtain ⟨A', hA', heq⟩ := Finset.exists_mem_eq_inf U hU fun A =>
    ((pieceWeight w (insert a A) + pieceWeight w (S \ insert a A) : ℕ) : WithTop ℕ)
  rw [heq] at hn
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA'
  have hanot : a ∉ A' := fun ha => by simpa using hsub ha
  have hAS : insert a A' ⊆ S :=
    Finset.insert_subset (S.max'_mem h) (hsub.trans (Finset.erase_subset a S))
  have hA6 : (insert a A').card = 6 := by rw [Finset.card_insert_of_notMem hanot, hcard]
  refine ⟨insert a A', S \ insert a A', ⟨Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hAS,
    hA6, by rw [Finset.card_sdiff_of_subset hAS, hA6, hS]⟩, ?_⟩
  exact_mod_cast hn

theorem indexCostTop_ne_top {S : Finset (Fin 30)} (hS : S.card = 12) : indexCostTop w S ≠ ⊤ := by
  have h : S.Nonempty := Finset.card_pos.mp (by omega)
  rw [indexCostTop, dif_pos h]
  obtain ⟨A, hA⟩ := Finset.powersetCard_nonempty.mpr
    (by rw [Finset.card_erase_of_mem (S.max'_mem h), hS]; decide : 5 ≤ (S.erase (S.max' h)).card)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (Finset.inf_le hA)

/-! ### The whole search -/

variable (w) in
/-- The cheapest piece-set: choose the twelve index keys, split them, and partition the other
eighteen into triples. -/
def optimumTop : WithTop ℕ :=
  ((univ : Finset (Fin 30)).powersetCard 12).inf fun S =>
    indexCostTop w S + bestTriplesTop w 6 (univ \ S)

variable (w) in
/-- The least same-finger cost over all piece-sets of thirty keys. -/
def optimumRef : ℕ := WithTop.untopD 0 (optimumTop w)

theorem card_compl_of_card_twelve {S : Finset (Fin 30)} (hS : S.card = 12) :
    ((univ : Finset (Fin 30)) \ S).card = 18 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin, hS]

theorem optimumTop_le {P : Finset (Finset (Fin 30))} (hP : IsPieceSet (univ : Finset (Fin 30)) P) :
    optimumTop w ≤ (pieceCost w P : WithTop ℕ) := by
  obtain ⟨A, B, hne, hAB⟩ := Finset.card_eq_two.mp hP.index_count
  have hA : A ∈ P.filter (·.card = 6) := hAB ▸ Finset.mem_insert_self A {B}
  have hB : B ∈ P.filter (·.card = 6) :=
    hAB ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self B)
  obtain ⟨hAP, hA6⟩ := Finset.mem_filter.mp hA
  obtain ⟨hBP, hB6⟩ := Finset.mem_filter.mp hB
  have hdisj : Disjoint A B := hP.disjoint (Finset.mem_coe.mpr hAP) (Finset.mem_coe.mpr hBP) hne
  have hS : (A ∪ B).card = 12 := by rw [Finset.card_union_of_disjoint hdisj, hA6, hB6]
  have hsplit : IsSixSplit (A ∪ B) A B := ⟨hdisj, rfl, hA6, hB6⟩
  have htrip : IsTriplePartition (univ \ (A ∪ B)) (P.filter (·.card = 3)) := by
    refine ⟨hP.disjoint.subset (Finset.coe_subset.mpr (Finset.filter_subset _ P)), ?_,
      fun q hq => (Finset.mem_filter.mp hq).2⟩
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, id, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨q, ⟨hqP, hq3⟩, hxq⟩ hxS
      have away : ∀ C ∈ P, C.card = 6 → x ∉ C := fun C hC hC6 hxC =>
        Finset.disjoint_left.mp (hP.disjoint (Finset.mem_coe.mpr hqP) (Finset.mem_coe.mpr hC)
          fun e => by rw [e] at hq3; omega) hxq hxC
      rcases Finset.mem_union.mp hxS with hxA | hxB
      · exact away A hAP hA6 hxA
      · exact away B hBP hB6 hxB
    · intro hxS
      have hx : x ∈ P.biUnion id := by rw [hP.cover]; exact Finset.mem_univ x
      obtain ⟨p, hpP, hxp⟩ := Finset.mem_biUnion.mp hx
      refine ⟨p, ⟨hpP, ?_⟩, hxp⟩
      rcases hP.sizes p hpP with h3 | h6
      · exact h3
      · have hp6 : p ∈ P.filter (·.card = 6) := Finset.mem_filter.mpr ⟨hpP, h6⟩
        rw [hAB] at hp6
        rcases Finset.mem_insert.mp hp6 with rfl | hpB
        · exact absurd (Finset.mem_union_left _ hxp) hxS
        · rw [Finset.mem_singleton] at hpB
          subst hpB
          exact absurd (Finset.mem_union_right _ hxp) hxS
  have hcost : pieceCost w P =
      (pieceWeight w A + pieceWeight w B) + pieceCost w (P.filter (·.card = 3)) := by
    rw [pieceCost_split hP, hAB, Finset.sum_pair hne]
    rfl
  have hmem : A ∪ B ∈ (univ : Finset (Fin 30)).powersetCard 12 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩
  calc optimumTop w ≤ indexCostTop w (A ∪ B) + bestTriplesTop w 6 (univ \ (A ∪ B)) :=
        Finset.inf_le (f := fun S => indexCostTop w S + bestTriplesTop w 6 (univ \ S)) hmem
    _ ≤ ((pieceWeight w A + pieceWeight w B : ℕ) : WithTop ℕ) +
          (pieceCost w (P.filter (·.card = 3)) : WithTop ℕ) :=
        add_le_add (indexCostTop_le hsplit)
          (bestTriplesTop_le 6 _ _ (by rw [card_compl_of_card_twelve hS]) htrip)
    _ = (pieceCost w P : WithTop ℕ) := by rw [hcost]; push_cast; rfl

theorem optimumTop_ne_top : optimumTop w ≠ ⊤ := by
  rw [optimumTop]
  obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr
    (by simp : 12 ≤ (univ : Finset (Fin 30)).card)
  have hS12 := (Finset.mem_powersetCard.mp hS).2
  have hcard := card_compl_of_card_twelve hS12
  refine ne_top_of_le_ne_top ?_ (Finset.inf_le hS)
  exact WithTop.add_ne_top.mpr ⟨indexCostTop_ne_top hS12,
    bestTriplesTop_ne_top 6 _ (by omega) (by omega)⟩

theorem optimumTop_achieved {n : ℕ} (hn : optimumTop w = n) :
    ∃ P, IsPieceSet (univ : Finset (Fin 30)) P ∧ pieceCost w P = n := by
  rw [optimumTop] at hn
  have hU : ((univ : Finset (Fin 30)).powersetCard 12).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simp)
  obtain ⟨S, hSU, heq⟩ := Finset.exists_mem_eq_inf _ hU fun S =>
    indexCostTop w S + bestTriplesTop w 6 (univ \ S)
  rw [heq] at hn
  have hS := (Finset.mem_powersetCard.mp hSU).2
  have hcard := card_compl_of_card_twelve hS
  obtain ⟨i, hi⟩ := exists_natCast_of_ne_top (indexCostTop_ne_top (w := w) hS)
  obtain ⟨t, ht⟩ := exists_natCast_of_ne_top
    (bestTriplesTop_ne_top (w := w) 6 (univ \ S) (by omega) (by omega))
  obtain ⟨A, B, hsplit, hABc⟩ := indexCostTop_achieved hS hi
  obtain ⟨Q, hQ, hQc⟩ := bestTriplesTop_achieved 6 _ t ht
  have hnit : i + t = n := by
    rw [hi, ht] at hn
    exact_mod_cast hn
  have hAS : A ⊆ S := hsplit.union ▸ Finset.subset_union_left
  have hBS : B ⊆ S := hsplit.union ▸ Finset.subset_union_right
  have hQfar : ∀ q ∈ Q, ∀ C ⊆ S, Disjoint C q := fun q hq C hC =>
    Finset.disjoint_of_subset_left hC
      (Finset.disjoint_of_subset_right (hQ.subset hq) Finset.disjoint_sdiff)
  have hAQ : A ∉ Q := fun h => by have := hQ.sizes A h; rw [hsplit.card_left] at this; omega
  have hBQ : B ∉ Q := fun h => by have := hQ.sizes B h; rw [hsplit.card_right] at this; omega
  have hAB : A ≠ B := fun h => by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hsplit.card_left]; decide : 0 < A.card)
    exact Finset.disjoint_left.mp hsplit.disjoint hx (h ▸ hx)
  have hAnot : A ∉ insert B Q := by simp [hAB, hAQ]
  have hQcard : Q.card = 6 := by have := hQ.card_eq; rw [hcard] at this; omega
  refine ⟨insert A (insert B Q), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.coe_insert, Finset.coe_insert]
    refine (hQ.disjoint.insert fun q hq _ => hQfar q (Finset.mem_coe.mp hq) B hBS).insert ?_
    intro r hr _
    rcases Set.mem_insert_iff.mp hr with rfl | hrQ
    · exact hsplit.disjoint
    · exact hQfar r (Finset.mem_coe.mp hrQ) A hAS
  · rw [Finset.biUnion_insert, Finset.biUnion_insert, hQ.cover]
    simp only [id]
    rw [← Finset.union_assoc, hsplit.union, Finset.union_sdiff_of_subset (Finset.subset_univ S)]
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inr hsplit.card_left
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inr hsplit.card_right
    · exact Or.inl (hQ.sizes p hp)
  · rw [Finset.filter_insert, Finset.filter_insert, if_neg (by rw [hsplit.card_left]; decide),
      if_neg (by rw [hsplit.card_right]; decide), Finset.filter_true_of_mem hQ.sizes, hQcard]
  · rw [Finset.filter_insert, Finset.filter_insert, if_pos hsplit.card_left,
      if_pos hsplit.card_right,
      Finset.filter_false_of_mem fun q hq => by rw [hQ.sizes q hq]; decide,
      Finset.card_insert_of_notMem (by simp [hAB]), Finset.card_insert_of_notMem (Finset.notMem_empty B),
      Finset.card_empty]
  · rw [pieceCost_insert hAnot, pieceCost_insert hBQ, hQc, ← Nat.add_assoc, hABc, hnit]

theorem optimumTop_eq_ref : optimumTop w = optimumRef w := eq_untopD_of_ne_top optimumTop_ne_top

/-- The reference optimum is the least cost over all piece-sets of thirty keys. -/
theorem optimumRef_isLeast :
    IsLeast (Set.range fun P : {P // IsPieceSet (univ : Finset (Fin 30)) P} => pieceCost w P.val)
      (optimumRef w) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hc⟩ := optimumTop_achieved (w := w) optimumTop_eq_ref
    exact ⟨⟨P, hP⟩, hc⟩
  · rintro _ ⟨⟨P, hP⟩, rfl⟩
    have := optimumTop_le (w := w) hP
    rw [optimumTop_eq_ref] at this
    exact_mod_cast this

/-- The thirty keys `Fin 30` as a repertoire. -/
def fullRepertoire : Repertoire (Fin 30) := ⟨univ, by simp⟩

/-- The reference optimum is the least same-finger weight over every layout of thirty keys. -/
theorem optimumRef_isLeast_layouts :
    IsLeast (Set.range fun L : LayoutOn fullRepertoire => L.val.sfbWeight w) (optimumRef w) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨P, hP⟩, hc⟩ := (optimumRef_isLeast (w := w)).1
    obtain ⟨L, hL⟩ := exists_layoutOn_columns_eq fullRepertoire hP
    exact ⟨L, by simp only [Layout.sfbWeight_eq_pieceCost, hL]; exact hc⟩
  · rintro _ ⟨L, rfl⟩
    simp only [Layout.sfbWeight_eq_pieceCost]
    exact (optimumRef_isLeast (w := w)).2 ⟨⟨L.val.columns, L.columns_isPieceSet⟩, rfl⟩

end Fern.Solver
