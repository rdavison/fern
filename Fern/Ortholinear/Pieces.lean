module
public import Fern.Ortholinear.Symmetry
public import Fern.Ortholinear.Corpus

/-!
# Pieces

Up to equivalence a layout is a *piece-set*: its keys split into six unordered blocks of three and
two unordered blocks of six, with no memory of rows or of which column went where. `Layout.columns`
already is that object, and `Layout.Equivalent` is defined as having the same one. This file makes
it the central object: the same-finger cost is a sum over pieces, it splits into index and simple
pieces, and every piece-set is realised by some layout, so equivalence classes and piece-sets are in
bijection.
-/

@[expose] public section

namespace Fern.Ortholinear

open Finset

variable {K : Type} [DecidableEq K]

/-- Disjoint pieces covering `s`: six of size three and two of size six. -/
structure IsPieceSet (s : Finset K) (P : Finset (Finset K)) : Prop where
  disjoint : (P : Set (Finset K)).PairwiseDisjoint id
  cover : P.biUnion id = s
  sizes : ∀ p ∈ P, p.card = 3 ∨ p.card = 6
  simple_count : (P.filter (·.card = 3)).card = 6
  index_count : (P.filter (·.card = 6)).card = 2

/-- The same-finger weight of one piece: every ordered pair of distinct keys in it. -/
def pieceWeight (w : K → K → ℕ) (p : Finset K) : ℕ := ∑ x ∈ p.offDiag, w x.1 x.2

/-- The same-finger weight of a piece-set. -/
def pieceCost (w : K → K → ℕ) (P : Finset (Finset K)) : ℕ := ∑ p ∈ P, pieceWeight w p

/-- The same-finger weight of a layout under a bigram weighting. -/
def Layout.sfbWeight (L : Layout K) (w : K → K → ℕ) : ℕ := ∑ x ∈ L.sfbs, w x.1 x.2

/-- Occurrences of each ordered bigram in a list. -/
def bigramCount (bs : List (Bigram K)) (a b : K) : ℕ := bs.countP fun x => decide (x = (a, b))

omit [DecidableEq K] in
theorem offDiag_disjoint {s t : Finset K} (h : Disjoint s t) : Disjoint s.offDiag t.offDiag :=
  Finset.disjoint_left.mpr fun _ hs ht =>
    Finset.disjoint_left.mp h (Finset.mem_offDiag.mp hs).1 (Finset.mem_offDiag.mp ht).1

theorem Layout.columns_pairwiseDisjoint (L : Layout K) :
    (L.columns : Set (Finset K)).PairwiseDisjoint id := by
  intro p hp q hq hpq
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hq
  exact L.columnKeys_disjoint fun h => hpq (by rw [h])

/-- The same-finger weight of a layout is the sum of its pieces' weights. -/
theorem Layout.sfbWeight_eq_pieceCost (L : Layout K) (w : K → K → ℕ) :
    L.sfbWeight w = pieceCost w L.columns := by
  rw [Layout.sfbWeight, Layout.sfbs, Finset.sum_biUnion]
  · rfl
  · intro p hp q hq hpq
    exact offDiag_disjoint (L.columns_pairwiseDisjoint hp hq hpq)

theorem sum_countP_eq_countP (bs : List (Bigram K)) (S : Finset (Bigram K)) :
    ∑ x ∈ S, bs.countP (fun y => decide (y = x)) = bs.countP fun x => decide (x ∈ S) := by
  induction bs with
  | nil => simp
  | cons y t ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, ih, decide_eq_true_eq]
    congr 1
    rw [Finset.sum_ite_eq]

section
attribute [local irreducible] Layout.sfbs

/-- Counting same-finger bigrams in a list is weighting the layout by bigram counts. -/
theorem Layout.sfbCountIn_eq_sfbWeight (L : Layout K) (bs : List (Bigram K)) :
    L.sfbCountIn bs = L.sfbWeight (bigramCount bs) := by
  rw [Layout.sfbWeight, Layout.sfbCountIn]
  simp only [bigramCount, Prod.mk.eta]
  rw [sum_countP_eq_countP]
  rfl

end

/-- The piece cost splits into index pieces and simple pieces, with no cross terms. -/
theorem pieceCost_split {s : Finset K} {P : Finset (Finset K)} (hP : IsPieceSet s P)
    (w : K → K → ℕ) :
    pieceCost w P = (∑ p ∈ P with p.card = 6, pieceWeight w p) +
      ∑ p ∈ P with p.card = 3, pieceWeight w p := by
  rw [pieceCost, ← Finset.sum_filter_add_sum_filter_not P (fun p => p.card = 6)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun p hp => ?_) fun _ _ => rfl
  rcases hP.sizes p hp with h | h <;> simp [h]

theorem Layout.columns_filter_card (L : Layout K) (n : ℕ) :
    L.columns.filter (·.card = n) = (univ.filter fun c => 3 * c.kind.width = n).image L.columnKeys := by
  rw [Layout.columns, Finset.filter_image]
  congr 1
  ext c
  simp [L.columnKeys_card]

/-- A layout's columns form a piece-set of its keys. -/
theorem Layout.columns_isPieceSet (L : Layout K) : IsPieceSet L.usedKeys L.columns where
  disjoint := L.columns_pairwiseDisjoint
  cover := by rw [Layout.columns, Finset.image_biUnion, ← L.columnKeys_cover]; rfl
  sizes := by
    intro p hp
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hp
    rw [L.columnKeys_card]
    cases c.kind <;> simp [ColumnKind.width]
  simple_count := by
    rw [L.columns_filter_card, Finset.card_image_of_injective _ L.columnKeys_injective]
    convert simple_column_count using 2
  index_count := by
    rw [L.columns_filter_card, Finset.card_image_of_injective _ L.columnKeys_injective]
    convert index_column_count using 2

theorem LayoutOn.columns_isPieceSet {R : Repertoire K} (L : LayoutOn R) :
    IsPieceSet R.keys L.val.columns := by
  have h := L.val.columns_isPieceSet
  rwa [L.property] at h

/-! ### Dropping pieces onto the board -/

theorem ColumnKind.eq_index_of_ne_simple {k : ColumnKind} (h : k ≠ .simple) : k = .index := by
  cases k
  · exact absurd rfl h
  · rfl

/-- Pieces placed on the finger columns: each column gets a piece of its size, and no piece twice. -/
structure Placement (P : Finset (Finset K)) where
  piece : ColumnId → Finset K
  mem : ∀ c, piece c ∈ P
  card : ∀ c, (piece c).card = 3 * c.kind.width
  injective : Function.Injective piece

section Realize

variable {s : Finset K} {P : Finset (Finset K)} (hP : IsPieceSet s P)
include hP

theorem IsPieceSet.card_eq_eight : P.card = 8 := by
  have h := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.card = 3)
  have hneg : P.filter (fun p => ¬p.card = 3) = P.filter (·.card = 6) :=
    Finset.filter_congr fun p hp => by rcases hP.sizes p hp with h | h <;> simp [h]
  rw [hneg, hP.simple_count, hP.index_count] at h
  omega

/-- The six simple columns, matched to the six pieces of size three. -/
noncomputable def simplePieceEquiv :
    {c : ColumnId // c.kind = .simple} ≃ {p // p ∈ P.filter (·.card = 3)} :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, hP.simple_count]; decide)

/-- The two index columns, matched to the two pieces of size six. -/
noncomputable def indexPieceEquiv :
    {c : ColumnId // c.kind = .index} ≃ {p // p ∈ P.filter (·.card = 6)} :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, hP.index_count]; decide)

/-- The piece dropped onto each finger column. -/
noncomputable def pieceOf (c : ColumnId) : Finset K :=
  if h : c.kind = .simple then (simplePieceEquiv hP ⟨c, h⟩).val
  else (indexPieceEquiv hP ⟨c, ColumnKind.eq_index_of_ne_simple h⟩).val

theorem pieceOf_mem (c : ColumnId) : pieceOf hP c ∈ P := by
  unfold pieceOf
  split
  · exact (Finset.mem_filter.mp (simplePieceEquiv hP _).property).1
  · exact (Finset.mem_filter.mp (indexPieceEquiv hP _).property).1

theorem card_pieceOf (c : ColumnId) : (pieceOf hP c).card = 3 * c.kind.width := by
  unfold pieceOf
  split
  · rename_i h
    rw [(Finset.mem_filter.mp (simplePieceEquiv hP _).property).2, h]
    rfl
  · rename_i h
    rw [(Finset.mem_filter.mp (indexPieceEquiv hP _).property).2, ColumnKind.eq_index_of_ne_simple h]
    rfl

theorem pieceOf_injective : Function.Injective (pieceOf hP) := by
  intro c d h
  have hk : c.kind = d.kind := ColumnKind.width_injective (by
    have := congrArg Finset.card h
    rw [card_pieceOf, card_pieceOf] at this
    omega)
  unfold pieceOf at h
  by_cases hc : c.kind = .simple
  · have hd : d.kind = .simple := hk ▸ hc
    rw [dif_pos hc, dif_pos hd] at h
    exact congrArg Subtype.val ((simplePieceEquiv hP).injective (Subtype.ext h))
  · have hd : ¬d.kind = .simple := hk ▸ hc
    rw [dif_neg hc, dif_neg hd] at h
    exact congrArg Subtype.val ((indexPieceEquiv hP).injective (Subtype.ext h))

/-- The placement matching the simple and index columns to the pieces arbitrarily. -/
noncomputable def canonicalPlacement : Placement P :=
  ⟨pieceOf hP, pieceOf_mem hP, card_pieceOf hP, pieceOf_injective hP⟩

variable (pl : Placement P)

/-- A placement uses every piece. -/
theorem Placement.image_eq : univ.image pl.piece = P := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hp
    exact pl.mem c
  · rw [Finset.card_image_of_injective _ pl.injective, hP.card_eq_eight]
    decide

/-- Each column's positions, matched to the keys of its piece. -/
noncomputable def fiberPieceEquiv (c : ColumnId) : Fiber c ≃ {k // k ∈ pl.piece c} :=
  Fintype.equivOfCardEq (by rw [card_fiber, Fintype.card_coe, pl.card])

/-- The key placed at each position. -/
noncomputable def realizeFun (p : Position) : K := (fiberPieceEquiv pl (colOf p) ⟨p, rfl⟩).val

omit [DecidableEq K] hP in
theorem realizeFun_eq {c : ColumnId} (x : Fiber c) :
    realizeFun pl x.val = (fiberPieceEquiv pl c x).val := by
  obtain ⟨x, rfl⟩ := x
  rfl

omit [DecidableEq K] hP in
theorem realizeFun_mem (p : Position) : realizeFun pl p ∈ pl.piece (colOf p) :=
  (fiberPieceEquiv pl (colOf p) ⟨p, rfl⟩).property

theorem realizeFun_injective : Function.Injective (realizeFun pl) := by
  intro p q h
  have hcol : colOf p = colOf q := by
    by_contra hne
    have hdisj := hP.disjoint (Finset.mem_coe.mpr (pl.mem (colOf p)))
      (Finset.mem_coe.mpr (pl.mem (colOf q))) fun e => hne (pl.injective e)
    exact Finset.disjoint_left.mp hdisj (realizeFun_mem pl p)
      (by rw [h]; exact realizeFun_mem pl q)
  have hval : (fiberPieceEquiv pl (colOf q) ⟨p, hcol⟩).val =
      (fiberPieceEquiv pl (colOf q) ⟨q, rfl⟩).val := by
    rw [← realizeFun_eq pl ⟨p, hcol⟩, ← realizeFun_eq pl ⟨q, rfl⟩]
    exact h
  exact congrArg Subtype.val ((fiberPieceEquiv pl (colOf q)).injective (Subtype.ext hval))

/-- The layout obtained by dropping every piece onto its column. -/
noncomputable def realize : Layout K := ⟨realizeFun pl, realizeFun_injective hP pl⟩

theorem realize_columnKeys (c : ColumnId) : (realize hP pl).columnKeys c = pl.piece c := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hc : colOf p = c := (mem_positions c p).mp hp
    exact hc ▸ realizeFun_mem pl p
  · rw [pl.card, (realize hP pl).columnKeys_card]

theorem realize_columns : (realize hP pl).columns = P := by
  rw [Layout.columns, show (realize hP pl).columnKeys = pl.piece from funext (realize_columnKeys hP pl),
    Placement.image_eq hP pl]

theorem realize_usedKeys : (realize hP pl).usedKeys = s := by
  rw [← (realize hP pl).columnKeys_cover,
    show (realize hP pl).columnKeys = pl.piece from funext (realize_columnKeys hP pl)]
  calc univ.biUnion pl.piece = (univ.image pl.piece).biUnion id := by
        rw [Finset.image_biUnion]; rfl
    _ = P.biUnion id := by rw [Placement.image_eq hP pl]
    _ = s := hP.cover

end Realize

/-- Every piece-set of a repertoire is the column structure of some layout on it. -/
theorem exists_layoutOn_columns_eq (R : Repertoire K) {P : Finset (Finset K)}
    (hP : IsPieceSet R.keys P) : ∃ L : LayoutOn R, L.val.columns = P :=
  ⟨⟨realize hP (canonicalPlacement hP), realize_usedKeys hP _⟩, realize_columns hP _⟩

/-- Every placement of the pieces on the finger columns is realised by a layout. -/
theorem exists_layoutOn_placement (R : Repertoire K) {P : Finset (Finset K)}
    (hP : IsPieceSet R.keys P) (pl : Placement P) :
    ∃ L : LayoutOn R, ∀ c, L.val.columnKeys c = pl.piece c :=
  ⟨⟨realize hP pl, realize_usedKeys hP pl⟩, realize_columnKeys hP pl⟩

/-! ### Equivalence classes are piece-sets -/

/-- An equivalence class of layouts is exactly a piece-set of the repertoire. -/
noncomputable def layoutClassEquiv (R : Repertoire K) :
    LayoutClass R ≃ {P // IsPieceSet R.keys P} :=
  Equiv.ofBijective
    (Quotient.lift (fun L : LayoutOn R => (⟨L.val.columns, L.columns_isPieceSet⟩ :
      {P // IsPieceSet R.keys P})) fun _ _ h => Subtype.ext h)
    ⟨by
      rintro ⟨L⟩ ⟨M⟩ h
      exact Quotient.sound (congrArg Subtype.val h),
     by
      rintro ⟨P, hP⟩
      obtain ⟨L, hL⟩ := exists_layoutOn_columns_eq R hP
      exact ⟨Quotient.mk _ L, Subtype.ext hL⟩⟩

noncomputable instance (R : Repertoire K) : Fintype {P // IsPieceSet R.keys P} :=
  Fintype.ofEquiv _ (layoutClassEquiv R)

/-- Any 30-key repertoire has exactly `30! / D` piece-sets. This also counts partitions into
blocks of prescribed sizes, which Mathlib does not prove. -/
theorem card_pieceSets (R : Repertoire K) :
    Fintype.card {P // IsPieceSet R.keys P} = 7615967597718480000 := by
  rw [← Fintype.card_congr (layoutClassEquiv R), card_layoutClass]

end Fern.Ortholinear
