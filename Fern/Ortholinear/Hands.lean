module
public import Fern.Ortholinear.Pieces
public import Mathlib.Data.Finset.Powerset

/-!
# Hands

Equivalence forgets which hand types each finger column, so the same-finger optimum is a piece-set,
not a layout. Measures that depend on hands, such as how many *spacegrams* (key, space, key) are
typed by one hand, still vary within the class.

Each hand holds three simple pieces and one index piece. `handSides P I` lists the key sets one hand
can type while it holds the index piece `I`: three of the six simple pieces together with `I`, so
there are `C(6,3) = 20` of them. They are exhaustive and every one is realised: the same-hand
weights achievable by layouts with pieces `P` are exactly the costs of those 20 sides
(`sameHandWeights_eq`). Fixing `I` loses nothing, because mirroring the hands swaps the two index
pieces and leaves the same-hand weight unchanged.
-/

@[expose] public section

namespace Fern.Ortholinear

open Finset

variable {K : Type} [DecidableEq K]

/-! ### Weights of key sets -/

/-- The weight of every ordered pair within a key set, each key paired with itself included. -/
def sideWeight (w : K → K → ℕ) (A : Finset K) : ℕ := ∑ p ∈ A ×ˢ A, w p.1 p.2

/-- The same-hand weight when one hand types the keys `A` of `s` and the other hand the rest. -/
def sideCost (w : K → K → ℕ) (s A : Finset K) : ℕ := sideWeight w A + sideWeight w (s \ A)

/-- Mirroring the hands does not change the same-hand weight. -/
theorem sideCost_sdiff (w : K → K → ℕ) {s A : Finset K} (h : A ⊆ s) :
    sideCost w s (s \ A) = sideCost w s A := by
  rw [sideCost, sideCost, Finset.sdiff_sdiff_eq_self h, Nat.add_comm]

/-! ### The keys each hand types -/

/-- The keys a hand types. -/
def Layout.handKeys (L : Layout K) (h : Hand) : Finset K :=
  (univ.filter fun c : ColumnId => c.hand = h).biUnion L.columnKeys

/-- The weight of ordered pairs of keys typed by the same hand. Weighted by spacegram counts, this
counts the same-hand spacegrams. -/
def Layout.sameHandWeight (L : Layout K) (w : K → K → ℕ) : ℕ :=
  sideWeight w (L.handKeys .left) + sideWeight w (L.handKeys .right)

theorem Layout.mem_handKeys {L : Layout K} {h : Hand} {k : K} :
    k ∈ L.handKeys h ↔ ∃ c : ColumnId, c.hand = h ∧ k ∈ L.columnKeys c := by
  simp [Layout.handKeys]

theorem Layout.handKeys_right (L : Layout K) : L.handKeys .right = L.usedKeys \ L.handKeys .left := by
  ext k
  rw [Finset.mem_sdiff, ← L.columnKeys_cover, Finset.mem_biUnion, Layout.mem_handKeys,
    Layout.mem_handKeys]
  constructor
  · rintro ⟨c, hc, hk⟩
    refine ⟨⟨c, Finset.mem_univ _, hk⟩, fun ⟨d, hd, hk'⟩ => ?_⟩
    rw [L.column_of_shared_key hk hk', hd] at hc
    exact absurd hc (by decide)
  · rintro ⟨⟨c, -, hk⟩, hno⟩
    refine ⟨c, ?_, hk⟩
    cases hc : c.hand
    · exact absurd ⟨c, hc, hk⟩ hno
    · rfl

theorem Layout.handKeys_subset (L : Layout K) (h : Hand) : L.handKeys h ⊆ L.usedKeys := by
  intro k hk
  obtain ⟨c, -, hc⟩ := Layout.mem_handKeys.mp hk
  rw [← L.columnKeys_cover]
  exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hc⟩

theorem Layout.sameHandWeight_eq (L : Layout K) (w : K → K → ℕ) :
    L.sameHandWeight w = sideCost w L.usedKeys (L.handKeys .left) := by
  rw [Layout.sameHandWeight, L.handKeys_right]
  rfl

/-- A hand types its three simple columns and its index column. -/
theorem Layout.handKeys_eq (L : Layout K) (h : Hand) :
    L.handKeys h = ((univ.filter fun c : ColumnId => c.hand = h ∧ c.kind = .simple).image
      L.columnKeys).biUnion id ∪ L.columnKeys (indexColumn h) := by
  ext k
  rw [Layout.mem_handKeys, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hk⟩
    by_cases hkind : c.kind = .simple
    · exact Or.inl ⟨L.columnKeys c,
        Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, hkind⟩, rfl⟩, hk⟩
    · have hci : c = indexColumn h := by
        revert hc hkind
        cases c <;> cases h <;> decide
      exact Or.inr (hci ▸ hk)
  · rintro (⟨p, hp, hk⟩ | hk)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨c, (Finset.mem_filter.mp hc).2.1, hk⟩
    · exact ⟨indexColumn h, by cases h <;> decide, hk⟩

/-! ### The sides a hand can hold -/

/-- The key sets one hand can type while holding the index piece `I`: three simple pieces with `I`. -/
def handSides (P : Finset (Finset K)) (I : Finset K) : Finset (Finset K) :=
  ((P.filter fun p : Finset K => p.card = 3).powersetCard 3).image fun S => S.biUnion id ∪ I

/-- The side a layout's hand types is one of the sides for the index piece it holds. -/
theorem Layout.handKeys_mem_handSides (L : Layout K) (h : Hand) :
    L.handKeys h ∈ handSides L.columns (L.columnKeys (indexColumn h)) := by
  rw [handSides, Finset.mem_image]
  refine ⟨(univ.filter fun c : ColumnId => c.hand = h ∧ c.kind = .simple).image L.columnKeys, ?_,
    (L.handKeys_eq h).symm⟩
  rw [Finset.mem_powersetCard]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [L.columnKeys_card, (Finset.mem_filter.mp hc).2.2]
    rfl
  · rw [Finset.card_image_of_injective _ L.columnKeys_injective]
    cases h <;> decide

theorem Hand.eq_right_of_ne_left {h : Hand} (hh : h ≠ .left) : h = .right := by
  cases h
  · exact absurd rfl hh
  · rfl

/-- A layout's index pieces are its two index columns. -/
theorem Layout.exists_indexColumn (L : Layout K) {I : Finset K}
    (hI : I ∈ L.columns.filter fun p : Finset K => p.card = 6) :
    ∃ h, I = L.columnKeys (indexColumn h) := by
  obtain ⟨hI, hcard⟩ := Finset.mem_filter.mp hI
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hI
  rw [L.columnKeys_card] at hcard
  cases c
  all_goals first | exact absurd hcard (by decide) | skip
  · exact ⟨.left, rfl⟩
  · exact ⟨.right, rfl⟩

section Sides

variable {s : Finset K} {P : Finset (Finset K)} (hP : IsPieceSet s P)
include hP

/-- A simple piece inside a union of chosen simple pieces and an index piece was chosen. -/
theorem mem_of_subset_biUnion_union {S : Finset (Finset K)} {I p : Finset K}
    (hS : S ⊆ P.filter fun p : Finset K => p.card = 3) (hI : I ∈ P.filter fun p : Finset K => p.card = 6)
    (hp : p ∈ P.filter fun p : Finset K => p.card = 3) (hsub : p ⊆ S.biUnion id ∪ I) : p ∈ S := by
  obtain ⟨hpP, hp3⟩ := Finset.mem_filter.mp hp
  obtain ⟨hIP, hI6⟩ := Finset.mem_filter.mp hI
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < p.card)
  rcases Finset.mem_union.mp (hsub hx) with hxS | hxI
  · obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hxS
    by_contra hpS
    have hpq : p ≠ q := fun e => hpS (e ▸ hq)
    exact Finset.disjoint_left.mp (hP.disjoint hpP (Finset.mem_filter.mp (hS hq)).1 hpq) hx hxq
  · have hpI : p ≠ I := fun e => by rw [e] at hp3; omega
    exact absurd hxI (Finset.disjoint_left.mp (hP.disjoint hpP hIP hpI) hx)

theorem handSides_injOn {I : Finset K} (hI : I ∈ P.filter fun p : Finset K => p.card = 6) :
    Set.InjOn (fun S : Finset (Finset K) => S.biUnion id ∪ I)
      ((P.filter fun p : Finset K => p.card = 3).powersetCard 3) := by
  intro S hS T hT hST
  have hS' := (Finset.mem_powersetCard.mp hS).1
  have hT' := (Finset.mem_powersetCard.mp hT).1
  simp only at hST
  ext p
  constructor
  · intro hp
    refine mem_of_subset_biUnion_union hP hT' hI (hS' hp) ?_
    rw [← hST]
    exact (Finset.subset_biUnion_of_mem id hp).trans Finset.subset_union_left
  · intro hp
    refine mem_of_subset_biUnion_union hP hS' hI (hT' hp) ?_
    rw [hST]
    exact (Finset.subset_biUnion_of_mem id hp).trans Finset.subset_union_left

/-- With its index piece fixed, a hand has exactly twenty possible sides. -/
theorem card_handSides {I : Finset K} (hI : I ∈ P.filter fun p : Finset K => p.card = 6) :
    (handSides P I).card = 20 := by
  rw [handSides, Finset.card_image_of_injOn (handSides_injOn hP hI), Finset.card_powersetCard,
    hP.simple_count]
  rfl

end Sides

/-- A layout's same-hand weight is the cost of one of the twenty sides for either index piece. -/
theorem LayoutOn.sameHandWeight_mem {R : Repertoire K} (L : LayoutOn R) {I : Finset K}
    (hI : I ∈ L.val.columns.filter fun p : Finset K => p.card = 6) (w : K → K → ℕ) :
    L.val.sameHandWeight w ∈ (handSides L.val.columns I).image (sideCost w R.keys) := by
  obtain ⟨h, rfl⟩ := L.val.exists_indexColumn hI
  refine Finset.mem_image.mpr ⟨L.val.handKeys h, L.val.handKeys_mem_handSides h, ?_⟩
  rw [Layout.sameHandWeight_eq, L.property]
  cases h
  · rfl
  · rw [L.val.handKeys_right, L.property]
    have hsub := L.val.handKeys_subset .left
    rw [L.property] at hsub
    exact sideCost_sdiff w hsub

/-- Every side is typed by the left hand of some layout with pieces `P`. -/
theorem exists_layoutOn_handKeys (R : Repertoire K) {P : Finset (Finset K)} (hP : IsPieceSet R.keys P)
    {I : Finset K} (hI : I ∈ P.filter fun p : Finset K => p.card = 6) {A : Finset K}
    (hA : A ∈ handSides P I) : ∃ L : LayoutOn R, L.val.columns = P ∧ L.val.handKeys .left = A := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  have hTsub : (P.filter fun p : Finset K => p.card = 3) \ S ⊆ P.filter fun p : Finset K => p.card = 3 :=
    Finset.sdiff_subset
  have hTcard : ((P.filter fun p : Finset K => p.card = 3) \ S).card = 3 := by
    rw [Finset.card_sdiff_of_subset hSsub, hP.simple_count, hScard]
  -- The other index piece.
  obtain ⟨J, hJ, hIJ⟩ : ∃ J ∈ P.filter (fun p : Finset K => p.card = 6), J ≠ I := by
    obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp hP.index_count
    rw [hxy'] at hI ⊢
    rcases Finset.mem_insert.mp hI with rfl | hIy
    · exact ⟨y, by simp, hxy.symm⟩
    · rw [Finset.mem_singleton.mp hIy]
      exact ⟨x, by simp, hxy⟩
  have hpair : P.filter (fun p : Finset K => p.card = 6) = {I, J} := by
    refine (Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_).symm
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hI
      · rw [Finset.mem_singleton.mp hx]
        exact hJ
    · rw [Finset.card_pair hIJ.symm, hP.index_count]
  -- Match each hand's simple columns to its chosen pieces.
  let eL : {c : ColumnId // c.hand = .left ∧ c.kind = .simple} ≃ {p // p ∈ S} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, hScard]; decide)
  let eR : {c : ColumnId // c.hand = .right ∧ c.kind = .simple} ≃
      {p // p ∈ (P.filter fun p : Finset K => p.card = 3) \ S} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, hTcard]; decide)
  let piece : ColumnId → Finset K := fun c =>
    if hk : c.kind = .simple then
      if hh : c.hand = .left then (eL ⟨c, hh, hk⟩).val
      else (eR ⟨c, Hand.eq_right_of_ne_left hh, hk⟩).val
    else if c.hand = .left then I else J
  have hmem : ∀ c, piece c ∈ P := by
    intro c
    by_cases hk : c.kind = .simple
    · by_cases hh : c.hand = .left
      · simp only [piece, dif_pos hk, dif_pos hh]
        exact (Finset.mem_filter.mp (hSsub (eL _).property)).1
      · simp only [piece, dif_pos hk, dif_neg hh]
        exact (Finset.mem_filter.mp (hTsub (eR _).property)).1
    · by_cases hh : c.hand = .left
      · simp only [piece, dif_neg hk, if_pos hh]
        exact (Finset.mem_filter.mp hI).1
      · simp only [piece, dif_neg hk, if_neg hh]
        exact (Finset.mem_filter.mp hJ).1
  have hcard : ∀ c, (piece c).card = 3 * c.kind.width := by
    intro c
    by_cases hk : c.kind = .simple
    · rw [hk]
      by_cases hh : c.hand = .left
      · simp only [piece, dif_pos hk, dif_pos hh]
        exact (Finset.mem_filter.mp (hSsub (eL _).property)).2
      · simp only [piece, dif_pos hk, dif_neg hh]
        exact (Finset.mem_filter.mp (hTsub (eR _).property)).2
    · rw [ColumnKind.eq_index_of_ne_simple hk]
      by_cases hh : c.hand = .left
      · simp only [piece, dif_neg hk, if_pos hh]
        exact (Finset.mem_filter.mp hI).2
      · simp only [piece, dif_neg hk, if_neg hh]
        exact (Finset.mem_filter.mp hJ).2
  have hsurj : ∀ p ∈ P, ∃ c, piece c = p := by
    intro p hp
    rcases hP.sizes p hp with h3 | h6
    · by_cases hpS : p ∈ S
      · obtain ⟨⟨c, hch, hck⟩, hc⟩ : ∃ c, eL c = ⟨p, hpS⟩ := ⟨eL.symm ⟨p, hpS⟩, eL.apply_symm_apply _⟩
        refine ⟨c, ?_⟩
        simp only [piece, dif_pos hck, dif_pos hch, hc]
      · have hpT : p ∈ (P.filter fun p : Finset K => p.card = 3) \ S :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hp, h3⟩, hpS⟩
        obtain ⟨⟨c, hch, hck⟩, hc⟩ : ∃ c, eR c = ⟨p, hpT⟩ := ⟨eR.symm ⟨p, hpT⟩, eR.apply_symm_apply _⟩
        have hnl : ¬c.hand = .left := by rw [hch]; decide
        refine ⟨c, ?_⟩
        simp only [piece, dif_pos hck, dif_neg hnl, hc]
    · have hp' : p ∈ ({I, J} : Finset (Finset K)) := hpair ▸ Finset.mem_filter.mpr ⟨hp, h6⟩
      rcases Finset.mem_insert.mp hp' with rfl | hpJ
      · exact ⟨.leftIndex, by simp [piece, ColumnId.kind, ColumnId.hand]⟩
      · rw [Finset.mem_singleton.mp hpJ]
        exact ⟨.rightIndex, by simp [piece, ColumnId.kind, ColumnId.hand]⟩
  have himage : univ.image piece = P := by
    refine Finset.eq_of_subset_of_card_le (fun p hp => ?_) (Finset.card_le_card fun p hp => ?_)
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hp
      exact hmem c
    · obtain ⟨c, hc⟩ := hsurj p hp
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩
  have hinj : Function.Injective piece := by
    have h := Finset.injOn_of_card_image_eq (s := (univ : Finset ColumnId)) (f := piece)
      (by rw [himage, hP.card_eq_eight]; rfl)
    exact fun c d hcd => h (Finset.mem_univ c) (Finset.mem_univ d) hcd
  obtain ⟨L, hLc⟩ := exists_layoutOn_placement R hP ⟨piece, hmem, hcard, hinj⟩
  have hfun : L.val.columnKeys = piece := funext hLc
  refine ⟨L, by rw [Layout.columns, hfun, himage], ?_⟩
  have hleft : (univ.filter fun c : ColumnId => c.hand = .left ∧ c.kind = .simple).image piece = S := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨hch, hck⟩, rfl⟩
      simp only [piece, dif_pos hck, dif_pos hch]
      exact (eL _).property
    · intro hp
      obtain ⟨⟨c, hch, hck⟩, hc⟩ : ∃ c, eL c = ⟨p, hp⟩ := ⟨eL.symm ⟨p, hp⟩, eL.apply_symm_apply _⟩
      exact ⟨c, ⟨hch, hck⟩, by simp only [piece, dif_pos hck, dif_pos hch, hc]⟩
  rw [Layout.handKeys_eq, hfun, hleft]
  simp [piece, indexColumn, ColumnId.kind, ColumnId.hand]

/-- The same-hand weights of the layouts with pieces `P` are exactly the costs of the twenty sides
for either index piece. -/
theorem sameHandWeights_eq (R : Repertoire K) {P : Finset (Finset K)} (hP : IsPieceSet R.keys P)
    {I : Finset K} (hI : I ∈ P.filter fun p : Finset K => p.card = 6) (w : K → K → ℕ) :
    Set.range (fun L : {L : LayoutOn R // L.val.columns = P} => L.val.val.sameHandWeight w) =
      ((handSides P I).image (sideCost w R.keys) : Set ℕ) := by
  ext n
  constructor
  · rintro ⟨⟨L, rfl⟩, rfl⟩
    exact Finset.mem_coe.mpr (L.sameHandWeight_mem hI w)
  · intro hn
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hn)
    obtain ⟨L, hLc, hLh⟩ := exists_layoutOn_handKeys R hP hI hA
    refine ⟨⟨L, hLc⟩, ?_⟩
    show L.val.sameHandWeight w = _
    rw [Layout.sameHandWeight_eq, L.property, hLh]

/-- The spacegram tie-break: the least same-hand weight among layouts with pieces `P` is the least
cost among the twenty sides. -/
theorem tieBreak_isLeast (R : Repertoire K) {P : Finset (Finset K)} (hP : IsPieceSet R.keys P)
    {I : Finset K} (hI : I ∈ P.filter fun p : Finset K => p.card = 6) (w : K → K → ℕ) {n : ℕ}
    (hn : IsLeast ((handSides P I).image (sideCost w R.keys) : Set ℕ) n) :
    IsLeast (Set.range fun L : {L : LayoutOn R // L.val.columns = P} => L.val.val.sameHandWeight w) n := by
  rwa [sameHandWeights_eq R hP hI w]

end Fern.Ortholinear
