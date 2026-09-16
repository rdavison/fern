module
public import Fern.Ortholinear.Symmetry

/-!
# Swapping two keys

A swap is the reindexing along a transposition of the grid. It preserves equivalence exactly
when the two positions share a finger column; otherwise a fixed number of same-finger bigrams
disappears and the same number appears, determined only by the sizes of the two columns.
-/

@[expose] public section

namespace Fern.Ortholinear

open Equiv

variable {Keycode : Type}

/-! ### Position swaps -/

/-- Exchange the keycodes at two grid positions. -/
def Layout.swapPositions (L : Layout Keycode) (p q : Position) : Layout Keycode :=
  L.reindex (Equiv.swap p q)

@[simp] theorem Layout.swapPositions_keyAt (L : Layout Keycode) (p q r : Position) :
    (L.swapPositions p q).keyAt r = L.keyAt (Equiv.swap p q r) := rfl

/-- Swapping a position with itself changes nothing. -/
@[simp] theorem Layout.swapPositions_self (L : Layout Keycode) (p : Position) :
    L.swapPositions p p = L :=
  Layout.ext fun r => by rw [Layout.swapPositions_keyAt, Equiv.swap_self]; rfl

/-- Repeating a swap restores the original layout. -/
@[simp] theorem Layout.swapPositions_swapPositions (L : Layout Keycode) (p q : Position) :
    (L.swapPositions p q).swapPositions p q = L :=
  Layout.ext fun r => by
    rw [Layout.swapPositions_keyAt, Layout.swapPositions_keyAt, Equiv.swap_apply_self]

theorem Layout.swapPositions_comm (L : Layout Keycode) (p q : Position) :
    L.swapPositions p q = L.swapPositions q p := by
  rw [Layout.swapPositions, Layout.swapPositions, Equiv.swap_comm]

/-- A transposition within one finger column is a column symmetry. -/
theorem swap_mem_columnSymmetry {p q : Position} (h : colOf p = colOf q) :
    Equiv.swap p q ∈ ColumnSymmetry := by
  refine mem_columnSymmetry_of_perm 1 fun r => ?_
  show colOf (Equiv.swap p q r) = colOf r
  rcases eq_or_ne r p with rfl | hrp
  · rw [Equiv.swap_apply_left]
    exact h.symm
  · rcases eq_or_ne r q with rfl | hrq
    · rw [Equiv.swap_apply_right]
      exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]

/-! ### The positions whose same-finger bigrams change -/

/-- The ordered same-finger position pairs touching `x`. -/
def sfbsAt (x : Position) : Finset (Position × Position) :=
  positionSFBs.filter fun rt => rt.1 = x ∨ rt.2 = x

theorem mem_positionSFBs {r t : Position} :
    (r, t) ∈ positionSFBs ↔ colOf r = colOf t ∧ r ≠ t := by
  simp [positionSFBs, colOf]

theorem mem_sfbsAt {x r t : Position} :
    (r, t) ∈ sfbsAt x ↔ (colOf r = colOf t ∧ r ≠ t) ∧ (r = x ∨ t = x) := by
  rw [sfbsAt, Finset.mem_filter, mem_positionSFBs]

set_option maxRecDepth 100000 in
theorem card_sfbsAt (x : Position) : (sfbsAt x).card = 2 * (3 * (colOf x).kind.width - 1) := by
  revert x; decide

/-- Apply a transposition to both halves of an ordered pair. -/
def swapPair (p q : Position) (rt : Position × Position) : Position × Position :=
  (Equiv.swap p q rt.1, Equiv.swap p q rt.2)

@[simp] theorem swapPair_swapPair (p q : Position) (rt : Position × Position) :
    swapPair p q (swapPair p q rt) = rt := by
  rw [swapPair, swapPair, Equiv.swap_apply_self, Equiv.swap_apply_self]

/-- The same-finger position pairs destroyed by a swap. -/
def swapLostPositions (p q : Position) : Finset (Position × Position) :=
  positionSFBs \ positionSFBs.image (swapPair p q)

section
-- Keep the 96-element enumeration opaque; it is exposed and would otherwise be evaluated
-- every time a membership hypothesis is checked.
attribute [local irreducible] positionSFBs

theorem mem_image_swapPair (p q : Position) (rt : Position × Position) :
    rt ∈ positionSFBs.image (swapPair p q) ↔ swapPair p q rt ∈ positionSFBs := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    rwa [swapPair_swapPair]
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, swapPair_swapPair p q rt⟩

theorem mem_positionSFBs_swapPair {p q r t : Position} :
    swapPair p q (r, t) ∈ positionSFBs ↔
      colOf (Equiv.swap p q r) = colOf (Equiv.swap p q t) ∧
        Equiv.swap p q r ≠ Equiv.swap p q t :=
  mem_positionSFBs

/-- Only pairs touching a swapped position can change. -/
theorem mem_swapLostPositions_touches {p q : Position} {r t : Position}
    (h : (r, t) ∈ swapLostPositions p q) : r = p ∨ t = p ∨ r = q ∨ t = q := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [swapLostPositions, Finset.mem_sdiff, mem_image_swapPair] at h
  refine h.2 ?_
  have hfix : swapPair p q (r, t) = (r, t) := by
    rw [swapPair, Equiv.swap_apply_of_ne_of_ne h1 h3, Equiv.swap_apply_of_ne_of_ne h2 h4]
  rw [hfix]
  exact h.1

theorem colOf_swap_left_ne {p q y : Position} (hpq : colOf p ≠ colOf q)
    (hcol : colOf p = colOf y) (hne : p ≠ y) :
    colOf (Equiv.swap p q p) ≠ colOf (Equiv.swap p q y) := by
  have hyq : y ≠ q := fun h => hpq (hcol.trans (congrArg colOf h))
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) hyq, ← hcol]
  exact fun h => hpq h.symm

theorem colOf_swap_right_ne {p q y : Position} (hpq : colOf p ≠ colOf q)
    (hcol : colOf q = colOf y) (hne : q ≠ y) :
    colOf (Equiv.swap p q q) ≠ colOf (Equiv.swap p q y) := by
  have hyp : y ≠ p := fun h => hpq (hcol.trans (congrArg colOf h)).symm
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyp (Ne.symm hne), ← hcol]
  exact hpq

theorem swapLostPositions_eq {p q : Position} (hpq : colOf p ≠ colOf q) :
    swapLostPositions p q = sfbsAt p ∪ sfbsAt q := by
  ext ⟨r, t⟩
  rw [swapLostPositions, Finset.mem_sdiff, mem_image_swapPair, Finset.mem_union,
    mem_sfbsAt, mem_sfbsAt, mem_positionSFBs, mem_positionSFBs_swapPair]
  constructor
  · rintro ⟨hb, hnot⟩
    have touches : r = p ∨ t = p ∨ r = q ∨ t = q := by
      by_contra hc
      push_neg at hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      refine hnot ?_
      rw [Equiv.swap_apply_of_ne_of_ne h1 h3, Equiv.swap_apply_of_ne_of_ne h2 h4]
      exact hb
    rcases touches with h | h | h | h
    · exact Or.inl ⟨hb, Or.inl h⟩
    · exact Or.inl ⟨hb, Or.inr h⟩
    · exact Or.inr ⟨hb, Or.inl h⟩
    · exact Or.inr ⟨hb, Or.inr h⟩
  · intro h
    have hb : colOf r = colOf t ∧ r ≠ t := by
      rcases h with ⟨hb, _⟩ | ⟨hb, _⟩ <;> exact hb
    refine ⟨hb, ?_⟩
    rintro ⟨hcol', -⟩
    rcases h with ⟨-, hx | hx⟩ | ⟨-, hx | hx⟩
    · subst hx
      exact colOf_swap_left_ne hpq hb.1 hb.2 hcol'
    · subst hx
      exact colOf_swap_left_ne hpq hb.1.symm (Ne.symm hb.2) hcol'.symm
    · subst hx
      exact colOf_swap_right_ne hpq hb.1 hb.2 hcol'
    · subst hx
      exact colOf_swap_right_ne hpq hb.1.symm (Ne.symm hb.2) hcol'.symm

theorem sfbsAt_disjoint {p q : Position} (hpq : colOf p ≠ colOf q) :
    Disjoint (sfbsAt p) (sfbsAt q) := by
  refine Finset.disjoint_left.mpr fun rt hp hq => hpq ?_
  obtain ⟨r, t⟩ := rt
  rw [mem_sfbsAt] at hp hq
  obtain ⟨⟨hcol, -⟩, hp'⟩ := hp
  obtain ⟨-, hq'⟩ := hq
  rcases hp' with h1 | h1 <;> rcases hq' with h2 | h2
  · rw [← h1, ← h2]
  · rw [← h1, ← h2]; exact hcol
  · rw [← h1, ← h2]; exact hcol.symm
  · rw [← h1, ← h2]

theorem width_pos (c : ColumnId) : 1 ≤ c.kind.width := by
  cases c <;> decide

/-- A cross-column swap destroys `2 (m + n - 2)` ordered same-finger position pairs. -/
theorem card_swapLostPositions {p q : Position} (hpq : colOf p ≠ colOf q) :
    (swapLostPositions p q).card
      = 2 * (3 * (colOf p).kind.width + 3 * (colOf q).kind.width - 2) := by
  rw [swapLostPositions_eq hpq, Finset.card_union_of_disjoint (sfbsAt_disjoint hpq),
    card_sfbsAt, card_sfbsAt]
  have h1 := width_pos (colOf p)
  have h2 := width_pos (colOf q)
  omega

end

/-! ### Same-finger bigrams lost and gained -/

variable [DecidableEq Keycode]

section
attribute [local irreducible] Layout.sfbs positionSFBs

/-- Reindexing along a within-column transposition preserves equivalence. -/
theorem Layout.equivalent_swapPositions (L : Layout Keycode) {p q : Position}
    (h : colOf p = colOf q) : L.Equivalent (L.swapPositions p q) :=
  L.equivalent_reindex ⟨Equiv.swap p q, swap_mem_columnSymmetry h⟩

theorem Layout.sfbs_swapPositions (L : Layout Keycode) (p q : Position) :
    (L.swapPositions p q).sfbs = (positionSFBs.image (swapPair p q)).image L.bigramAt := by
  rw [Layout.sfbs_eq_image, Finset.image_image]
  rfl

theorem Layout.sfbs_sdiff_swapPositions (L : Layout Keycode) (p q : Position) :
    L.sfbs \ (L.swapPositions p q).sfbs = (swapLostPositions p q).image L.bigramAt := by
  rw [Layout.sfbs_eq_image, Layout.sfbs_swapPositions, swapLostPositions,
    Finset.image_sdiff _ _ L.bigramAt_injective]

/-- A cross-column swap destroys exactly `2 (m + n - 2)` ordered same-finger bigrams. -/
theorem Layout.card_sfbs_lost (L : Layout Keycode) {p q : Position} (hpq : colOf p ≠ colOf q) :
    (L.sfbs \ (L.swapPositions p q).sfbs).card
      = 2 * (3 * (colOf p).kind.width + 3 * (colOf q).kind.width - 2) := by
  rw [L.sfbs_sdiff_swapPositions p q, Finset.card_image_of_injective _ L.bigramAt_injective,
    card_swapLostPositions hpq]

/-- The same number of ordered same-finger bigrams appears. -/
theorem Layout.card_sfbs_gained (L : Layout Keycode) {p q : Position} (hpq : colOf p ≠ colOf q) :
    ((L.swapPositions p q).sfbs \ L.sfbs).card
      = 2 * (3 * (colOf p).kind.width + 3 * (colOf q).kind.width - 2) := by
  have h := (L.swapPositions p q).card_sfbs_lost hpq
  rwa [Layout.swapPositions_swapPositions] at h

/-- The ordered same-finger bigrams that a swap changes. -/
def Layout.sfbsChanged (L : Layout Keycode) (p q : Position) : Finset (Bigram Keycode) :=
  (L.sfbs \ (L.swapPositions p q).sfbs) ∪ ((L.swapPositions p q).sfbs \ L.sfbs)

theorem Layout.card_sfbsChanged (L : Layout Keycode) {p q : Position} (hpq : colOf p ≠ colOf q) :
    (L.sfbsChanged p q).card
      = 4 * (3 * (colOf p).kind.width + 3 * (colOf q).kind.width - 2) := by
  rw [Layout.sfbsChanged, Finset.card_union_of_disjoint disjoint_sdiff_sdiff,
    L.card_sfbs_lost hpq, L.card_sfbs_gained hpq]
  omega

/-- Within one finger column a swap changes nothing. -/
theorem Layout.sfbs_swapPositions_eq (L : Layout Keycode) {p q : Position}
    (h : colOf p = colOf q) : (L.swapPositions p q).sfbs = L.sfbs :=
  (Layout.equivalent_sfb_eq (L.equivalent_swapPositions h)).symm

theorem Layout.card_sfbsChanged_sameColumn (L : Layout Keycode) {p q : Position}
    (h : colOf p = colOf q) : (L.sfbsChanged p q).card = 0 := by
  rw [Layout.sfbsChanged, L.sfbs_swapPositions_eq h, Finset.sdiff_self, Finset.union_self,
    Finset.card_empty]

/-- A swap preserves equivalence exactly when its positions share a finger column. -/
theorem Layout.equivalent_swapPositions_iff (L : Layout Keycode) (p q : Position) :
    L.Equivalent (L.swapPositions p q) ↔ colOf p = colOf q := by
  constructor
  · intro h
    by_contra hpq
    have hcard := L.card_sfbs_lost hpq
    have hempty : L.sfbs \ (L.swapPositions p q).sfbs = ∅ := by
      rw [Layout.equivalent_sfb_eq h, Finset.sdiff_self]
    rw [hempty, Finset.card_empty] at hcard
    have h1 := width_pos (colOf p)
    have h2 := width_pos (colOf q)
    omega
  · exact fun h => L.equivalent_swapPositions h

/-- Every changed same-finger bigram contains one of the two swapped keycodes. -/
theorem Layout.mem_sfbs_lost_touches (L : Layout Keycode) {p q : Position}
    {x : Bigram Keycode} (hx : x ∈ L.sfbs \ (L.swapPositions p q).sfbs) :
    x.1 = L.keyAt p ∨ x.2 = L.keyAt p ∨ x.1 = L.keyAt q ∨ x.2 = L.keyAt q := by
  rw [L.sfbs_sdiff_swapPositions p q] at hx
  obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨r, t⟩ := rt
  rcases mem_swapLostPositions_touches hrt with h | h | h | h
  · exact Or.inl (congrArg L.keyAt h)
  · exact Or.inr (Or.inl (congrArg L.keyAt h))
  · exact Or.inr (Or.inr (Or.inl (congrArg L.keyAt h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg L.keyAt h)))

theorem Layout.mem_sfbsChanged_touches (L : Layout Keycode) {p q : Position}
    {x : Bigram Keycode} (hx : x ∈ L.sfbsChanged p q) :
    x.1 = L.keyAt p ∨ x.2 = L.keyAt p ∨ x.1 = L.keyAt q ∨ x.2 = L.keyAt q := by
  rcases Finset.mem_union.mp hx with h | h
  · exact L.mem_sfbs_lost_touches h
  · have h' := (L.swapPositions p q).mem_sfbs_lost_touches
      (p := p) (q := q) (by rwa [Layout.swapPositions_swapPositions])
    rw [Layout.swapPositions_keyAt, Layout.swapPositions_keyAt, Equiv.swap_apply_left,
      Equiv.swap_apply_right] at h'
    tauto

/-- The number of ordered same-finger bigrams a swap changes, read off the two columns. -/
def changedCount (p q : Position) : Nat :=
  if colOf p = colOf q then 0
  else 4 * (3 * (colOf p).kind.width + 3 * (colOf q).kind.width - 2)

theorem Layout.card_sfbsChanged_eq (L : Layout Keycode) (p q : Position) :
    (L.sfbsChanged p q).card = changedCount p q := by
  unfold changedCount
  split_ifs with h
  · exact L.card_sfbsChanged_sameColumn h
  · exact L.card_sfbsChanged h

/-! ### The three cross-column cases -/

theorem Layout.card_sfbsChanged_simple_simple (L : Layout Keycode) {p q : Position}
    (hpq : colOf p ≠ colOf q) (hp : (colOf p).kind = .simple) (hq : (colOf q).kind = .simple) :
    (L.sfbsChanged p q).card = 16 := by
  rw [L.card_sfbsChanged hpq, hp, hq]
  decide

theorem Layout.card_sfbsChanged_simple_index (L : Layout Keycode) {p q : Position}
    (hpq : colOf p ≠ colOf q) (hp : (colOf p).kind = .simple) (hq : (colOf q).kind = .index) :
    (L.sfbsChanged p q).card = 28 := by
  rw [L.card_sfbsChanged hpq, hp, hq]
  decide

theorem Layout.card_sfbsChanged_index_index (L : Layout Keycode) {p q : Position}
    (hpq : colOf p ≠ colOf q) (hp : (colOf p).kind = .index) (hq : (colOf q).kind = .index) :
    (L.sfbsChanged p q).card = 40 := by
  rw [L.card_sfbsChanged hpq, hp, hq]
  decide

/-! ### Swapping two used keycodes -/

/-- Exchange the positions of two used keycodes. -/
def Layout.swapKeys (L : Layout Keycode) (a b : UsedKey L) : Layout Keycode :=
  L.swapPositions a.position b.position

@[simp] theorem Layout.swapKeys_left (L : Layout Keycode) (a b : UsedKey L) :
    (L.swapKeys a b).keyAt a.position = b.val := by
  rw [Layout.swapKeys, Layout.swapPositions_keyAt, Equiv.swap_apply_left,
    UsedKey.keyAt_position]

@[simp] theorem Layout.swapKeys_right (L : Layout Keycode) (a b : UsedKey L) :
    (L.swapKeys a b).keyAt b.position = a.val := by
  rw [Layout.swapKeys, Layout.swapPositions_keyAt, Equiv.swap_apply_right,
    UsedKey.keyAt_position]

@[simp] theorem Layout.swapKeys_self (L : Layout Keycode) (a : UsedKey L) :
    L.swapKeys a a = L := L.swapPositions_self a.position

theorem Layout.swapKeys_swapKeys (L : Layout Keycode) (a b : UsedKey L) :
    (L.swapKeys a b).swapPositions a.position b.position = L :=
  L.swapPositions_swapPositions a.position b.position

@[simp] theorem Layout.usedKeys_swapKeys (L : Layout Keycode) (a b : UsedKey L) :
    (L.swapKeys a b).usedKeys = L.usedKeys := L.usedKeys_reindex _

/-- Swapping two used keycodes preserves equivalence exactly when they share a column. -/
theorem Layout.equivalent_swapKeys_iff (L : Layout Keycode) (a b : UsedKey L) :
    L.Equivalent (L.swapKeys a b) ↔ a.column = b.column :=
  L.equivalent_swapPositions_iff a.position b.position

end

end Fern.Ortholinear
