module
public import Fern.Ortholinear.Lookup

/-!
# Exhaustive classification of ordered bigrams

Every ordered pair of used keycodes falls into exactly one of four categories. The classifier
is total on `UsedKey L`, which keeps unused keycodes out of the classification domain, and the
category counts are the same for every layout.
-/

@[expose] public section

namespace Fern.Ortholinear

/-- The four categories of an ordered bigram. -/
inductive BigramKind where
  | repeated
  | sameFinger
  | sameHandDifferentFinger
  | oppositeHands
  deriving DecidableEq, Fintype, Repr

/-- The number of ordered pairs in each category, for any layout. -/
def BigramKind.count : BigramKind → Nat
  | .repeated => 30
  | .sameFinger => 96
  | .sameHandDifferentFinger => 324
  | .oppositeHands => 450

/-- Classification of an ordered pair of positions, before keycodes are assigned. -/
def positionKind (p q : Position) : BigramKind :=
  if p = q then .repeated
  else if columnAt p.2 = columnAt q.2 then .sameFinger
  else if (columnAt p.2).hand = (columnAt q.2).hand then .sameHandDifferentFinger
  else .oppositeHands

variable {Keycode : Type} [DecidableEq Keycode]

/-- Classification of an ordered pair of used keycodes. -/
def Layout.classify (L : Layout Keycode) (a b : UsedKey L) : BigramKind :=
  if a = b then .repeated
  else if a.column = b.column then .sameFinger
  else if a.hand = b.hand then .sameHandDifferentFinger
  else .oppositeHands

theorem Layout.classify_atPosition (L : Layout Keycode) (p q : Position) :
    L.classify (L.atPosition p) (L.atPosition q) = positionKind p q := by
  simp only [Layout.classify, positionKind, UsedKey.hand, UsedKey.column_atPosition,
    L.atPosition_inj_iff]

theorem Layout.classify_eq_positionKind (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = positionKind a.position b.position := by
  rw [← L.classify_atPosition a.position b.position, L.atPosition_position,
    L.atPosition_position]

/-! ### Characterisations -/

section
attribute [local irreducible] Layout.sfbs

@[simp] theorem Layout.classify_eq_repeated (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = .repeated ↔ a = b := by
  unfold Layout.classify
  split_ifs with h₁ h₂ h₃ <;> simp_all

theorem Layout.classify_eq_sameFinger (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = .sameFinger ↔ IsSFB L (a.val, b.val) := by
  rw [isSFB_iff_sameColumn L a b]
  unfold Layout.classify SameColumn
  split_ifs with h₁ h₂ h₃ <;> simp_all

theorem Layout.classify_eq_sameHand (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = .sameHandDifferentFinger ↔ a.hand = b.hand ∧ a.finger ≠ b.finger := by
  unfold Layout.classify UsedKey.hand UsedKey.finger
  have hcol : a.column = b.column ↔ a.column.hand = b.column.hand ∧ a.column.finger = b.column.finger :=
    (hand_finger_unique a.column b.column).symm
  split_ifs with h₁ h₂ h₃ <;> simp_all

theorem Layout.classify_eq_oppositeHands (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = .oppositeHands ↔ a.hand ≠ b.hand := by
  unfold Layout.classify UsedKey.hand
  split_ifs with h₁ h₂ h₃ <;> simp_all

/-- The four categories are exhaustive. -/
theorem Layout.classify_exhaustive (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = .repeated ∨ L.classify a b = .sameFinger ∨
      L.classify a b = .sameHandDifferentFinger ∨ L.classify a b = .oppositeHands := by
  generalize L.classify a b = k
  cases k <;> simp

/-- The four categories are mutually exclusive. -/
theorem Layout.classify_exclusive (L : Layout Keycode) (a b : UsedKey L)
    {j k : BigramKind} (hj : L.classify a b = j) (hk : L.classify a b = k) : j = k := by
  rw [← hj, ← hk]

/-- Reversing an ordered bigram preserves its category. -/
theorem Layout.classify_comm (L : Layout Keycode) (a b : UsedKey L) :
    L.classify a b = L.classify b a := by
  unfold Layout.classify UsedKey.hand
  by_cases h : a = b
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases hc : a.column = b.column
    · rw [if_pos hc, if_pos (Eq.symm hc)]
    · rw [if_neg hc, if_neg (Ne.symm hc)]
      by_cases hh : a.column.hand = b.column.hand
      · rw [if_pos hh, if_pos (Eq.symm hh)]
      · rw [if_neg hh, if_neg (Ne.symm hh)]

/-- Distinct keys give two distinct ordered bigrams under reversal. -/
theorem Layout.reversed_ne (L : Layout Keycode) (a b : UsedKey L) (h : a ≠ b) :
    ((a, b) : UsedKey L × UsedKey L) ≠ (b, a) := by
  intro hab
  exact h (congrArg Prod.fst hab)

end

/-! ### Category cardinalities -/

set_option maxRecDepth 8192 in
theorem positionKind_card (k : BigramKind) :
    Fintype.card {pq : Position × Position // positionKind pq.1 pq.2 = k} = k.count := by
  cases k <;> decide

theorem Layout.classify_card (L : Layout Keycode) (k : BigramKind) :
    Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = k} = k.count := by
  rw [← positionKind_card k]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (L.posEquiv.prodCongr L.posEquiv) fun pq => by
      obtain ⟨p, q⟩ := pq
      show positionKind p q = k ↔ L.classify (L.atPosition p) (L.atPosition q) = k
      rw [L.classify_atPosition])
    |>.symm

theorem Layout.card_repeated (L : Layout Keycode) :
    Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .repeated} = 30 :=
  L.classify_card .repeated

theorem Layout.card_sameFinger (L : Layout Keycode) :
    Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .sameFinger} = 96 :=
  L.classify_card .sameFinger

theorem Layout.card_sameHandDifferentFinger (L : Layout Keycode) :
    Fintype.card
      {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .sameHandDifferentFinger} = 324 :=
  L.classify_card .sameHandDifferentFinger

theorem Layout.card_oppositeHands (L : Layout Keycode) :
    Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .oppositeHands} = 450 :=
  L.classify_card .oppositeHands

theorem Layout.card_usedKey_pairs (L : Layout Keycode) :
    Fintype.card (UsedKey L × UsedKey L) = 900 := by
  rw [Fintype.card_prod, L.card_usedKey]

/-- The four categories partition all 900 ordered pairs of used keycodes. -/
theorem Layout.classify_partition_card (L : Layout Keycode) :
    Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .repeated}
      + Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .sameFinger}
      + Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .sameHandDifferentFinger}
      + Fintype.card {ab : UsedKey L × UsedKey L // L.classify ab.1 ab.2 = .oppositeHands}
      = Fintype.card (UsedKey L × UsedKey L) := by
  rw [L.card_repeated, L.card_sameFinger, L.card_sameHandDifferentFinger, L.card_oppositeHands,
    L.card_usedKey_pairs]

end Fern.Ortholinear
