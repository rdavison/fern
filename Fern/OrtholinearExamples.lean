module
public import Fern.Ortholinear
import Mathlib.Logic.Equiv.Prod

/-! Checked examples and counterexamples for the ortholinear model. -/

@[expose] public section

namespace Fern.Ortholinear.Examples

-- Closed finite-set computations are checked by the kernel, without native_decide.
set_option maxRecDepth 4096

/-- Use the 30 positions themselves as distinct keycode labels. -/
def identityLayout : Layout Position where
  keyAt := id
  unique := Function.injective_id

/-- Label positions by a permutation of the grid. -/
def rearrange (e : Position ≃ Position) : Layout Position where
  keyAt := e
  unique := e.injective

/-- Exchange the top and bottom rows. -/
def rowSwap : Layout Position :=
  rearrange (Equiv.prodCongr (Equiv.swap (0 : Fin 3) 2) (Equiv.refl (Fin 10)))

/-- Exchange left pinky with right ring, including all three rows. -/
def simpleColumnSwap : Layout Position :=
  rearrange (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 10) 8))

/-- Exchange the inner and outer halves of the left index region. -/
def indexHalfSwap : Layout Position :=
  rearrange (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.swap (3 : Fin 10) 4))

/-- Exchange just two keys, crossing from left pinky to left ring. -/
def individualKeySwap : Layout Position :=
  rearrange (Equiv.swap ((0, 0) : Position) (0, 1))

theorem forward_pair : IsSFB identityLayout ((0, 0), (1, 0)) := by decide
theorem reversed_pair : IsSFB identityLayout ((1, 0), (0, 0)) := by decide
theorem ordered_pairs_differ :
    (((0, 0), (1, 0)) : Bigram Position) ≠ ((1, 0), (0, 0)) := by decide
theorem repeat_excluded : ¬IsSFB identityLayout ((0, 0), (0, 0)) := by decide
theorem different_fingers_excluded : ¬IsSFB identityLayout ((0, 0), (1, 1)) := by decide
theorem opposite_hands_excluded : ¬IsSFB identityLayout ((0, 0), (1, 9)) := by decide
theorem left_index_across_halves : IsSFB identityLayout ((0, 3), (2, 4)) := by decide
theorem right_index_across_halves : IsSFB identityLayout ((0, 5), (2, 6)) := by decide
theorem opposite_indices_excluded : ¬IsSFB identityLayout ((0, 4), (0, 5)) := by decide

theorem row_swap_equivalent : identityLayout.Equivalent rowSwap := by
  change identityLayout.columns = rowSwap.columns
  decide

theorem simple_column_swap_equivalent : identityLayout.Equivalent simpleColumnSwap := by
  change identityLayout.columns = simpleColumnSwap.columns
  decide

theorem index_half_swap_equivalent : identityLayout.Equivalent indexHalfSwap := by
  change identityLayout.columns = indexHalfSwap.columns
  decide

theorem column_order_ignored :
    Column.Equivalent (identityLayout, .leftPinky) (rowSwap, .leftPinky) := by
  change identityLayout.columnKeys .leftPinky = rowSwap.columnKeys .leftPinky
  decide

theorem column_hand_and_finger_ignored :
    Column.Equivalent (identityLayout, .leftPinky) (simpleColumnSwap, .rightRing) := by
  change identityLayout.columnKeys .leftPinky = simpleColumnSwap.columnKeys .rightRing
  decide

theorem inner_index_membership_can_change :
    (innerIndexPositions .left).image identityLayout.keyAt ≠
      (innerIndexPositions .left).image indexHalfSwap.keyAt := by decide

theorem row_swap_preserves_sfbs : identityLayout.sfbs = rowSwap.sfbs :=
  Layout.equivalent_sfb_eq row_swap_equivalent

theorem simple_column_swap_preserves_sfbs : identityLayout.sfbs = simpleColumnSwap.sfbs :=
  Layout.equivalent_sfb_eq simple_column_swap_equivalent

theorem individual_key_swap_breaks_pair :
    ¬IsSFB individualKeySwap ((0, 0), (1, 0)) := by decide

theorem individual_key_swap_changes_sfbs : identityLayout.sfbs ≠ individualKeySwap.sfbs := by
  intro h
  apply individual_key_swap_breaks_pair
  change ((0, 0), (1, 0)) ∈ individualKeySwap.sfbs
  rw [← h]
  exact forward_pair

theorem individual_key_swap_not_equivalent : ¬identityLayout.Equivalent individualKeySwap := by
  intro h
  exact individual_key_swap_changes_sfbs (Layout.equivalent_sfb_eq h)

/-- Only 30 labels are used even when the ambient keycode type is infinite. -/
def naturalKeycodes : Layout Nat where
  keyAt p := p.1.val * 10 + p.2.val
  unique := by
    intro p q h
    apply Prod.ext <;> apply Fin.ext <;> dsimp at h ⊢ <;> omega

theorem thirty_used_naturals : naturalKeycodes.usedKeys.card = 30 :=
  naturalKeycodes.usedKeys_card

theorem ninety_six_sfbs : naturalKeycodes.sfbs.card = 96 := naturalKeycodes.sfbs_card

end Fern.Ortholinear.Examples
