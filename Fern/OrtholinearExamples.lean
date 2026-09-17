module
public import Fern.Ortholinear.Classify
public import Fern.Ortholinear.Swap
public import Fern.Ortholinear.Corpus
public import Fern.Ortholinear.Text
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

/-! ## Lookup on an infinite ambient keycode type

`naturalKeycodes` labels the grid with natural numbers, so most keycodes are unused. -/

theorem positionOf_present : naturalKeycodes.positionOf 13 = some (1, 3) := by decide

theorem positionOf_missing : naturalKeycodes.positionOf 100 = none := by decide

theorem hundred_unused : (100 : Nat) ∉ naturalKeycodes.usedKeys := by decide

theorem missing_key_has_no_partners : naturalKeycodes.outgoing 100 = ∅ :=
  naturalKeycodes.outgoing_eq_empty hundred_unused

theorem used_key_position : (naturalKeycodes.atPosition (1, 3)).position = (1, 3) := by decide

/-! ## Same-finger partner counts -/

theorem simple_column_key_has_two_partners :
    (naturalKeycodes.outgoing (naturalKeycodes.atPosition (0, 0)).val).card = 2 :=
  naturalKeycodes.card_outgoing_simple _ (by decide)

theorem index_column_key_has_five_partners :
    (naturalKeycodes.outgoing (naturalKeycodes.atPosition (0, 3)).val).card = 5 :=
  naturalKeycodes.card_outgoing_index _ (by decide)

/-! ## All four bigram categories -/

theorem kind_repeated : positionKind (0, 0) (0, 0) = .repeated := by decide
theorem kind_sameFinger : positionKind (0, 0) (1, 0) = .sameFinger := by decide
theorem kind_sameHand : positionKind (0, 0) (1, 1) = .sameHandDifferentFinger := by decide
theorem kind_oppositeHands : positionKind (0, 0) (1, 9) = .oppositeHands := by decide

theorem classify_repeated :
    naturalKeycodes.classify (naturalKeycodes.atPosition (0, 0))
      (naturalKeycodes.atPosition (0, 0)) = .repeated :=
  (naturalKeycodes.classify_atPosition _ _).trans kind_repeated

theorem classify_sameFinger :
    naturalKeycodes.classify (naturalKeycodes.atPosition (0, 0))
      (naturalKeycodes.atPosition (1, 0)) = .sameFinger :=
  (naturalKeycodes.classify_atPosition _ _).trans kind_sameFinger

theorem classify_sameHand :
    naturalKeycodes.classify (naturalKeycodes.atPosition (0, 0))
      (naturalKeycodes.atPosition (1, 1)) = .sameHandDifferentFinger :=
  (naturalKeycodes.classify_atPosition _ _).trans kind_sameHand

theorem classify_oppositeHands :
    naturalKeycodes.classify (naturalKeycodes.atPosition (0, 0))
      (naturalKeycodes.atPosition (1, 9)) = .oppositeHands :=
  (naturalKeycodes.classify_atPosition _ _).trans kind_oppositeHands

/-- The category counts hold over an infinite ambient keycode type too. -/
theorem naturalKeycodes_category_counts :
    Fintype.card {ab : UsedKey naturalKeycodes × UsedKey naturalKeycodes //
        naturalKeycodes.classify ab.1 ab.2 = .sameHandDifferentFinger} = 324 :=
  naturalKeycodes.card_sameHandDifferentFinger

/-! ## Arbitrary rearrangement inside an index column -/

/-- A six-cycle through both halves of the left index region. -/
def leftIndexCycle : Equiv.Perm Position :=
  Equiv.swap (0, 3) (0, 4) * Equiv.swap (0, 4) (1, 3) * Equiv.swap (1, 3) (1, 4) *
    Equiv.swap (1, 4) (2, 3) * Equiv.swap (2, 3) (2, 4)

theorem leftIndexCycle_mem : leftIndexCycle ∈ ColumnSymmetry := by
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ ?_ ?_) ?_) ?_) ?_ <;>
      exact swap_mem_columnSymmetry (by decide)

/-- Relabelling the left index column by a six-cycle. -/
def indexCycled : Layout Position := identityLayout.reindex leftIndexCycle

theorem index_cycle_equivalent : identityLayout.Equivalent indexCycled :=
  identityLayout.equivalent_reindex ⟨leftIndexCycle, leftIndexCycle_mem⟩

theorem index_cycle_moves_keys : indexCycled.keyAt (0, 3) ≠ identityLayout.keyAt (0, 3) := by
  decide

/-! ## Exchanging whole columns across hands -/

/-- Exchange the left and right pinky columns, all three rows at once. -/
def pinkyColumnSwap : Equiv.Perm Position :=
  Equiv.swap (0, 0) (0, 9) * Equiv.swap (1, 0) (1, 9) * Equiv.swap (2, 0) (2, 9)

theorem pinkyColumnSwap_mem : pinkyColumnSwap ∈ ColumnSymmetry :=
  mem_columnSymmetry_of_perm (Equiv.swap ColumnId.leftPinky ColumnId.rightPinky) (by decide)

/-- The whole-column exchange across hands. -/
def pinkiesSwapped : Layout Position := identityLayout.reindex pinkyColumnSwap

theorem pinky_swap_equivalent : identityLayout.Equivalent pinkiesSwapped :=
  identityLayout.equivalent_reindex ⟨pinkyColumnSwap, pinkyColumnSwap_mem⟩

theorem pinky_swap_crosses_hands :
    (columnAt ((0 : Fin 3), (0 : Fin 10)).2).hand ≠
      (columnAt (pinkyColumnSwap ((0 : Fin 3), (0 : Fin 10))).2).hand := by decide

/-! ## Swap sizes -/

theorem swap_simple_simple :
    (identityLayout.sfbsChanged (0, 0) (0, 1)).card = 16 :=
  identityLayout.card_sfbsChanged_simple_simple (by decide) (by decide) (by decide)

theorem swap_simple_index :
    (identityLayout.sfbsChanged (0, 0) (0, 3)).card = 28 :=
  identityLayout.card_sfbsChanged_simple_index (by decide) (by decide) (by decide)

theorem swap_index_index :
    (identityLayout.sfbsChanged (0, 3) (0, 5)).card = 40 :=
  identityLayout.card_sfbsChanged_index_index (by decide) (by decide) (by decide)

theorem swap_within_column :
    (identityLayout.sfbsChanged (0, 0) (1, 0)).card = 0 :=
  identityLayout.card_sfbsChanged_sameColumn (by decide)

theorem swap_within_column_preserves :
    identityLayout.Equivalent (identityLayout.swapPositions (0, 0) (1, 0)) :=
  identityLayout.equivalent_swapPositions (by decide)

theorem swap_across_columns_breaks :
    ¬identityLayout.Equivalent (identityLayout.swapPositions (0, 0) (0, 1)) := by
  rw [identityLayout.equivalent_swapPositions_iff]
  decide

/-! ## Every distinct pair of positions -/

/-- Reading order index of a grid position. -/
def posIndex (p : Position) : Nat := p.1.val * 10 + p.2.val

/-- The 435 unordered pairs of distinct grid positions, listed once each.
A `List` keeps the exhaustive checks below inside the kernel's budget. -/
def distinctPositionPairs : List (Position × Position) :=
  (allPositions.flatMap fun p => allPositions.map fun q => (p, q)).filter
    fun pq => decide (posIndex pq.1 < posIndex pq.2)

theorem length_distinctPositionPairs : distinctPositionPairs.length = 435 := by decide

/-- The listing is exactly the pairs in reading order, so every unordered pair of distinct
positions appears once. -/
theorem mem_distinctPositionPairs (p q : Position) :
    (p, q) ∈ distinctPositionPairs ↔ posIndex p < posIndex q := by
  simp [distinctPositionPairs, mem_allPositions]

set_option maxHeartbeats 1000000 in
/-- Checked over every one of the 435 pairs: a swap changes nothing exactly when the two
positions share a finger column, and otherwise changes 16, 28 or 40 ordered bigrams. -/
theorem swaps_exhaustive :
    ∀ pq ∈ distinctPositionPairs,
      (changedCount pq.1 pq.2 = 0 ↔ colOf pq.1 = colOf pq.2) ∧
        (changedCount pq.1 pq.2 = 0 ∨ changedCount pq.1 pq.2 = 16 ∨
          changedCount pq.1 pq.2 = 28 ∨ changedCount pq.1 pq.2 = 40) := by decide

theorem changedCount_exhaustive (pq : Position × Position) (h : pq ∈ distinctPositionPairs) :
    changedCount pq.1 pq.2 = 0 ∨ changedCount pq.1 pq.2 = 16 ∨
      changedCount pq.1 pq.2 = 28 ∨ changedCount pq.1 pq.2 = 40 :=
  (swaps_exhaustive pq h).2

theorem swap_preserves_iff_exhaustive (pq : Position × Position)
    (h : pq ∈ distinctPositionPairs) :
    changedCount pq.1 pq.2 = 0 ↔ colOf pq.1 = colOf pq.2 :=
  (swaps_exhaustive pq h).1

/-- Hence for every layout and every one of the 435 pairs, a swap changes 0, 16, 28 or 40
ordered same-finger bigrams. -/
theorem swap_sizes_exhaustive {Keycode : Type} [DecidableEq Keycode] (L : Layout Keycode) :
    ∀ pq ∈ distinctPositionPairs,
      (L.sfbsChanged pq.1 pq.2).card = 0 ∨ (L.sfbsChanged pq.1 pq.2).card = 16 ∨
        (L.sfbsChanged pq.1 pq.2).card = 28 ∨ (L.sfbsChanged pq.1 pq.2).card = 40 := by
  intro pq hpq
  rw [L.card_sfbsChanged_eq]
  exact changedCount_exhaustive pq hpq

/-! ## Measuring layouts against a corpus

`sfbCount` is computed here through `Layout.kindCount_sameFinger`, so `decide` runs the cheap
list-based classifier instead of rebuilding `Layout.sfbs` for every bigram. -/

/-- A short keystroke stream over `naturalKeycodes` touching every category, plus one keycode the
layout does not use. -/
def sampleCorpus : Corpus Nat := [0, 10, 1, 20, 3, 14, 9, 9, 100]

theorem sample_bigrams :
    Fern.Ngram.bigrams sampleCorpus =
      [(0, 10), (10, 1), (1, 20), (20, 3), (3, 14), (14, 9), (9, 9), (9, 100)] := rfl

theorem sample_sfbCount : naturalKeycodes.sfbCount sampleCorpus = 2 := by
  rw [← Layout.kindCount_sameFinger]
  decide

theorem sample_split :
    naturalKeycodes.kindCount .repeated sampleCorpus = 1 ∧
      naturalKeycodes.kindCount .sameFinger sampleCorpus = 2 ∧
      naturalKeycodes.kindCount .sameHandDifferentFinger sampleCorpus = 3 ∧
      naturalKeycodes.kindCount .oppositeHands sampleCorpus = 1 ∧
      naturalKeycodes.unmappedCount sampleCorpus = 1 := by decide

theorem sample_not_supported : ¬naturalKeycodes.Supports sampleCorpus := by decide

/-- The same stream without the unused keycode. -/
def supportedCorpus : Corpus Nat := [0, 10, 1, 20, 3, 14, 9, 9]

theorem supportedCorpus_supported : naturalKeycodes.Supports supportedCorpus := by decide

theorem supported_split_is_total :
    naturalKeycodes.kindCount .repeated supportedCorpus
        + naturalKeycodes.kindCount .sameFinger supportedCorpus
        + naturalKeycodes.kindCount .sameHandDifferentFinger supportedCorpus
        + naturalKeycodes.kindCount .oppositeHands supportedCorpus
      = supportedCorpus.length - 1 :=
  naturalKeycodes.kindCount_sum_of_supports supportedCorpus_supported

/-! ## Equivalence fixes same-finger counts but not the hand split -/

/-- Two keystrokes that `simpleColumnSwap` moves onto opposite hands. -/
def handCorpus : Corpus Position := [(0, 0), (0, 1)]

theorem hand_corpus_sfbCount_agrees :
    identityLayout.sfbCount handCorpus = simpleColumnSwap.sfbCount handCorpus :=
  simple_column_swap_equivalent.sfbCount_eq handCorpus

/-- Equivalent layouts, same corpus, different hand split: equivalence forgets hand. -/
theorem hand_split_differs :
    identityLayout.kindCount .oppositeHands handCorpus = 0 ∧
      simpleColumnSwap.kindCount .oppositeHands handCorpus = 1 := by decide

/-! ## Swaps against a corpus -/

theorem pinky_swap_changes_count :
    (naturalKeycodes.swapPositions (0, 0) (0, 9)).sfbCount supportedCorpus = 1 := by
  rw [← Layout.kindCount_sameFinger]
  decide

theorem pinky_swap_touches :
    touchCount (naturalKeycodes.keyAt (0, 0)) (naturalKeycodes.keyAt (0, 9)) supportedCorpus
      = 3 := by decide

theorem untouched_swap_preserves_count :
    (naturalKeycodes.swapPositions (2, 8) (2, 9)).sfbCount supportedCorpus
      = naturalKeycodes.sfbCount supportedCorpus :=
  naturalKeycodes.sfbCount_swap_of_not_mem (by decide) (by decide)

/-! ## Reading text through a keymap -/

/-- Sends `a`, `b` and `c` to three left-hand keys and ignores everything else. -/
def abcKeymap : Keymap Nat :=
  ⟨fun ch => if ch = 'a' then some 0 else if ch = 'b' then some 10 else
    if ch = 'c' then some 1 else none⟩

theorem unmapped_characters_dropped : abcKeymap.corpus ['a', '?', 'b'] = [0, 10] := by decide

/-- Dropping an unmapped character creates a bigram the text never contained: reading the text
first yields `(0, 10)`, while mapping the text's own bigrams yields nothing. -/
theorem keymap_joins_neighbours :
    Fern.Ngram.bigrams (abcKeymap.corpus ['a', '?', 'b']) = [(0, 10)] ∧
      (Fern.Ngram.bigrams ['a', '?', 'b']).filterMap
          (fun p => (abcKeymap.toKeycode p.1).bind fun x =>
            (abcKeymap.toKeycode p.2).map fun y => (x, y)) = [] := by decide

theorem abcKeymap_mapsInto : abcKeymap.MapsInto naturalKeycodes.usedKeys := by
  intro ch k h
  simp only [abcKeymap] at h
  split_ifs at h <;> cases h <;> decide

theorem abc_text_is_supported (cs : List Char) : naturalKeycodes.Supports (abcKeymap.corpus cs) :=
  naturalKeycodes.supports_corpus abcKeymap_mapsInto cs

/-! ## Reading prose

`bigramsOf` reads the text's own bigrams, so an unmapped character breaks the stream instead of
joining its neighbours the way `corpus` does. -/

theorem bigramsOf_breaks_at_unmapped : abcKeymap.bigramsOf ['a', '?', 'b'] = [] := rfl

theorem bigramsOf_breaks_at_space : abcKeymap.bigramsOf ['a', 'b', ' ', 'c'] = [(0, 10)] := rfl

theorem segments_split_at_space : abcKeymap.segments ['a', 'b', ' ', 'c'] = [[0, 10], [1]] := rfl

/-- A space between two keys makes a spacegram, not a skipgram. -/
theorem space_makes_spacegram : abcKeymap.spacegramsOf ['a', ' ', 'b'] = [(0, 10)] := rfl

theorem space_is_not_skipgram : abcKeymap.skipgramsOf ['a', ' ', 'b'] = [] := rfl

/-- A key between two keys makes a skipgram, not a spacegram. -/
theorem key_makes_skipgram : abcKeymap.skipgramsOf ['a', 'c', 'b'] = [(0, 10)] := rfl

theorem key_is_not_spacegram : abcKeymap.spacegramsOf ['a', 'c', 'b'] = [] := rfl

/-- A newline is not a space, so separate lines never form a spacegram. -/
theorem newline_is_not_spacegram : abcKeymap.spacegramsOf ['a', '\n', 'b'] = [] := rfl

end Fern.Ortholinear.Examples
