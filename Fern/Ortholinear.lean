module
public import Fern.Model
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# The 3×10 ortholinear keyboard

A geometric column is one grid coordinate. A finger column is the entire region
operated by one finger on one hand, including both geometric index columns.
Concrete layouts retain positions; equivalence forgets positions and finger labels.
-/

@[expose] public section

namespace Fern.Ortholinear

abbrev Position := Fin 3 × Fin 10
abbrev Bigram (Keycode : Type) := Keycode × Keycode

/-- Thirty distinct keycodes arranged on the grid. The ambient type may be larger. -/
structure Layout (Keycode : Type) where
  keyAt : Position → Keycode
  unique : Function.Injective keyAt

inductive ColumnKind where
  | simple
  | index
  deriving DecidableEq, Fintype, Repr

def ColumnKind.width : ColumnKind → Nat
  | .simple => 1
  | .index => 2

inductive ColumnId where
  | leftPinky | leftRing | leftMiddle | leftIndex
  | rightIndex | rightMiddle | rightRing | rightPinky
  deriving DecidableEq, Fintype, Repr

def ColumnId.hand : ColumnId → Hand
  | .leftPinky | .leftRing | .leftMiddle | .leftIndex => .left
  | _ => .right

def ColumnId.finger : ColumnId → Finger
  | .leftPinky | .rightPinky => .pinky
  | .leftRing | .rightRing => .ring
  | .leftMiddle | .rightMiddle => .middle
  | .leftIndex | .rightIndex => .index

def ColumnId.kind : ColumnId → ColumnKind
  | .leftIndex | .rightIndex => .index
  | _ => .simple

/-- The leftmost geometric column occupied by a finger column. -/
def ColumnId.start : ColumnId → Nat
  | .leftPinky => 0 | .leftRing => 1 | .leftMiddle => 2 | .leftIndex => 3
  | .rightIndex => 5 | .rightMiddle => 7 | .rightRing => 8 | .rightPinky => 9

def columnAt (x : Fin 10) : ColumnId :=
  match x.val with
  | 0 => .leftPinky | 1 => .leftRing | 2 => .leftMiddle
  | 3 | 4 => .leftIndex
  | 5 | 6 => .rightIndex
  | 7 => .rightMiddle | 8 => .rightRing | _ => .rightPinky

/-- Outermost to innermost, with thumbs outside this model. -/
def fingerRank : Finger → Option Nat
  | .pinky => some 0 | .ring => some 1 | .middle => some 2
  | .index => some 3 | .thumb => none

def ColumnId.positions (c : ColumnId) : Finset Position :=
  Finset.univ.filter fun p => columnAt p.2 = c

def ColumnId.horizontal (c : ColumnId) : Finset (Fin 10) :=
  Finset.univ.filter fun x => c.start ≤ x.val ∧ x.val < c.start + c.kind.width

@[simp] theorem mem_positions (c : ColumnId) (p : Position) :
    p ∈ c.positions ↔ columnAt p.2 = c := by
  simp [ColumnId.positions]

theorem grid_card : Fintype.card Position = 30 := by decide

theorem column_count : Fintype.card ColumnId = 8 := by decide

theorem simple_column_count :
    (Finset.univ.filter fun c : ColumnId => c.kind = .simple).card = 6 := by decide

theorem index_column_count :
    (Finset.univ.filter fun c : ColumnId => c.kind = .index).card = 2 := by decide

theorem column_finger_not_thumb (c : ColumnId) : c.finger ≠ .thumb := by
  cases c <;> decide

theorem simple_iff_finger (c : ColumnId) :
    c.kind = .simple ↔ c.finger = .pinky ∨ c.finger = .ring ∨ c.finger = .middle := by
  cases c <;> decide

theorem index_iff_finger (c : ColumnId) : c.kind = .index ↔ c.finger = .index := by
  cases c <;> decide

theorem hand_finger_unique (c d : ColumnId) :
    c.hand = d.hand ∧ c.finger = d.finger ↔ c = d := by
  cases c <;> cases d <;> decide

/-- Each region is exactly all three rows times a contiguous horizontal interval. -/
theorem positions_rectangle (c : ColumnId) :
    c.positions = Finset.univ ×ˢ c.horizontal := by
  cases c <;> decide

theorem horizontal_card (c : ColumnId) : c.horizontal.card = c.kind.width := by
  cases c <;> decide

theorem positions_card (c : ColumnId) : c.positions.card = 3 * c.kind.width := by
  cases c <;> decide

theorem positions_cover :
    Finset.univ.biUnion ColumnId.positions = (Finset.univ : Finset Position) := by decide

theorem positions_disjoint {c d : ColumnId} (h : c ≠ d) :
    Disjoint c.positions d.positions := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((mem_positions c p).mp hp |>.symm.trans ((mem_positions d p).mp hq))

def otherHand : Hand → Hand
  | .left => .right
  | .right => .left

def reflect (p : Position) : Position :=
  (p.1, ⟨9 - p.2.val, by omega⟩)

theorem reflect_involutive : Function.Involutive reflect := by
  change ∀ p, reflect (reflect p) = p
  decide

theorem reflect_row (p : Position) : (reflect p).1 = p.1 := rfl

theorem reflect_hand (p : Position) :
    (columnAt (reflect p).2).hand = otherHand (columnAt p.2).hand := by
  revert p; decide

theorem reflect_finger (p : Position) :
    (columnAt (reflect p).2).finger = (columnAt p.2).finger := by
  revert p; decide

/-- Distance from the nearer outside edge, in geometric columns. -/
def inwardDistance (x : Fin 10) : Nat := min x.val (9 - x.val)

theorem outer_to_inner_order (x : Fin 10) :
    fingerRank (columnAt x).finger = some (min (inwardDistance x) 3) := by
  revert x; decide

def innerIndexPositions (h : Hand) : Finset Position :=
  Finset.univ.filter fun p => p.2 = (match h with | .left => 4 | .right => 5)

def indexColumn (h : Hand) : ColumnId :=
  match h with | .left => .leftIndex | .right => .rightIndex

theorem inner_index_rectangle (h : Hand) :
    innerIndexPositions h =
      Finset.univ ×ˢ ({match h with | .left => 4 | .right => 5} : Finset (Fin 10)) := by
  cases h <;> decide

theorem inner_index_card (h : Hand) : (innerIndexPositions h).card = 3 := by
  cases h <;> decide

theorem inner_index_subset (h : Hand) : innerIndexPositions h ⊆ (indexColumn h).positions := by
  cases h <;> decide

theorem inner_index_closer (h : Hand) :
    ∀ p ∈ innerIndexPositions h, ∀ q ∈ (indexColumn h).positions \ innerIndexPositions h,
      inwardDistance q.2 < inwardDistance p.2 := by
  cases h <;> decide

theorem reflect_inner_index (h : Hand) :
    (innerIndexPositions h).image reflect = innerIndexPositions (otherHand h) := by
  cases h <;> decide

variable {Keycode : Type} [DecidableEq Keycode]

def Layout.usedKeys (L : Layout Keycode) : Finset Keycode :=
  Finset.univ.image L.keyAt

def Layout.columnKeys (L : Layout Keycode) (c : ColumnId) : Finset Keycode :=
  c.positions.image L.keyAt

@[simp] theorem Layout.usedKeys_card (L : Layout Keycode) : L.usedKeys.card = 30 := by
  rw [Layout.usedKeys, Finset.card_image_of_injective _ L.unique]
  decide

@[simp] theorem Layout.columnKeys_card (L : Layout Keycode) (c : ColumnId) :
    (L.columnKeys c).card = 3 * c.kind.width := by
  rw [Layout.columnKeys, Finset.card_image_of_injective _ L.unique, positions_card]

theorem Layout.columnKeys_nontrivial (L : Layout Keycode) (c : ColumnId) :
    1 < (L.columnKeys c).card := by
  rw [L.columnKeys_card]; cases c <;> decide

theorem Layout.columnKeys_nonempty (L : Layout Keycode) (c : ColumnId) :
    (L.columnKeys c).Nonempty :=
  Finset.card_pos.mp (by have := L.columnKeys_nontrivial c; omega)

@[simp] theorem Layout.keyAt_mem_columnKeys (L : Layout Keycode) (p : Position) (c : ColumnId) :
    L.keyAt p ∈ L.columnKeys c ↔ columnAt p.2 = c := by
  simp [Layout.columnKeys, Finset.mem_image, L.unique.eq_iff]

theorem Layout.columnKeys_disjoint (L : Layout Keycode) {c d : ColumnId} (h : c ≠ d) :
    Disjoint (L.columnKeys c) (L.columnKeys d) := by
  apply Finset.disjoint_left.mpr
  intro k hk hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  exact h ((mem_positions c p).mp hp |>.symm.trans ((L.keyAt_mem_columnKeys p d).mp hd))

theorem Layout.columnKeys_cover (L : Layout Keycode) :
    Finset.univ.biUnion L.columnKeys = L.usedKeys := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Layout.usedKeys, Finset.mem_image]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hc
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨columnAt p.2, (L.keyAt_mem_columnKeys p _).mpr rfl⟩

/-- A column retains the concrete layout and the finger region it refers to. -/
abbrev Column (Keycode : Type) := Layout Keycode × ColumnId

def Column.hand (c : Column Keycode) : Hand := c.2.hand
def Column.finger (c : Column Keycode) : Finger := c.2.finger
def Column.kind (c : Column Keycode) : ColumnKind := c.2.kind
def Column.positions (c : Column Keycode) : Finset Position := c.2.positions
def Column.keys (c : Column Keycode) : Finset Keycode := c.1.columnKeys c.2

def columnSFBs (c : Column Keycode) : Finset (Bigram Keycode) := c.keys.offDiag

@[simp] theorem mem_columnSFBs (c : Column Keycode) (a b : Keycode) :
    (a, b) ∈ columnSFBs c ↔ a ∈ c.keys ∧ b ∈ c.keys ∧ a ≠ b :=
  Finset.mem_offDiag

theorem columnSFBs_card (c : Column Keycode) :
    (columnSFBs c).card = c.keys.card * (c.keys.card - 1) := by
  simp only [columnSFBs, Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]

def Layout.columns (L : Layout Keycode) : Finset (Finset Keycode) :=
  Finset.univ.image L.columnKeys

def Column.Equivalent (c d : Column Keycode) : Prop := c.keys = d.keys
def Layout.Equivalent (L M : Layout Keycode) : Prop := L.columns = M.columns

theorem Column.equivalent_refl (c : Column Keycode) : c.Equivalent c := rfl
theorem Column.equivalent_symm {c d : Column Keycode} (h : c.Equivalent d) :
    d.Equivalent c := h.symm
theorem Column.equivalent_trans {c d e : Column Keycode}
    (h : c.Equivalent d) (h' : d.Equivalent e) : c.Equivalent e := h.trans h'

theorem Layout.equivalent_refl (L : Layout Keycode) : L.Equivalent L := rfl
theorem Layout.equivalent_symm {L M : Layout Keycode} (h : L.Equivalent M) :
    M.Equivalent L := h.symm
theorem Layout.equivalent_trans {L M N : Layout Keycode}
    (h : L.Equivalent M) (h' : M.Equivalent N) : L.Equivalent N := h.trans h'

theorem Column.equivalent_sfb_eq {c d : Column Keycode} (h : c.Equivalent d) :
    columnSFBs c = columnSFBs d := congrArg Finset.offDiag h

def Layout.sfbs (L : Layout Keycode) : Finset (Bigram Keycode) :=
  L.columns.biUnion Finset.offDiag

def IsSFB (L : Layout Keycode) (b : Bigram Keycode) : Prop := b ∈ L.sfbs

instance (L : Layout Keycode) (b : Bigram Keycode) : Decidable (IsSFB L b) :=
  inferInstanceAs (Decidable (b ∈ L.sfbs))

theorem Layout.mem_sfbs (L : Layout Keycode) (a b : Keycode) :
    (a, b) ∈ L.sfbs ↔ ∃ c, a ∈ L.columnKeys c ∧ b ∈ L.columnKeys c ∧ a ≠ b := by
  simp [Layout.sfbs, Layout.columns, Finset.mem_offDiag]

theorem isSFB_iff (L : Layout Keycode) (a b : Keycode) :
    IsSFB L (a, b) ↔ ∃ c, a ∈ L.columnKeys c ∧ b ∈ L.columnKeys c ∧ a ≠ b :=
  L.mem_sfbs a b

theorem Layout.equivalent_sfb_eq {L M : Layout Keycode} (h : L.Equivalent M) :
    L.sfbs = M.sfbs := congrArg (fun s => s.biUnion Finset.offDiag) h

theorem Layout.column_of_shared_key (L : Layout Keycode) {c d : ColumnId} {a : Keycode}
    (hc : a ∈ L.columnKeys c) (hd : a ∈ L.columnKeys d) : c = d := by
  by_contra h
  exact Finset.disjoint_left.mp (L.columnKeys_disjoint h) hc hd

theorem Layout.columnKeys_injective (L : Layout Keycode) :
    Function.Injective L.columnKeys := by
  intro c d h
  obtain ⟨a, ha⟩ := L.columnKeys_nonempty c
  exact L.column_of_shared_key ha (h ▸ ha)

theorem Layout.columns_card (L : Layout Keycode) : L.columns.card = 8 := by
  rw [Layout.columns, Finset.card_image_of_injective _ L.columnKeys_injective]
  decide

/-- SFB destinations from a given keycode; the keycode itself is excluded. -/
def Layout.outgoing (L : Layout Keycode) (a : Keycode) : Finset Keycode :=
  (L.sfbs.filter fun b => b.1 = a).image Prod.snd

@[simp] theorem Layout.mem_outgoing (L : Layout Keycode) (a b : Keycode) :
    b ∈ L.outgoing a ↔ (a, b) ∈ L.sfbs := by
  have aux (s : Finset (Bigram Keycode)) :
      b ∈ (s.filter fun p => p.1 = a).image Prod.snd ↔ (a, b) ∈ s := by
    simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨h, rfl⟩, rfl⟩
      exact h
    · intro h
      exact ⟨a, b, ⟨h, rfl⟩, rfl⟩
  exact aux L.sfbs

/-- Recover a whole finger column from any one of its keys and that key's SFBs. -/
theorem Layout.recover_column (L : Layout Keycode) (c : ColumnId) {a : Keycode}
    (ha : a ∈ L.columnKeys c) : L.columnKeys c = insert a (L.outgoing a) := by
  ext b
  simp only [Finset.mem_insert, L.mem_outgoing, L.mem_sfbs]
  constructor
  · intro hb
    by_cases h : b = a
    · exact Or.inl h
    · exact Or.inr ⟨c, ha, hb, Ne.symm h⟩
  · rintro (rfl | ⟨d, had, hbd, _⟩)
    · exact ha
    · have h := L.column_of_shared_key ha had
      simpa [h] using hbd

section
-- Keep the enumerated SFB set abstract while transferring membership between layouts.
attribute [local irreducible] Layout.sfbs

theorem Layout.match_column_of_sfbs_eq {L M : Layout Keycode} (h : L.sfbs = M.sfbs)
    (c : ColumnId) : ∃ d, L.columnKeys c = M.columnKeys d := by
  obtain ⟨a, ha⟩ := L.columnKeys_nonempty c
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (L.columnKeys_nontrivial c) a
  have witness : ∃ d : ColumnId, a ∈ L.columnKeys d ∧ b ∈ L.columnKeys d ∧ a ≠ b :=
    ⟨c, ha, hb, Ne.symm hba⟩
  have habL := Iff.mpr (L.mem_sfbs a b) witness
  have hab : (a, b) ∈ M.sfbs :=
    Eq.mp (congrArg (fun s : Finset (Bigram Keycode) => (a, b) ∈ s) h) habL
  obtain ⟨d, had, _, _⟩ := (M.mem_sfbs a b).mp hab
  refine ⟨d, ?_⟩
  have hout : L.outgoing a = M.outgoing a := by
    unfold Layout.outgoing
    rw [h]
  exact (L.recover_column c ha).trans
    ((congrArg (fun s : Finset Keycode => insert a s) hout).trans
      (M.recover_column d had).symm)

end

/-- Column membership is exactly the information retained by the full SFB set. -/
theorem Layout.equivalent_iff_sfbs_eq (L M : Layout Keycode) :
    L.Equivalent M ↔ L.sfbs = M.sfbs := by
  constructor
  · exact Layout.equivalent_sfb_eq
  · intro h
    apply Finset.Subset.antisymm
    · intro s hs
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨d, hd⟩ := Layout.match_column_of_sfbs_eq h c
      exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd.symm⟩
    · intro s hs
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨c, hc⟩ := Layout.match_column_of_sfbs_eq h.symm d
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc.symm⟩

/-- The SFB relation on positions, before assigning keycodes. -/
def positionSFBs : Finset (Position × Position) :=
  Finset.univ.filter fun pq => columnAt pq.1.2 = columnAt pq.2.2 ∧ pq.1 ≠ pq.2

set_option maxRecDepth 4096 in
theorem positionSFBs_card : positionSFBs.card = 96 := by decide

def Layout.bigramAt (L : Layout Keycode) (pq : Position × Position) : Bigram Keycode :=
  (L.keyAt pq.1, L.keyAt pq.2)

omit [DecidableEq Keycode] in
theorem Layout.bigramAt_injective (L : Layout Keycode) : Function.Injective L.bigramAt := by
  intro p q h
  exact Prod.ext (L.unique (congrArg Prod.fst h)) (L.unique (congrArg Prod.snd h))

theorem Layout.sfbs_eq_image (L : Layout Keycode) :
    L.sfbs = positionSFBs.image L.bigramAt := by
  ext ⟨a, b⟩
  rw [L.mem_sfbs]
  constructor
  · rintro ⟨c, ha, hb, hab⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨(p, q), ?_, rfl⟩
    simp only [positionSFBs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨((mem_positions c p).mp hp).trans ((mem_positions c q).mp hq).symm,
      fun h => hab (congrArg L.keyAt h)⟩
  · intro h
    obtain ⟨⟨p, q⟩, hpq, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hc, hne⟩ := (Finset.mem_filter.mp hpq).2
    cases heq
    refine ⟨columnAt p.2, (L.keyAt_mem_columnKeys p _).mpr rfl,
      (L.keyAt_mem_columnKeys q _).mpr hc.symm, ?_⟩
    exact fun h => hne (L.unique h)

theorem Layout.sfbs_card (L : Layout Keycode) : L.sfbs.card = 96 := by
  rw [L.sfbs_eq_image, Finset.card_image_of_injective _ L.bigramAt_injective,
    positionSFBs_card]

theorem simple_columnSFBs_card (c : Column Keycode) (h : c.kind = .simple) :
    (columnSFBs c).card = 6 := by
  rw [columnSFBs_card]
  change (c.1.columnKeys c.2).card * ((c.1.columnKeys c.2).card - 1) = 6
  rw [c.1.columnKeys_card]
  change c.2.kind = .simple at h
  rw [h]; decide

theorem index_columnSFBs_card (c : Column Keycode) (h : c.kind = .index) :
    (columnSFBs c).card = 30 := by
  rw [columnSFBs_card]
  change (c.1.columnKeys c.2).card * ((c.1.columnKeys c.2).card - 1) = 30
  rw [c.1.columnKeys_card]
  change c.2.kind = .index at h
  rw [h]; decide

end Fern.Ortholinear
