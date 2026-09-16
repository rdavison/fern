module
public import Fern.Ortholinear

/-!
# Repertoires, lookup, and same-column structure

A `Repertoire` fixes the thirty keycodes a layout may use, so that layouts over an infinite
ambient keycode type still form a finite collection. `Layout.positionOf` is the computable
inverse of `keyAt`, and `UsedKey` packages a keycode together with the proof that the layout
uses it, making position, column, hand, finger and row lookups total.
-/

@[expose] public section

namespace Fern.Ortholinear

/-- A fixed repertoire: exactly thirty keycodes drawn from a possibly infinite ambient type. -/
structure Repertoire (Keycode : Type) where
  keys : Finset Keycode
  card_eq : keys.card = 30

variable {Keycode : Type} [DecidableEq Keycode]

/-- Layouts whose used keycodes are exactly the repertoire `R`. -/
def LayoutOn (R : Repertoire Keycode) : Type := {L : Layout Keycode // L.usedKeys = R.keys}

@[simp] theorem Layout.mem_usedKeys (L : Layout Keycode) (k : Keycode) :
    k ∈ L.usedKeys ↔ ∃ p, L.keyAt p = k := by
  simp [Layout.usedKeys]

theorem Layout.keyAt_mem_usedKeys (L : Layout Keycode) (p : Position) :
    L.keyAt p ∈ L.usedKeys := by simp

/-! ### Computable lookup -/

/-- Every grid position, in row-major order. -/
def allPositions : List Position :=
  (List.finRange 3).flatMap fun r => (List.finRange 10).map fun c => (r, c)

theorem mem_allPositions (p : Position) : p ∈ allPositions := by
  revert p; decide

/-- The position holding `k`, or `none` when the layout does not use `k`. -/
def Layout.positionOf (L : Layout Keycode) (k : Keycode) : Option Position :=
  allPositions.find? fun p => decide (L.keyAt p = k)

@[simp] theorem Layout.positionOf_eq_some (L : Layout Keycode) (k : Keycode) (p : Position) :
    L.positionOf k = some p ↔ L.keyAt p = k := by
  constructor
  · intro h
    have := List.find?_some h
    simpa using this
  · intro h
    match hq : L.positionOf k with
    | none =>
        rw [Layout.positionOf, List.find?_eq_none] at hq
        exact absurd (hq p (mem_allPositions p)) (by simpa using h)
    | some q =>
        have hq' : L.keyAt q = k := by
          have := List.find?_some hq
          simpa using this
        rw [L.unique (hq'.trans h.symm)]

@[simp] theorem Layout.positionOf_eq_none (L : Layout Keycode) (k : Keycode) :
    L.positionOf k = none ↔ k ∉ L.usedKeys := by
  constructor
  · intro h hk
    obtain ⟨p, hp⟩ := (L.mem_usedKeys k).mp hk
    rw [← L.positionOf_eq_some k p] at hp
    simp [hp] at h
  · intro hk
    match hq : L.positionOf k with
    | none => rfl
    | some q =>
        exact absurd ((L.mem_usedKeys k).mpr ⟨q, (L.positionOf_eq_some k q).mp hq⟩) hk

theorem Layout.positionOf_keyAt (L : Layout Keycode) (p : Position) :
    L.positionOf (L.keyAt p) = some p :=
  (L.positionOf_eq_some _ p).mpr rfl

theorem Layout.positionOf_isSome (L : Layout Keycode) {k : Keycode} (hk : k ∈ L.usedKeys) :
    (L.positionOf k).isSome := by
  match hq : L.positionOf k with
  | none => exact absurd ((L.positionOf_eq_none k).mp hq) (by simpa using hk)
  | some _ => rfl

/-! ### Used keycodes as a subtype -/

/-- A keycode together with a proof that `L` uses it. -/
def UsedKey (L : Layout Keycode) : Type := {k : Keycode // k ∈ L.usedKeys}

instance (L : Layout Keycode) : DecidableEq (UsedKey L) := fun _ _ =>
  decidable_of_iff _ Subtype.ext_iff.symm

/-- The keycode at a position, as a used keycode. -/
def Layout.atPosition (L : Layout Keycode) (p : Position) : UsedKey L :=
  ⟨L.keyAt p, L.keyAt_mem_usedKeys p⟩

/-- Total position lookup on used keycodes. -/
def UsedKey.position {L : Layout Keycode} (k : UsedKey L) : Position :=
  (L.positionOf k.val).getD (0, 0)

@[simp] theorem UsedKey.keyAt_position {L : Layout Keycode} (k : UsedKey L) :
    L.keyAt k.position = k.val := by
  obtain ⟨p, hp⟩ := (L.mem_usedKeys k.val).mp k.property
  have : L.positionOf k.val = some p := (L.positionOf_eq_some _ p).mpr hp
  simp [UsedKey.position, this, hp]

@[simp] theorem UsedKey.position_atPosition {L : Layout Keycode} (p : Position) :
    (L.atPosition p).position = p :=
  L.unique (UsedKey.keyAt_position (L.atPosition p))

@[simp] theorem Layout.atPosition_position {L : Layout Keycode} (k : UsedKey L) :
    L.atPosition k.position = k :=
  Subtype.ext (UsedKey.keyAt_position k)

/-- Positions and used keycodes are in bijection. -/
def Layout.posEquiv (L : Layout Keycode) : Position ≃ UsedKey L where
  toFun := L.atPosition
  invFun := UsedKey.position
  left_inv := UsedKey.position_atPosition
  right_inv := Layout.atPosition_position

@[simp] theorem Layout.posEquiv_apply (L : Layout Keycode) (p : Position) :
    L.posEquiv p = L.atPosition p := rfl

@[simp] theorem Layout.posEquiv_symm_apply (L : Layout Keycode) (k : UsedKey L) :
    L.posEquiv.symm k = k.position := rfl

instance (L : Layout Keycode) : Fintype (UsedKey L) := Fintype.ofEquiv Position L.posEquiv

@[simp] theorem Layout.card_usedKey (L : Layout Keycode) : Fintype.card (UsedKey L) = 30 := by
  rw [Fintype.card_congr L.posEquiv.symm]
  decide

/-! ### Total geometric lookup on used keycodes -/

/-- The finger column operating a used keycode. -/
def UsedKey.column {L : Layout Keycode} (k : UsedKey L) : ColumnId := columnAt k.position.2

/-- The hand operating a used keycode. -/
def UsedKey.hand {L : Layout Keycode} (k : UsedKey L) : Hand := k.column.hand

/-- The finger operating a used keycode. -/
def UsedKey.finger {L : Layout Keycode} (k : UsedKey L) : Finger := k.column.finger

/-- The row holding a used keycode. -/
def UsedKey.row {L : Layout Keycode} (k : UsedKey L) : Fin 3 := k.position.1

/-- Whether a used keycode sits in an inner index region. -/
def UsedKey.isInnerIndex {L : Layout Keycode} (k : UsedKey L) : Bool :=
  decide (k.position ∈ innerIndexPositions k.hand)

@[simp] theorem UsedKey.mem_columnKeys {L : Layout Keycode} (k : UsedKey L) (c : ColumnId) :
    k.val ∈ L.columnKeys c ↔ k.column = c := by
  rw [← UsedKey.keyAt_position k, L.keyAt_mem_columnKeys]
  rfl

theorem UsedKey.mem_columnKeys_self {L : Layout Keycode} (k : UsedKey L) :
    k.val ∈ L.columnKeys k.column := (k.mem_columnKeys k.column).mpr rfl

@[simp] theorem UsedKey.column_atPosition {L : Layout Keycode} (p : Position) :
    (L.atPosition p).column = columnAt p.2 := by
  simp [UsedKey.column]

theorem Layout.atPosition_inj (L : Layout Keycode) {p q : Position}
    (h : L.atPosition p = L.atPosition q) : p = q :=
  L.unique (congrArg Subtype.val h)

theorem Layout.atPosition_inj_iff (L : Layout Keycode) (p q : Position) :
    L.atPosition p = L.atPosition q ↔ p = q :=
  ⟨L.atPosition_inj, fun h => by rw [h]⟩

/-! ### Same-finger bigram relation laws

`Layout.sfbs` is kept opaque below: downstream of `Fern.Ortholinear` it is an exposed
definition over concrete `Finset`s, and the unifier will otherwise try to evaluate the
whole eight-column union while checking membership hypotheses. -/

section
attribute [local irreducible] Layout.sfbs

theorem isSFB_congr {L M : Layout Keycode} (h : L.sfbs = M.sfbs) (b : Bigram Keycode) :
    IsSFB L b ↔ IsSFB M b := by
  unfold IsSFB
  rw [h]

theorem Layout.sfbs_symm (L : Layout Keycode) {a b : Keycode} (h : IsSFB L (a, b)) :
    IsSFB L (b, a) := by
  obtain ⟨c, ha, hb, hab⟩ := (isSFB_iff L a b).mp h
  exact (isSFB_iff L b a).mpr ⟨c, hb, ha, Ne.symm hab⟩

theorem Layout.sfbs_comm (L : Layout Keycode) (a b : Keycode) :
    IsSFB L (a, b) ↔ IsSFB L (b, a) :=
  ⟨L.sfbs_symm, L.sfbs_symm⟩

theorem Layout.sfbs_irrefl (L : Layout Keycode) (a : Keycode) : ¬IsSFB L (a, a) := by
  intro h
  obtain ⟨_, _, _, hne⟩ := (isSFB_iff L a a).mp h
  exact hne rfl

theorem Layout.not_mem_outgoing_self (L : Layout Keycode) (a : Keycode) :
    a ∉ L.outgoing a := by
  simp only [L.mem_outgoing]
  exact L.sfbs_irrefl a

/-- Two used keycodes are operated by the same finger column. -/
def SameColumn (L : Layout Keycode) (a b : UsedKey L) : Prop := a.column = b.column

instance (L : Layout Keycode) (a b : UsedKey L) : Decidable (SameColumn L a b) :=
  inferInstanceAs (Decidable (a.column = b.column))

theorem sameColumn_refl (L : Layout Keycode) (a : UsedKey L) : SameColumn L a a := rfl

theorem sameColumn_symm {L : Layout Keycode} {a b : UsedKey L} (h : SameColumn L a b) :
    SameColumn L b a := Eq.symm h

theorem sameColumn_trans {L : Layout Keycode} {a b c : UsedKey L}
    (h : SameColumn L a b) (h' : SameColumn L b c) : SameColumn L a c := Eq.trans h h'

theorem sameColumn_equivalence (L : Layout Keycode) : Equivalence (SameColumn L) :=
  ⟨sameColumn_refl L, sameColumn_symm, sameColumn_trans⟩

/-- Sharing a finger column is exactly being equal or forming a same-finger bigram. -/
theorem sameColumn_iff (L : Layout Keycode) (a b : UsedKey L) :
    SameColumn L a b ↔ a = b ∨ IsSFB L (a.val, b.val) := by
  constructor
  · intro h
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr ((isSFB_iff L a.val b.val).mpr ⟨a.column, a.mem_columnKeys_self,
        (b.mem_columnKeys a.column).mpr (Eq.symm h), fun hv => hab (Subtype.ext hv)⟩)
  · rintro (rfl | h)
    · rfl
    · obtain ⟨c, ha, hb, _⟩ := (isSFB_iff L a.val b.val).mp h
      exact Eq.trans ((a.mem_columnKeys c).mp ha) (Eq.symm ((b.mem_columnKeys c).mp hb))

/-- A same-finger bigram on used keycodes is exactly a shared column between distinct keys. -/
theorem isSFB_iff_sameColumn (L : Layout Keycode) (a b : UsedKey L) :
    IsSFB L (a.val, b.val) ↔ SameColumn L a b ∧ a ≠ b := by
  rw [isSFB_iff L a.val b.val]
  constructor
  · rintro ⟨c, ha, hb, hne⟩
    exact ⟨Eq.trans ((a.mem_columnKeys c).mp ha) (Eq.symm ((b.mem_columnKeys c).mp hb)),
      fun h => hne (congrArg Subtype.val h)⟩
  · rintro ⟨hc, hne⟩
    exact ⟨a.column, a.mem_columnKeys_self, (b.mem_columnKeys a.column).mpr (Eq.symm hc),
      fun hv => hne (Subtype.ext hv)⟩

theorem mem_outgoing_iff (L : Layout Keycode) (a b : UsedKey L) :
    b.val ∈ L.outgoing a.val ↔ SameColumn L a b ∧ a ≠ b := by
  rw [L.mem_outgoing]
  constructor
  · intro h
    refine ⟨(sameColumn_iff L a b).mpr (Or.inr h), ?_⟩
    rintro rfl
    exact L.sfbs_irrefl _ h
  · rintro ⟨hc, hne⟩
    rcases (sameColumn_iff L a b).mp hc with rfl | h
    · exact absurd rfl hne
    · exact h

/-! ### Counting same-finger partners -/

/-- The outgoing partners of a used keycode are the rest of its finger column. -/
theorem Layout.outgoing_eq (L : Layout Keycode) (k : UsedKey L) :
    L.outgoing k.val = (L.columnKeys k.column).erase k.val := by
  rw [L.recover_column k.column k.mem_columnKeys_self,
    Finset.erase_insert (L.not_mem_outgoing_self k.val)]

@[simp] theorem Layout.card_outgoing (L : Layout Keycode) (k : UsedKey L) :
    (L.outgoing k.val).card = 3 * k.column.kind.width - 1 := by
  have hins : L.columnKeys k.column = insert k.val (L.outgoing k.val) :=
    L.recover_column k.column k.mem_columnKeys_self
  have hcard : (L.columnKeys k.column).card = (L.outgoing k.val).card + 1 := by
    rw [hins, Finset.card_insert_of_notMem (L.not_mem_outgoing_self k.val)]
  rw [L.columnKeys_card] at hcard
  omega

/-- A key in a simple column has exactly two same-finger partners. -/
theorem Layout.card_outgoing_simple (L : Layout Keycode) (k : UsedKey L)
    (h : k.column.kind = .simple) : (L.outgoing k.val).card = 2 := by
  rw [L.card_outgoing k, h]
  decide

/-- A key in an index column has exactly five same-finger partners. -/
theorem Layout.card_outgoing_index (L : Layout Keycode) (k : UsedKey L)
    (h : k.column.kind = .index) : (L.outgoing k.val).card = 5 := by
  rw [L.card_outgoing k, h]
  decide

theorem Layout.card_outgoing_eq_five_iff (L : Layout Keycode) (k : UsedKey L) :
    (L.outgoing k.val).card = 5 ↔ k.column.kind = .index := by
  rw [L.card_outgoing k]
  generalize k.column.kind = kk
  cases kk <;> decide

/-- An unused keycode has no same-finger partners. -/
theorem Layout.outgoing_eq_empty (L : Layout Keycode) {k : Keycode} (hk : k ∉ L.usedKeys) :
    L.outgoing k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hb
  obtain ⟨c, hkc, _, _⟩ := (isSFB_iff L k b).mp ((L.mem_outgoing k b).mp hb)
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hkc
  exact hk ((L.mem_usedKeys k).mpr ⟨p, hp⟩)

/-! ### Invariants of layout equivalence -/

theorem Layout.Equivalent.usedKeys_eq {L M : Layout Keycode} (h : L.Equivalent M) :
    L.usedKeys = M.usedKeys := by
  have key : ∀ A B : Layout Keycode, A.columns = B.columns → A.usedKeys ⊆ B.usedKeys := by
    intro A B hAB k hk
    rw [← A.columnKeys_cover] at hk
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hk
    have hmem : A.columnKeys c ∈ B.columns := by
      rw [← hAB]
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hmem
    rw [← B.columnKeys_cover]
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, by rw [hd]; exact hc⟩
  exact Finset.Subset.antisymm (key L M h) (key M L (Eq.symm h))

theorem Layout.Equivalent.outgoing_eq {L M : Layout Keycode} (h : L.Equivalent M) (k : Keycode) :
    L.outgoing k = M.outgoing k := by
  unfold Layout.outgoing
  rw [Layout.equivalent_sfb_eq h]

/-- The keycodes operated by an index finger. -/
def Layout.indexKeys (L : Layout Keycode) : Finset Keycode :=
  L.columnKeys .leftIndex ∪ L.columnKeys .rightIndex

theorem Layout.indexKeys_subset (L : Layout Keycode) : L.indexKeys ⊆ L.usedKeys := by
  intro k hk
  rw [← L.columnKeys_cover]
  rcases Finset.mem_union.mp hk with h | h
  · exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h⟩
  · exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, h⟩

theorem Layout.mem_indexKeys_iff_used (L : Layout Keycode) (k : UsedKey L) :
    k.val ∈ L.indexKeys ↔ k.column.kind = .index := by
  rw [Layout.indexKeys, Finset.mem_union, k.mem_columnKeys, k.mem_columnKeys]
  generalize k.column = c
  cases c <;> decide

/-- Index operation is visible in the same-finger bigram data alone. -/
theorem Layout.mem_indexKeys_iff (L : Layout Keycode) (k : Keycode) :
    k ∈ L.indexKeys ↔ k ∈ L.usedKeys ∧ (L.outgoing k).card = 5 := by
  constructor
  · intro hk
    have hused := L.indexKeys_subset hk
    exact ⟨hused, (L.card_outgoing_eq_five_iff ⟨k, hused⟩).mpr
      ((L.mem_indexKeys_iff_used ⟨k, hused⟩).mp hk)⟩
  · rintro ⟨hused, hcard⟩
    exact (L.mem_indexKeys_iff_used ⟨k, hused⟩).mpr
      ((L.card_outgoing_eq_five_iff ⟨k, hused⟩).mp hcard)

theorem Layout.Equivalent.indexKeys_eq {L M : Layout Keycode} (h : L.Equivalent M) :
    L.indexKeys = M.indexKeys := by
  ext k
  rw [L.mem_indexKeys_iff, M.mem_indexKeys_iff, h.usedKeys_eq, h.outgoing_eq]

end

end Fern.Ortholinear
