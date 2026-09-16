module
public import Fern.Ortholinear.Lookup
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.NormNum

/-!
# Rearrangements, column symmetries, and exact counting

`Layout.reindex` moves a layout along a permutation of the grid. The permutations that preserve
the same-finger-column relation form the subgroup `ColumnSymmetry`, and these are exactly the
rearrangements that preserve layout equivalence.
-/

@[expose] public section

namespace Fern.Ortholinear

open Equiv

/-- The finger column operating a grid position. -/
def colOf (p : Position) : ColumnId := columnAt p.2

@[simp] theorem colOf_def (p : Position) : colOf p = columnAt p.2 := rfl

@[simp] theorem perm_apply_inv (σ : Equiv.Perm Position) (x : Position) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

@[simp] theorem perm_inv_apply (σ : Equiv.Perm Position) (x : Position) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

/-! ### Reindexing -/

variable {Keycode : Type}

/-- Move a layout along a permutation of the grid. -/
def Layout.reindex (L : Layout Keycode) (σ : Equiv.Perm Position) : Layout Keycode where
  keyAt p := L.keyAt (σ p)
  unique := L.unique.comp σ.injective

@[simp] theorem Layout.reindex_keyAt (L : Layout Keycode) (σ : Equiv.Perm Position)
    (p : Position) : (L.reindex σ).keyAt p = L.keyAt (σ p) := rfl

@[simp] theorem Layout.reindex_one (L : Layout Keycode) : L.reindex 1 = L := rfl

theorem Layout.reindex_reindex (L : Layout Keycode) (σ τ : Equiv.Perm Position) :
    (L.reindex σ).reindex τ = L.reindex (σ * τ) := rfl

/-- Reindexing is free: a layout determines the permutation that produced it. -/
theorem Layout.reindex_injective (L : Layout Keycode) :
    Function.Injective L.reindex := fun _ _ h =>
  Equiv.ext fun p => L.unique (congrFun (congrArg Layout.keyAt h) p)

theorem Layout.reindex_eq_iff (L : Layout Keycode) (σ τ : Equiv.Perm Position) :
    L.reindex σ = L.reindex τ ↔ σ = τ :=
  ⟨fun h => L.reindex_injective h, fun h => by rw [h]⟩

variable [DecidableEq Keycode]

@[simp] theorem Layout.usedKeys_reindex (L : Layout Keycode) (σ : Equiv.Perm Position) :
    (L.reindex σ).usedKeys = L.usedKeys := by
  ext k
  simp only [Layout.mem_usedKeys, Layout.reindex_keyAt]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨σ p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨σ⁻¹ p, (congrArg L.keyAt (perm_apply_inv σ p)).trans hp⟩

theorem Layout.columnKeys_reindex (L : Layout Keycode) (σ : Equiv.Perm Position)
    (c : ColumnId) (d : ColumnId) (h : ∀ p, colOf (σ p) = d ↔ colOf p = c) :
    (L.reindex σ).columnKeys c = L.columnKeys d := by
  ext k
  simp only [Layout.columnKeys, Finset.mem_image, mem_positions]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨σ p, (h p).mpr hp, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨σ⁻¹ q, (h (σ⁻¹ q)).mp ((congrArg colOf (perm_apply_inv σ q)).trans hq),
      congrArg L.keyAt (perm_apply_inv σ q)⟩

/-! ### Column symmetries -/

/-- Grid permutations that preserve whether two positions share a finger column. -/
def ColumnSymmetry : Subgroup (Equiv.Perm Position) where
  carrier := {σ | ∀ p q, colOf (σ p) = colOf (σ q) ↔ colOf p = colOf q}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {σ τ} hσ hτ := fun p q => by
    show colOf (σ (τ p)) = colOf (σ (τ q)) ↔ _
    rw [hσ, hτ]
  inv_mem' {σ} hσ := fun p q => by
    have h := hσ (σ⁻¹ p) (σ⁻¹ q)
    rw [perm_apply_inv, perm_apply_inv] at h
    exact h.symm

theorem mem_columnSymmetry {σ : Equiv.Perm Position} :
    σ ∈ ColumnSymmetry ↔ ∀ p q, colOf (σ p) = colOf (σ q) ↔ colOf p = colOf q := Iff.rfl

/-- A canonical position in each finger column. -/
def ColumnId.rep (c : ColumnId) : Position := (0, ⟨c.start, by cases c <;> decide⟩)

@[simp] theorem colOf_rep (c : ColumnId) : colOf c.rep = c := by cases c <;> decide

/-- The column map induced by a grid permutation, read off the canonical representatives. -/
def inducedFun (σ : Equiv.Perm Position) (c : ColumnId) : ColumnId := colOf (σ c.rep)

theorem inducedFun_spec {σ : Equiv.Perm Position} (hσ : σ ∈ ColumnSymmetry) (p : Position) :
    colOf (σ p) = inducedFun σ (colOf p) :=
  (hσ p (colOf p).rep).mpr (by rw [colOf_rep])

theorem inducedFun_left_inv {σ : Equiv.Perm Position} (hσ : σ ∈ ColumnSymmetry) (c : ColumnId) :
    inducedFun σ⁻¹ (inducedFun σ c) = c := by
  have h := inducedFun_spec (ColumnSymmetry.inv_mem hσ) (σ c.rep)
  rw [perm_inv_apply, colOf_rep] at h
  exact h.symm

theorem inducedFun_right_inv {σ : Equiv.Perm Position} (hσ : σ ∈ ColumnSymmetry) (c : ColumnId) :
    inducedFun σ (inducedFun σ⁻¹ c) = c := by
  have h := inducedFun_spec hσ (σ⁻¹ c.rep)
  rw [perm_apply_inv, colOf_rep] at h
  exact h.symm

/-- The permutation of finger columns induced by a column symmetry. -/
def inducedPerm (σ : ColumnSymmetry) : Equiv.Perm ColumnId where
  toFun := inducedFun σ.val
  invFun := inducedFun σ.val⁻¹
  left_inv := inducedFun_left_inv σ.property
  right_inv := inducedFun_right_inv σ.property

@[simp] theorem inducedPerm_apply (σ : ColumnSymmetry) (c : ColumnId) :
    inducedPerm σ c = inducedFun σ.val c := rfl

theorem colOf_apply (σ : ColumnSymmetry) (p : Position) :
    colOf (σ.val p) = inducedPerm σ (colOf p) :=
  inducedFun_spec σ.property p

/-- The induced column permutation is the unique one describing a column symmetry. -/
theorem inducedPerm_unique (σ : ColumnSymmetry) (π : Equiv.Perm ColumnId)
    (h : ∀ p, colOf (σ.val p) = π (colOf p)) : π = inducedPerm σ := by
  ext c
  have := (h c.rep).symm.trans (colOf_apply σ c.rep)
  rwa [colOf_rep] at this

theorem mem_columnSymmetry_of_perm {σ : Equiv.Perm Position} (π : Equiv.Perm ColumnId)
    (h : ∀ p, colOf (σ p) = π (colOf p)) : σ ∈ ColumnSymmetry := by
  intro p q
  rw [h p, h q]
  exact ⟨fun hpq => π.injective hpq, fun hpq => by rw [hpq]⟩

/-! ### Fibers and kind preservation -/

/-- The positions operated by one finger column. -/
def Fiber (c : ColumnId) : Type := {p : Position // colOf p = c}

instance (c : ColumnId) : DecidableEq (Fiber c) := Subtype.instDecidableEq
instance (c : ColumnId) : Fintype (Fiber c) := Subtype.fintype _

@[simp] theorem card_fiber (c : ColumnId) : Fintype.card (Fiber c) = 3 * c.kind.width := by
  cases c <;> decide

/-- A column symmetry restricts to a bijection from each column onto its image. -/
def fiberEquiv (σ : ColumnSymmetry) (c : ColumnId) : Fiber c ≃ Fiber (inducedPerm σ c) where
  toFun p := ⟨σ.val p.val, by rw [colOf_apply, p.property]⟩
  invFun q := ⟨σ.val⁻¹ q.val, by
    have := colOf_apply σ (σ.val⁻¹ q.val)
    rw [perm_apply_inv, q.property] at this
    exact (inducedPerm σ).injective this.symm⟩
  left_inv p := Subtype.ext (perm_inv_apply σ.val p.val)
  right_inv q := Subtype.ext (perm_apply_inv σ.val q.val)

theorem ColumnKind.width_injective : Function.Injective ColumnKind.width := by decide

/-- Column symmetries preserve column kind. -/
@[simp] theorem inducedPerm_kind (σ : ColumnSymmetry) (c : ColumnId) :
    (inducedPerm σ c).kind = c.kind := by
  have h : Fintype.card (Fiber c) = Fintype.card (Fiber (inducedPerm σ c)) :=
    Fintype.card_congr (fiberEquiv σ c)
  rw [card_fiber, card_fiber] at h
  exact ColumnKind.width_injective (by omega)

/-! ### Equivalence is exactly reindexing by a column symmetry -/

omit [DecidableEq Keycode] in
theorem Layout.ext {L M : Layout Keycode} (h : ∀ p, L.keyAt p = M.keyAt p) : L = M := by
  obtain ⟨f, _⟩ := L
  obtain ⟨g, _⟩ := M
  have hfg : f = g := funext h
  subst hfg
  rfl

theorem Layout.columnKeys_reindex_eq (L : Layout Keycode) (σ : ColumnSymmetry) (c : ColumnId) :
    (L.reindex σ.val).columnKeys c = L.columnKeys (inducedPerm σ c) := by
  apply L.columnKeys_reindex
  intro p
  rw [colOf_apply σ p]
  exact ⟨fun h => (inducedPerm σ).injective h, fun h => by rw [h]⟩

theorem Layout.columns_reindex (L : Layout Keycode) (σ : ColumnSymmetry) :
    (L.reindex σ.val).columns = L.columns := by
  ext s
  simp only [Layout.columns, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨inducedPerm σ c, (L.columnKeys_reindex_eq σ c).symm⟩
  · rintro ⟨d, rfl⟩
    refine ⟨(inducedPerm σ).symm d, ?_⟩
    rw [L.columnKeys_reindex_eq σ, Equiv.apply_symm_apply]

/-- Reindexing by a column symmetry preserves equivalence. -/
theorem Layout.equivalent_reindex (L : Layout Keycode) (σ : ColumnSymmetry) :
    L.Equivalent (L.reindex σ.val) :=
  (L.columns_reindex σ).symm

/-- The grid permutation carrying `L` onto a layout with the same repertoire. -/
def transferPerm (L M : Layout Keycode) (h : M.usedKeys = L.usedKeys) : Equiv.Perm Position :=
  M.posEquiv.trans
    ((Equiv.subtypeEquivRight fun k => by rw [h] : UsedKey M ≃ UsedKey L).trans L.posEquiv.symm)

@[simp] theorem keyAt_transferPerm (L M : Layout Keycode) (h : M.usedKeys = L.usedKeys)
    (p : Position) : L.keyAt (transferPerm L M h p) = M.keyAt p :=
  UsedKey.keyAt_position (L := L) _

theorem reindex_transferPerm (L M : Layout Keycode) (h : M.usedKeys = L.usedKeys) :
    L.reindex (transferPerm L M h) = M :=
  Layout.ext fun p => keyAt_transferPerm L M h p

section
attribute [local irreducible] Layout.sfbs

/-- Two positions share a finger column exactly when they are equal or hold a same-finger
bigram. -/
theorem colOf_eq_iff (L : Layout Keycode) (p q : Position) :
    colOf p = colOf q ↔ p = q ∨ IsSFB L (L.keyAt p, L.keyAt q) := by
  have h := sameColumn_iff L (L.atPosition p) (L.atPosition q)
  have h1 : SameColumn L (L.atPosition p) (L.atPosition q) ↔ colOf p = colOf q := by
    unfold SameColumn
    rw [UsedKey.column_atPosition, UsedKey.column_atPosition, colOf_def, colOf_def]
  rw [h1, L.atPosition_inj_iff] at h
  exact h

theorem transferPerm_mem_columnSymmetry (L M : Layout Keycode) (hEq : L.Equivalent M) :
    transferPerm L M hEq.usedKeys_eq.symm ∈ ColumnSymmetry := by
  intro p q
  rw [colOf_eq_iff L, colOf_eq_iff M, keyAt_transferPerm, keyAt_transferPerm,
    isSFB_congr (Layout.equivalent_sfb_eq hEq)]
  constructor
  · rintro (h | h)
    · exact Or.inl ((transferPerm L M hEq.usedKeys_eq.symm).injective h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

/-- Two layouts are equivalent exactly when one is a reindexing of the other by a column
symmetry. -/
theorem Layout.equivalent_iff_exists_reindex (L M : Layout Keycode) :
    L.Equivalent M ↔ ∃ σ : ColumnSymmetry, M = L.reindex σ.val := by
  constructor
  · intro hEq
    exact ⟨⟨transferPerm L M hEq.usedKeys_eq.symm, transferPerm_mem_columnSymmetry L M hEq⟩,
      (reindex_transferPerm L M hEq.usedKeys_eq.symm).symm⟩
  · rintro ⟨σ, rfl⟩
    exact L.equivalent_reindex σ

end

/-! ### Building column symmetries from column data -/

section
variable (π : Equiv.Perm ColumnId) (F : ∀ c, Fiber c ≃ Fiber (π c))

/-- Assemble a grid map from a column permutation and a bijection inside each column. -/
def columnDataFun (p : Position) : Position := (F (colOf p) ⟨p, rfl⟩).val

theorem columnDataFun_eq {c : ColumnId} (p : Fiber c) : columnDataFun π F p.val = (F c p).val := by
  obtain ⟨p, rfl⟩ := p
  rfl

theorem colOf_columnDataFun (p : Position) : colOf (columnDataFun π F p) = π (colOf p) :=
  (F (colOf p) ⟨p, rfl⟩).property

theorem columnDataFun_injective : Function.Injective (columnDataFun π F) := by
  intro p q h
  have hcol : colOf p = colOf q :=
    π.injective (by rw [← colOf_columnDataFun π F p, ← colOf_columnDataFun π F q, h])
  have hval : (F (colOf q) ⟨p, hcol⟩).val = (F (colOf q) ⟨q, rfl⟩).val := by
    rw [← columnDataFun_eq π F ⟨p, hcol⟩, ← columnDataFun_eq π F ⟨q, rfl⟩]
    exact h
  exact congrArg Subtype.val ((F (colOf q)).injective (Subtype.ext hval))

/-- The grid permutation assembled from column data. -/
noncomputable def ofColumnData : Equiv.Perm Position :=
  Equiv.ofBijective (columnDataFun π F)
    (Finite.injective_iff_bijective.mp (columnDataFun_injective π F))

@[simp] theorem ofColumnData_apply (p : Position) :
    ofColumnData π F p = columnDataFun π F p := rfl

theorem ofColumnData_mem : ofColumnData π F ∈ ColumnSymmetry :=
  mem_columnSymmetry_of_perm π fun p => colOf_columnDataFun π F p

/-- Any column permutation together with bijections inside each column is a column symmetry. -/
noncomputable def ColumnSymmetry.ofData : ColumnSymmetry := ⟨ofColumnData π F, ofColumnData_mem π F⟩

@[simp] theorem inducedPerm_ofData : inducedPerm (ColumnSymmetry.ofData π F) = π :=
  (inducedPerm_unique _ π fun p => colOf_columnDataFun π F p).symm

end

/-! ### Kind-preserving column permutations -/

/-- Permutations of the eight finger columns that preserve column kind. -/
def KindPerm : Type := {π : Equiv.Perm ColumnId // ∀ c, (π c).kind = c.kind}

instance : DecidableEq KindPerm := Subtype.instDecidableEq
-- These enumerations exist only to state cardinalities; they are never run, and compiling
-- them would make module initialisation try to build a list of 34 828 517 376 000 elements.
noncomputable instance : Fintype KindPerm := Subtype.fintype _

theorem ColumnKind.eq_iff_index (x y : ColumnKind) : x = y ↔ (x = .index ↔ y = .index) := by
  cases x <;> cases y <;> decide

/-- Permutations preserving a decidable predicate split into independent permutations of the
two parts. -/
def permPreservingEquiv {α : Type*} (p : α → Prop) [DecidablePred p] :
    {σ : Equiv.Perm α // ∀ a, p (σ a) ↔ p a} ≃
      Equiv.Perm {a // p a} × Equiv.Perm {a // ¬p a} where
  toFun σ := (σ.val.subtypePerm σ.property, σ.val.subtypePerm fun a => not_congr (σ.property a))
  invFun fg := ⟨Equiv.Perm.subtypeCongr fg.1 fg.2, fun a => by
    by_cases h : p a
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ h]
      exact iff_of_true (fg.1 ⟨a, h⟩).property h
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ h]
      exact iff_of_false (fg.2 ⟨a, h⟩).property h⟩
  left_inv σ := by
    refine Subtype.ext (Equiv.ext fun a => ?_)
    by_cases h : p a
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ h]
      rfl
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ h]
      rfl
  right_inv fg := by
    refine Prod.ext (Equiv.ext fun a => Subtype.ext ?_) (Equiv.ext fun a => Subtype.ext ?_)
    · exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ a
    · exact Equiv.Perm.subtypeCongr.right_apply_subtype _ _ a

/-- Kind preservation is the same as preserving membership of the index columns. -/
def kindPermEquiv :
    KindPerm ≃ {σ : Equiv.Perm ColumnId // ∀ c, ((σ c).kind = .index ↔ c.kind = .index)} :=
  Equiv.subtypeEquivRight fun _ => forall_congr' fun _ => ColumnKind.eq_iff_index _ _

theorem card_index_columns : Fintype.card {c : ColumnId // c.kind = ColumnKind.index} = 2 := by
  decide

theorem card_simple_columns : Fintype.card {c : ColumnId // ¬(c.kind = ColumnKind.index)} = 6 := by
  decide

/-- Six simple columns and two index columns can be permuted independently. -/
theorem card_kindPerm : Fintype.card KindPerm = 1440 := by
  rw [Fintype.card_congr
      (kindPermEquiv.trans (permPreservingEquiv fun c : ColumnId => c.kind = ColumnKind.index)),
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, card_index_columns,
    card_simple_columns]
  decide

/-! ### The order of the column symmetry group -/

instance : DecidablePred (· ∈ ColumnSymmetry) := fun σ =>
  inferInstanceAs (Decidable (∀ p q, colOf (σ p) = colOf (σ q) ↔ colOf p = colOf q))

/-- A kind-preserving column permutation together with a bijection inside each column. -/
def ColumnData : Type := Σ π : KindPerm, ∀ c : ColumnId, Fiber c ≃ Fiber (π.val c)

noncomputable instance : Fintype ColumnData := inferInstanceAs (Fintype (Σ _ : KindPerm, _))

/-- Column data assembles into a column symmetry. -/
noncomputable def toSymmetry (d : ColumnData) : ColumnSymmetry :=
  ColumnSymmetry.ofData d.1.val d.2

theorem toSymmetry_injective : Function.Injective toSymmetry := by
  rintro ⟨π, F⟩ ⟨π', F'⟩ h
  have hval : ofColumnData π.val F = ofColumnData π'.val F' := congrArg Subtype.val h
  have hπ : π = π' := by
    refine Subtype.ext ?_
    rw [← inducedPerm_ofData π.val F, ← inducedPerm_ofData π'.val F']
    exact congrArg inducedPerm h
  subst hπ
  have hF : ∀ (c : ColumnId) (p : Fiber c), (F c p).val = (F' c p).val := by
    intro c p
    rw [← columnDataFun_eq π.val F p, ← columnDataFun_eq π.val F' p]
    exact congrArg (fun e : Equiv.Perm Position => e p.val) hval
  have hFF : F = F' := funext fun c => Equiv.ext fun p => Subtype.ext (hF c p)
  rw [hFF]

theorem toSymmetry_surjective : Function.Surjective toSymmetry := by
  intro σ
  refine ⟨⟨⟨inducedPerm σ, inducedPerm_kind σ⟩, fiberEquiv σ⟩, ?_⟩
  exact Subtype.ext (Equiv.ext fun _ => rfl)

theorem toSymmetry_bijective : Function.Bijective toSymmetry :=
  ⟨toSymmetry_injective, toSymmetry_surjective⟩

/-- Within a column, a column symmetry induces an arbitrary bijection onto the image column. -/
theorem card_fiber_equiv (π : KindPerm) (c : ColumnId) :
    Fintype.card (Fiber c ≃ Fiber (π.val c)) = Nat.factorial (3 * c.kind.width) := by
  have hcard : Fintype.card (Fiber c) = Fintype.card (Fiber (π.val c)) := by
    rw [card_fiber, card_fiber, π.property c]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), card_fiber]

theorem prod_fiber_factorial :
    ∏ c : ColumnId, Nat.factorial (3 * c.kind.width) = 24186470400 := by decide

theorem card_columnData : Fintype.card ColumnData = 34828517376000 := by
  have h1 : Fintype.card ColumnData
      = ∑ π : KindPerm, Fintype.card (∀ c : ColumnId, Fiber c ≃ Fiber (π.val c)) :=
    Fintype.card_sigma
  have h2 : ∀ π : KindPerm,
      Fintype.card (∀ c : ColumnId, Fiber c ≃ Fiber (π.val c)) = 24186470400 := fun π => by
    rw [Fintype.card_pi, Finset.prod_congr rfl fun c _ => card_fiber_equiv π c,
      prod_fiber_factorial]
  rw [h1, Finset.sum_congr rfl fun π _ => h2 π, Finset.sum_const, Finset.card_univ,
    card_kindPerm, smul_eq_mul]

/-- The column symmetry group has order `(3!)^6 (6!)^2 6! 2!`. -/
theorem card_columnSymmetry : Fintype.card ColumnSymmetry = 34828517376000 := by
  rw [← Fintype.card_of_bijective toSymmetry_bijective, card_columnData]

/-! ### Layouts over a fixed repertoire -/

variable (R : Repertoire Keycode)

/-- Used keycodes of a layout on `R` are exactly the repertoire. -/
def usedKeyEquivRepertoire (L : LayoutOn R) : UsedKey L.val ≃ {k // k ∈ R.keys} :=
  Equiv.subtypeEquivRight fun _ => by rw [L.property]

/-- A layout on `R` is the same thing as a bijection from the grid onto the repertoire. -/
def layoutOnEquiv : LayoutOn R ≃ (Position ≃ {k // k ∈ R.keys}) where
  toFun L := L.val.posEquiv.trans (usedKeyEquivRepertoire R L)
  invFun e := ⟨⟨fun p => (e p).val, fun _ _ h => e.injective (Subtype.ext h)⟩, by
    ext k
    simp only [Layout.mem_usedKeys]
    constructor
    · rintro ⟨p, rfl⟩
      exact (e p).property
    · intro hk
      exact ⟨e.symm ⟨k, hk⟩, congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)⟩⟩
  left_inv L := Subtype.ext (Layout.ext fun _ => rfl)
  right_inv e := Equiv.ext fun _ => Subtype.ext rfl

noncomputable instance : Fintype (LayoutOn R) := Fintype.ofEquiv _ (layoutOnEquiv R).symm

instance : DecidableEq (LayoutOn R) := fun L M =>
  decidable_of_iff (L.val.keyAt = M.val.keyAt)
    ⟨fun h => Subtype.ext (Layout.ext (congrFun h)), fun h => by rw [h]⟩

omit [DecidableEq Keycode] in
theorem card_repertoire : Fintype.card {k // k ∈ R.keys} = 30 := by
  rw [Fintype.card_coe, R.card_eq]

/-- Every repertoire carries exactly `30!` concrete layouts. -/
theorem card_layoutOn : Fintype.card (LayoutOn R) = Nat.factorial 30 := by
  have hpos : Fintype.card Position = 30 := by decide
  have e : Position ≃ {k // k ∈ R.keys} :=
    Fintype.equivOfCardEq (by rw [hpos, card_repertoire])
  rw [Fintype.card_congr (layoutOnEquiv R), Fintype.card_equiv e, hpos]

/-! ### The group action and the equivalence classes -/

instance : SMul ColumnSymmetry (LayoutOn R) :=
  ⟨fun σ L => ⟨L.val.reindex σ.val⁻¹, by rw [Layout.usedKeys_reindex, L.property]⟩⟩

theorem smul_layoutOn_val (σ : ColumnSymmetry) (L : LayoutOn R) :
    (σ • L).val = L.val.reindex σ.val⁻¹ := rfl

instance : MulAction ColumnSymmetry (LayoutOn R) where
  one_smul L := Subtype.ext (by
    show L.val.reindex (1 : ColumnSymmetry).val⁻¹ = L.val
    rw [OneMemClass.coe_one, inv_one, Layout.reindex_one])
  mul_smul σ τ L := Subtype.ext (by
    show L.val.reindex ((σ * τ).val)⁻¹ = (L.val.reindex τ.val⁻¹).reindex σ.val⁻¹
    rw [Layout.reindex_reindex, Subgroup.coe_mul, mul_inv_rev])

/-- The action of the column symmetry group on layouts is free. -/
theorem smul_eq_self_iff (σ : ColumnSymmetry) (L : LayoutOn R) : σ • L = L ↔ σ = 1 := by
  constructor
  · intro h
    have h1 : L.val.reindex σ.val⁻¹ = L.val.reindex 1 := by
      rw [Layout.reindex_one]
      exact congrArg Subtype.val h
    have h2 := L.val.reindex_injective h1
    exact Subtype.ext (by rw [← inv_inv σ.val, h2, inv_one, OneMemClass.coe_one])
  · rintro rfl
    exact one_smul _ L

/-- The orbits of the action are exactly the equivalence classes. -/
theorem mem_orbit_iff (L M : LayoutOn R) :
    M ∈ MulAction.orbit ColumnSymmetry L ↔ L.val.Equivalent M.val := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact L.val.equivalent_reindex ⟨σ.val⁻¹, ColumnSymmetry.inv_mem σ.property⟩
  · intro h
    obtain ⟨σ, hσ⟩ := (L.val.equivalent_iff_exists_reindex M.val).mp h
    refine ⟨σ⁻¹, Subtype.ext ?_⟩
    rw [smul_layoutOn_val, InvMemClass.coe_inv, inv_inv]
    exact hσ.symm

/-- Layout equivalence, as a setoid on the layouts over one repertoire. -/
def layoutSetoid : Setoid (LayoutOn R) where
  r L M := L.val.Equivalent M.val
  iseqv := ⟨fun L => Layout.equivalent_refl L.val, fun h => Layout.equivalent_symm h,
    fun h h' => Layout.equivalent_trans h h'⟩

instance : DecidableRel (layoutSetoid R).r := fun L M =>
  inferInstanceAs (Decidable (L.val.columns = M.val.columns))

/-- Equivalence classes of layouts over a fixed repertoire. -/
def LayoutClass : Type := Quotient (layoutSetoid R)

noncomputable instance : Fintype (LayoutClass R) := Quotient.fintype (layoutSetoid R)

instance (L : LayoutOn R) : DecidablePred fun M : LayoutOn R => L.val.Equivalent M.val :=
  fun M => inferInstanceAs (Decidable (L.val.columns = M.val.columns))

/-- Every equivalence class is a free orbit, hence has exactly `D` members. -/
noncomputable def classEquiv (L : LayoutOn R) :
    ColumnSymmetry ≃ {M : LayoutOn R // L.val.Equivalent M.val} :=
  Equiv.ofBijective
    (fun σ => ⟨⟨L.val.reindex σ.val, by rw [Layout.usedKeys_reindex, L.property]⟩,
      L.val.equivalent_reindex σ⟩)
    ⟨fun _ _ h =>
      Subtype.ext (L.val.reindex_injective (congrArg Subtype.val (congrArg Subtype.val h))),
     fun M => by
       obtain ⟨σ, hσ⟩ := (L.val.equivalent_iff_exists_reindex M.val.val).mp M.property
       exact ⟨σ, Subtype.ext (Subtype.ext hσ.symm)⟩⟩

theorem card_class (L : LayoutOn R) :
    Fintype.card {M : LayoutOn R // L.val.Equivalent M.val} = 34828517376000 := by
  rw [← Fintype.card_congr (classEquiv R L), card_columnSymmetry]

theorem card_class_fiber (q : LayoutClass R) :
    Fintype.card {L : LayoutOn R // Quotient.mk (layoutSetoid R) L = q} = 34828517376000 := by
  induction q using Quotient.inductionOn with
  | _ L =>
    rw [Fintype.card_congr (Equiv.subtypeEquivRight fun M =>
      (Quotient.eq (r := layoutSetoid R)).trans
        ⟨fun h => Layout.equivalent_symm h, fun h => Layout.equivalent_symm h⟩)]
    exact card_class R L

/-- The layouts over a repertoire split into equal-sized equivalence classes. -/
theorem card_layoutOn_eq_mul :
    Fintype.card (LayoutOn R) = Fintype.card (LayoutClass R) * 34828517376000 := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (layoutSetoid R))),
    Fintype.card_sigma]
  simp only [card_class_fiber]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

theorem factorial_thirty : Nat.factorial 30 = 7615967597718480000 * 34828517376000 := by decide

theorem columnSymmetry_card_dvd_factorial : (34828517376000 : ℕ) ∣ Nat.factorial 30 :=
  ⟨7615967597718480000, by rw [factorial_thirty, Nat.mul_comm]⟩

/-- There are `30! / D` equivalence classes of layouts over any repertoire. -/
theorem card_layoutClass : Fintype.card (LayoutClass R) = 7615967597718480000 := by
  have h := card_layoutOn_eq_mul R
  rw [card_layoutOn R, factorial_thirty] at h
  have hpos : (0 : ℕ) < 34828517376000 := by decide
  exact (Nat.eq_of_mul_eq_mul_right hpos h).symm

end Fern.Ortholinear
