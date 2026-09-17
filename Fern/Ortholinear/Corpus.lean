module
public import Fern.Ngram
public import Fern.Ortholinear.Classify
public import Fern.Ortholinear.Swap

/-!
# Measuring a layout against a corpus

A corpus is a contiguous stream of keycodes, independent of any layout, so two layouts can be
compared on the same text. Its bigrams come from `Fern.Ngram.bigrams`.

Every count proved elsewhere in `Fern.Ortholinear` is structural and identical for all layouts.
Corpus counts are not, and they see exactly layout equivalence: two layouts are equivalent iff
they give the same same-finger bigram count on every corpus, and two-keystroke corpora already
suffice.

Counts are defined twice, once over an explicit list of bigrams (`…In`) and once over a corpus.
The list form is where the inductions run, and it lets other windows such as skipgrams reuse the
same theorems.
-/

@[expose] public section

namespace Fern.Ortholinear

/-- A contiguous stream of keystrokes. -/
abbrev Corpus (Keycode : Type) := List Keycode

variable {Keycode : Type} [DecidableEq Keycode]

section
attribute [local irreducible] Layout.sfbs

/-! ### Same-finger bigram counts -/

/-- Same-finger bigrams among an explicit list of bigrams. -/
def Layout.sfbCountIn (L : Layout Keycode) (bs : List (Bigram Keycode)) : Nat :=
  bs.countP fun b => decide (IsSFB L b)

/-- Same-finger bigrams in a corpus. -/
def Layout.sfbCount (L : Layout Keycode) (c : Corpus Keycode) : Nat :=
  L.sfbCountIn (Ngram.bigrams c)

theorem Layout.sfbCountIn_congr {L M : Layout Keycode} (h : L.sfbs = M.sfbs)
    (bs : List (Bigram Keycode)) : L.sfbCountIn bs = M.sfbCountIn bs :=
  List.countP_congr fun b _ => by
    simp only [decide_eq_true_eq]
    exact isSFB_congr h b

theorem Layout.sfbCount_pair (L : Layout Keycode) (a b : Keycode) :
    L.sfbCount [a, b] = if IsSFB L (a, b) then 1 else 0 := by
  simp [Layout.sfbCount, Layout.sfbCountIn]

theorem Layout.sfbCount_pair_eq_one_iff (L : Layout Keycode) (a b : Keycode) :
    L.sfbCount [a, b] = 1 ↔ IsSFB L (a, b) := by
  rw [L.sfbCount_pair]
  split <;> simp_all

/-- A corpus of `n` keystrokes has at most `n - 1` same-finger bigrams. -/
theorem Layout.sfbCount_le (L : Layout Keycode) (c : Corpus Keycode) :
    L.sfbCount c ≤ c.length - 1 := by
  rw [← Ngram.length_bigrams]
  exact List.countP_le_length

/-! ### Corpus counts see exactly layout equivalence -/

theorem Layout.Equivalent.sfbCount_eq {L M : Layout Keycode} (h : L.Equivalent M)
    (c : Corpus Keycode) : L.sfbCount c = M.sfbCount c :=
  Layout.sfbCountIn_congr (Layout.equivalent_sfb_eq h) _

/-- Two-keystroke corpora determine the same-finger bigram set. -/
theorem Layout.sfbs_eq_of_sfbCount_pairs {L M : Layout Keycode}
    (h : ∀ a b, L.sfbCount [a, b] = M.sfbCount [a, b]) : L.sfbs = M.sfbs := by
  ext ⟨a, b⟩
  show IsSFB L (a, b) ↔ IsSFB M (a, b)
  rw [← L.sfbCount_pair_eq_one_iff, ← M.sfbCount_pair_eq_one_iff, h]

/-- Two-keystroke corpora already pin a layout down up to equivalence. -/
theorem Layout.equivalent_of_sfbCount_pairs {L M : Layout Keycode}
    (h : ∀ a b, L.sfbCount [a, b] = M.sfbCount [a, b]) : L.Equivalent M :=
  (L.equivalent_iff_sfbs_eq M).mpr (Layout.sfbs_eq_of_sfbCount_pairs h)

/-- Layouts are equivalent exactly when they agree on the same-finger bigram count of every
corpus. -/
theorem Layout.equivalent_iff_sfbCount_eq (L M : Layout Keycode) :
    L.Equivalent M ↔ ∀ c : Corpus Keycode, L.sfbCount c = M.sfbCount c :=
  ⟨fun h c => h.sfbCount_eq c, fun h => Layout.equivalent_of_sfbCount_pairs fun a b => h [a, b]⟩

/-! ### Classifying raw bigrams -/

/-- Classification of a raw ordered bigram, or `none` when the layout does not use a keycode. -/
def Layout.classify? (L : Layout Keycode) (a b : Keycode) : Option BigramKind :=
  match L.positionOf a, L.positionOf b with
  | some p, some q => some (positionKind p q)
  | _, _ => none

theorem Layout.classify?_usedKey (L : Layout Keycode) (a b : UsedKey L) :
    L.classify? a.val b.val = some (L.classify a b) := by
  have ha : L.positionOf a.val = some a.position :=
    (L.positionOf_eq_some _ _).mpr a.keyAt_position
  have hb : L.positionOf b.val = some b.position :=
    (L.positionOf_eq_some _ _).mpr b.keyAt_position
  simp only [Layout.classify?, ha, hb, L.classify_eq_positionKind]

theorem Layout.classify?_of_not_mem_left (L : Layout Keycode) {a : Keycode} (b : Keycode)
    (h : a ∉ L.usedKeys) : L.classify? a b = none := by
  simp [Layout.classify?, (L.positionOf_eq_none a).mpr h]

theorem Layout.classify?_of_not_mem_right (L : Layout Keycode) (a : Keycode) {b : Keycode}
    (h : b ∉ L.usedKeys) : L.classify? a b = none := by
  unfold Layout.classify?
  rw [(L.positionOf_eq_none b).mpr h]
  cases L.positionOf a <;> rfl

theorem Layout.mem_usedKeys_of_isSFB (L : Layout Keycode) {a b : Keycode} (h : IsSFB L (a, b)) :
    a ∈ L.usedKeys ∧ b ∈ L.usedKeys := by
  obtain ⟨c, ha, hb, -⟩ := (isSFB_iff L a b).mp h
  rw [← L.columnKeys_cover]
  exact ⟨Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ha⟩,
    Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hb⟩⟩

/-- On raw keycodes, the same-finger category is exactly `IsSFB`, with no side condition. -/
theorem Layout.classify?_eq_sameFinger_iff (L : Layout Keycode) (a b : Keycode) :
    L.classify? a b = some .sameFinger ↔ IsSFB L (a, b) := by
  by_cases ha : a ∈ L.usedKeys
  · by_cases hb : b ∈ L.usedKeys
    · rw [show L.classify? a b = some (L.classify ⟨a, ha⟩ ⟨b, hb⟩) from
        L.classify?_usedKey ⟨a, ha⟩ ⟨b, hb⟩, Option.some.injEq]
      exact L.classify_eq_sameFinger _ _
    · rw [L.classify?_of_not_mem_right a hb]
      exact ⟨(fun h => nomatch h), fun h => absurd (L.mem_usedKeys_of_isSFB h).2 hb⟩
  · rw [L.classify?_of_not_mem_left b ha]
    exact ⟨(fun h => nomatch h), fun h => absurd (L.mem_usedKeys_of_isSFB h).1 ha⟩

/-! ### The four-way split of a corpus

`kindCount` counts occurrences in a corpus. It is unrelated to `BigramKind.count`, which gives
the fixed number of ordered key pairs in each category (30, 96, 324 and 450). -/

/-- Bigrams of one kind among an explicit list of bigrams. -/
def Layout.kindCountIn (L : Layout Keycode) (k : BigramKind) (bs : List (Bigram Keycode)) :
    Nat :=
  bs.countP fun b => decide (L.classify? b.1 b.2 = some k)

/-- Bigrams of one kind in a corpus. -/
def Layout.kindCount (L : Layout Keycode) (k : BigramKind) (c : Corpus Keycode) : Nat :=
  L.kindCountIn k (Ngram.bigrams c)

/-- Bigrams using a keycode the layout lacks, among an explicit list of bigrams. -/
def Layout.unmappedCountIn (L : Layout Keycode) (bs : List (Bigram Keycode)) : Nat :=
  bs.countP fun b => (L.classify? b.1 b.2).isNone

/-- Bigrams using a keycode the layout lacks, in a corpus. -/
def Layout.unmappedCount (L : Layout Keycode) (c : Corpus Keycode) : Nat :=
  L.unmappedCountIn (Ngram.bigrams c)

private theorem countP_option_partition {α : Type} (f : α → Option BigramKind) (l : List α) :
    l.countP (fun x => decide (f x = some .repeated))
      + l.countP (fun x => decide (f x = some .sameFinger))
      + l.countP (fun x => decide (f x = some .sameHandDifferentFinger))
      + l.countP (fun x => decide (f x = some .oppositeHands))
      + l.countP (fun x => (f x).isNone) = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.countP_cons, List.length_cons]
    rcases f x with _ | k
    · simp
      omega
    · cases k <;> simp <;> omega

/-- Every bigram falls into exactly one kind or uses a keycode the layout lacks. -/
theorem Layout.kindCountIn_add_unmappedCountIn (L : Layout Keycode) (bs : List (Bigram Keycode)) :
    L.kindCountIn .repeated bs + L.kindCountIn .sameFinger bs
      + L.kindCountIn .sameHandDifferentFinger bs + L.kindCountIn .oppositeHands bs
      + L.unmappedCountIn bs = bs.length :=
  countP_option_partition (α := Bigram Keycode) (fun b => L.classify? b.1 b.2) bs

theorem Layout.kindCount_add_unmappedCount (L : Layout Keycode) (c : Corpus Keycode) :
    L.kindCount .repeated c + L.kindCount .sameFinger c
      + L.kindCount .sameHandDifferentFinger c + L.kindCount .oppositeHands c
      + L.unmappedCount c = c.length - 1 := by
  rw [← Ngram.length_bigrams]
  exact L.kindCountIn_add_unmappedCountIn _

/-- A layout supports a corpus when it uses every keycode that occurs in it. -/
def Layout.Supports (L : Layout Keycode) (c : Corpus Keycode) : Prop := ∀ k ∈ c, k ∈ L.usedKeys

instance (L : Layout Keycode) (c : Corpus Keycode) : Decidable (L.Supports c) :=
  inferInstanceAs (Decidable (∀ k ∈ c, k ∈ L.usedKeys))

theorem Layout.unmappedCount_eq_zero (L : Layout Keycode) {c : Corpus Keycode}
    (h : L.Supports c) : L.unmappedCount c = 0 := by
  unfold Layout.unmappedCount Layout.unmappedCountIn
  rw [List.countP_eq_zero]
  intro b hb
  obtain ⟨h1, h2⟩ := Ngram.mem_bigrams hb
  rw [show L.classify? b.1 b.2 = some (L.classify ⟨b.1, h b.1 h1⟩ ⟨b.2, h b.2 h2⟩) from
    L.classify?_usedKey ⟨b.1, h b.1 h1⟩ ⟨b.2, h b.2 h2⟩]
  simp

/-- On a supported corpus the four kinds account for every bigram. -/
theorem Layout.kindCount_sum_of_supports (L : Layout Keycode) {c : Corpus Keycode}
    (h : L.Supports c) :
    L.kindCount .repeated c + L.kindCount .sameFinger c
      + L.kindCount .sameHandDifferentFinger c + L.kindCount .oppositeHands c
      = c.length - 1 := by
  have := L.kindCount_add_unmappedCount c
  rw [L.unmappedCount_eq_zero h] at this
  omega

/-- The same-finger kind count is the same-finger bigram count. -/
theorem Layout.kindCount_sameFinger (L : Layout Keycode) (c : Corpus Keycode) :
    L.kindCount .sameFinger c = L.sfbCount c :=
  List.countP_congr fun b _ => by
    simp only [decide_eq_true_eq]
    exact L.classify?_eq_sameFinger_iff b.1 b.2

theorem Layout.Equivalent.kindCount_sameFinger_eq {L M : Layout Keycode} (h : L.Equivalent M)
    (c : Corpus Keycode) : L.kindCount .sameFinger c = M.kindCount .sameFinger c := by
  rw [L.kindCount_sameFinger, M.kindCount_sameFinger, h.sfbCount_eq]

/-! ### How far one swap can move the count -/

/-- A bigram involving either of two keycodes. The disjuncts are ordered to match
`Layout.mem_sfbsChanged_touches`. -/
def Touches (x y : Keycode) (b : Bigram Keycode) : Prop :=
  b.1 = x ∨ b.2 = x ∨ b.1 = y ∨ b.2 = y

instance (x y : Keycode) (b : Bigram Keycode) : Decidable (Touches x y b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- Bigrams involving either of two keycodes, among an explicit list of bigrams. -/
def touchCountIn (x y : Keycode) (bs : List (Bigram Keycode)) : Nat :=
  bs.countP fun b => decide (Touches x y b)

/-- Bigrams involving either of two keycodes, in a corpus. -/
def touchCount (x y : Keycode) (c : Corpus Keycode) : Nat :=
  touchCountIn x y (Ngram.bigrams c)

theorem touchCount_comm (x y : Keycode) (c : Corpus Keycode) :
    touchCount x y c = touchCount y x c :=
  List.countP_congr fun b _ => by
    simp only [decide_eq_true_eq, Touches]
    tauto

theorem touchCount_eq_zero {x y : Keycode} {c : Corpus Keycode} (hx : x ∉ c) (hy : y ∉ c) :
    touchCount x y c = 0 := by
  unfold touchCount touchCountIn
  rw [List.countP_eq_zero]
  intro b hb
  obtain ⟨h1, h2⟩ := Ngram.mem_bigrams hb
  simp only [decide_eq_true_eq, Touches, not_or]
  exact ⟨fun h => hx (h ▸ h1), fun h => hx (h ▸ h2), fun h => hy (h ▸ h1), fun h => hy (h ▸ h2)⟩

private theorem countP_le_add_of_imp {α : Type} (l : List α) {p q r : α → Bool}
    (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have ht := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x (by simp)
    simp only [List.countP_cons]
    by_cases hp : p x <;> by_cases hq : q x <;> by_cases hr : r x <;> simp_all <;> omega

theorem Layout.touches_of_isSFB_of_not_isSFB_swap (L : Layout Keycode) (p q : Position)
    {b : Bigram Keycode} (h : IsSFB L b) (h' : ¬IsSFB (L.swapPositions p q) b) :
    Touches (L.keyAt p) (L.keyAt q) b :=
  L.mem_sfbsChanged_touches (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, h'⟩))

theorem touchCountIn_comm (x y : Keycode) (bs : List (Bigram Keycode)) :
    touchCountIn x y bs = touchCountIn y x bs :=
  List.countP_congr fun b _ => by
    simp only [decide_eq_true_eq, Touches]
    tauto

/-- A swap can remove at most as many same-finger bigrams from a list as it has bigrams involving
the two swapped keycodes. -/
theorem Layout.sfbCountIn_le_swap_add_touchCountIn (L : Layout Keycode) (p q : Position)
    (bs : List (Bigram Keycode)) :
    L.sfbCountIn bs ≤ (L.swapPositions p q).sfbCountIn bs + touchCountIn (L.keyAt p) (L.keyAt q) bs :=
  countP_le_add_of_imp _ fun b _ hb => by
    simp only [decide_eq_true_eq] at hb ⊢
    by_cases hM : IsSFB (L.swapPositions p q) b
    · exact Or.inl hM
    · exact Or.inr (L.touches_of_isSFB_of_not_isSFB_swap p q hb hM)

/-- …and add at most as many. -/
theorem Layout.swap_sfbCountIn_le_add_touchCountIn (L : Layout Keycode) (p q : Position)
    (bs : List (Bigram Keycode)) :
    (L.swapPositions p q).sfbCountIn bs ≤ L.sfbCountIn bs + touchCountIn (L.keyAt p) (L.keyAt q) bs := by
  have h := (L.swapPositions p q).sfbCountIn_le_swap_add_touchCountIn p q bs
  rw [Layout.swapPositions_swapPositions, Layout.swapPositions_keyAt,
    Layout.swapPositions_keyAt, Equiv.swap_apply_left, Equiv.swap_apply_right,
    touchCountIn_comm] at h
  exact h

theorem Layout.abs_sfbCountIn_sub_swap_le (L : Layout Keycode) (p q : Position)
    (bs : List (Bigram Keycode)) :
    |(L.sfbCountIn bs : ℤ) - ((L.swapPositions p q).sfbCountIn bs : ℤ)|
      ≤ (touchCountIn (L.keyAt p) (L.keyAt q) bs : ℤ) := by
  have h1 := L.sfbCountIn_le_swap_add_touchCountIn p q bs
  have h2 := L.swap_sfbCountIn_le_add_touchCountIn p q bs
  rw [abs_sub_le_iff]
  exact ⟨by omega, by omega⟩

/-- A swap can remove at most as many same-finger bigrams as the corpus has bigrams involving
the two swapped keycodes. -/
theorem Layout.sfbCount_le_swap_add_touchCount (L : Layout Keycode) (p q : Position)
    (c : Corpus Keycode) :
    L.sfbCount c ≤ (L.swapPositions p q).sfbCount c + touchCount (L.keyAt p) (L.keyAt q) c :=
  L.sfbCountIn_le_swap_add_touchCountIn p q _

/-- …and add at most as many. -/
theorem Layout.swap_sfbCount_le_add_touchCount (L : Layout Keycode) (p q : Position)
    (c : Corpus Keycode) :
    (L.swapPositions p q).sfbCount c ≤ L.sfbCount c + touchCount (L.keyAt p) (L.keyAt q) c :=
  L.swap_sfbCountIn_le_add_touchCountIn p q _

/-- One swap moves the same-finger bigram count of a corpus by at most the number of bigrams
involving the two swapped keycodes. -/
theorem Layout.abs_sfbCount_sub_swap_le (L : Layout Keycode) (p q : Position)
    (c : Corpus Keycode) :
    |(L.sfbCount c : ℤ) - ((L.swapPositions p q).sfbCount c : ℤ)|
      ≤ (touchCount (L.keyAt p) (L.keyAt q) c : ℤ) := by
  have h1 := L.sfbCount_le_swap_add_touchCount p q c
  have h2 := L.swap_sfbCount_le_add_touchCount p q c
  rw [abs_sub_le_iff]
  exact ⟨by omega, by omega⟩

/-- A swap inside one finger column leaves every corpus count unchanged. -/
theorem Layout.sfbCount_swap_of_sameColumn (L : Layout Keycode) {p q : Position}
    (h : colOf p = colOf q) (c : Corpus Keycode) :
    (L.swapPositions p q).sfbCount c = L.sfbCount c :=
  Layout.sfbCountIn_congr (L.sfbs_swapPositions_eq h) _

/-- A swap of two keycodes the corpus never uses leaves its count unchanged. -/
theorem Layout.sfbCount_swap_of_not_mem (L : Layout Keycode) {p q : Position}
    {c : Corpus Keycode} (hp : L.keyAt p ∉ c) (hq : L.keyAt q ∉ c) :
    (L.swapPositions p q).sfbCount c = L.sfbCount c := by
  have h1 := L.sfbCount_le_swap_add_touchCount p q c
  have h2 := L.swap_sfbCount_le_add_touchCount p q c
  rw [touchCount_eq_zero hp hq] at h1 h2
  omega

end

/-! ### Reading text through a keymap -/

/-- A partial map from characters to keycodes. -/
structure Keymap (Keycode : Type) where
  toKeycode : Char → Option Keycode

/-- The keystroke stream for a character stream.

Unmapped characters are dropped, so their neighbours become adjacent. This deliberately does
**not** commute with n-gram extraction: text `a?b` with `?` unmapped yields the bigram `ab`,
which the text itself never contains. It does commute with a total map
(`Keymap.corpus_ofTotal` together with `Fern.Ngram.bigrams_map`). -/
def Keymap.corpus (m : Keymap Keycode) (cs : List Char) : Corpus Keycode :=
  cs.filterMap m.toKeycode

/-- The keystroke stream for a string. -/
def Keymap.ofString (m : Keymap Keycode) (s : String) : Corpus Keycode :=
  m.corpus s.toList

/-- Every keycode the keymap produces lies in `s`. -/
def Keymap.MapsInto (m : Keymap Keycode) (s : Finset Keycode) : Prop :=
  ∀ ch k, m.toKeycode ch = some k → k ∈ s

/-- The keymap sending every character somewhere. -/
def Keymap.ofTotal (f : Char → Keycode) : Keymap Keycode := ⟨fun ch => some (f ch)⟩

omit [DecidableEq Keycode] in
@[simp] theorem Keymap.mem_corpus {m : Keymap Keycode} {cs : List Char} {k : Keycode} :
    k ∈ m.corpus cs ↔ ∃ ch ∈ cs, m.toKeycode ch = some k :=
  List.mem_filterMap

omit [DecidableEq Keycode] in
theorem Keymap.length_corpus_le (m : Keymap Keycode) (cs : List Char) :
    (m.corpus cs).length ≤ cs.length :=
  List.length_filterMap_le _ _

omit [DecidableEq Keycode] in
theorem Keymap.corpus_ofTotal (f : Char → Keycode) (cs : List Char) :
    (Keymap.ofTotal f).corpus cs = cs.map f := by
  simp [Keymap.corpus, Keymap.ofTotal]

theorem Layout.supports_corpus (L : Layout Keycode) {m : Keymap Keycode}
    (h : m.MapsInto L.usedKeys) (cs : List Char) : L.Supports (m.corpus cs) := by
  intro k hk
  obtain ⟨ch, -, hch⟩ := Keymap.mem_corpus.mp hk
  exact h ch k hch

/-- A keymap into a repertoire produces corpora supported by every layout on it, so layouts
can be compared on the same text with no side condition. -/
theorem LayoutOn.supports_corpus {R : Repertoire Keycode} (L : LayoutOn R) {m : Keymap Keycode}
    (h : m.MapsInto R.keys) (cs : List Char) : L.val.Supports (m.corpus cs) :=
  L.val.supports_corpus (by rw [L.property]; exact h) cs

end Fern.Ortholinear
