module
public import Fern.Ortholinear.Corpus

/-!
# Reading real text

`Keymap.corpus` drops unmapped characters and joins their neighbours. That suits a stream of
keystrokes but not prose: the space in "the cat" is a thumb keystroke, so `e` and `c` are never
typed back to back. `Keymap.bigramsOf` instead takes the text's own character bigrams and keeps
those whose two characters are both mapped, so an unmapped character breaks the stream. Equivalently
the text splits into `segments` of mapped keys, and every corpus theorem applies segment by segment.
The list-level corpus theorems (`Layout.sfbCountIn_le_swap_add_touchCountIn` and friends) apply to
`m.bigramsOf cs` directly.

Two letter–gap–letter patterns are kept apart. A *skipgram* has a mapped key in the middle; a
*spacegram* has exactly the space character there. A newline is not a space, so separate lines
never join.
-/

@[expose] public section

namespace Fern.Ortholinear

variable {K : Type}

/-- Map both characters of a pair, if both are mapped. -/
def Keymap.mapPair (m : Keymap K) (x y : Char) : Option (Bigram K) :=
  (m.toKeycode x).bind fun a => (m.toKeycode y).map fun b => (a, b)

/-- The text's own bigrams whose two characters are both mapped. -/
def Keymap.bigramsOf (m : Keymap K) (cs : List Char) : List (Bigram K) :=
  (Ngram.bigrams cs).filterMap fun p => m.mapPair p.1 p.2

/-- The text split into runs of mapped keys; every unmapped character ends a run. -/
def Keymap.segments (m : Keymap K) : List Char → List (Corpus K)
  | [] => [[]]
  | c :: cs =>
    match m.toKeycode c with
    | some k =>
      match m.segments cs with
      | [] => [[k]]
      | s :: rest => (k :: s) :: rest
    | none => [] :: m.segments cs

/-- Key–key–key patterns with all three characters mapped, reported as the outer pair. -/
def Keymap.skipgramsOf (m : Keymap K) (cs : List Char) : List (Bigram K) :=
  (Ngram.trigrams cs).filterMap fun t => (m.toKeycode t.2.1).bind fun _ => m.mapPair t.1 t.2.2

/-- Key–space–key patterns with both outer characters mapped, reported as the outer pair. -/
def Keymap.spacegramsOf (m : Keymap K) (cs : List Char) : List (Bigram K) :=
  (Ngram.trigrams cs).filterMap fun t => if t.2.1 = ' ' then m.mapPair t.1 t.2.2 else none

theorem Keymap.mapPair_eq_some {m : Keymap K} {x y : Char} {a b : K} :
    m.mapPair x y = some (a, b) ↔ m.toKeycode x = some a ∧ m.toKeycode y = some b := by
  unfold Keymap.mapPair
  cases m.toKeycode x <;> cases m.toKeycode y <;> simp

/-- A kept bigram comes from two adjacent mapped characters of the text: nothing is invented. -/
theorem Keymap.mem_bigramsOf {m : Keymap K} {cs : List Char} {a b : K} :
    (a, b) ∈ m.bigramsOf cs ↔
      ∃ x y, (x, y) ∈ Ngram.bigrams cs ∧ m.toKeycode x = some a ∧ m.toKeycode y = some b := by
  simp only [Keymap.bigramsOf, List.mem_filterMap, Keymap.mapPair_eq_some, Prod.exists]

/-- A spacegram comes from a mapped key, a space, and a mapped key, adjacent in the text. -/
theorem Keymap.mem_spacegramsOf {m : Keymap K} {cs : List Char} {a b : K} :
    (a, b) ∈ m.spacegramsOf cs ↔
      ∃ x y, (x, ' ', y) ∈ Ngram.trigrams cs ∧ m.toKeycode x = some a ∧ m.toKeycode y = some b := by
  simp only [Keymap.spacegramsOf, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨x, z, y, h, hs⟩
    split at hs
    · rename_i hz
      subst hz
      exact ⟨x, y, h, (Keymap.mapPair_eq_some.mp hs).1, (Keymap.mapPair_eq_some.mp hs).2⟩
    · exact absurd hs (by simp)
  · rintro ⟨x, y, h, hx, hy⟩
    exact ⟨x, ' ', y, h, by simp [Keymap.mapPair_eq_some.mpr ⟨hx, hy⟩]⟩

/-! ### Segments -/

theorem Keymap.segments_ne_nil (m : Keymap K) : ∀ cs, m.segments cs ≠ []
  | [] => by simp [Keymap.segments]
  | c :: cs => by
    unfold Keymap.segments
    cases m.toKeycode c with
    | none => simp
    | some k => cases m.segments cs <;> simp

theorem Keymap.segments_cons_none (m : Keymap K) {c : Char} (cs : List Char)
    (h : m.toKeycode c = none) : m.segments (c :: cs) = [] :: m.segments cs := by
  simp [Keymap.segments, h]

theorem Keymap.segments_cons_some (m : Keymap K) {c : Char} {k : K} {cs : List Char}
    {s : Corpus K} {rest : List (Corpus K)} (h : m.toKeycode c = some k)
    (hs : m.segments cs = s :: rest) : m.segments (c :: cs) = (k :: s) :: rest := by
  simp [Keymap.segments, h, hs]

/-- Joining the segments gives back the keystroke stream. -/
theorem Keymap.flatten_segments (m : Keymap K) : ∀ cs, (m.segments cs).flatten = m.corpus cs
  | [] => rfl
  | c :: cs => by
    have ih := m.flatten_segments cs
    cases h : m.toKeycode c with
    | none =>
      rw [m.segments_cons_none cs h, List.flatten_cons, List.nil_append, ih]
      simp [Keymap.corpus, h]
    | some k =>
      obtain ⟨s, rest, hs⟩ := List.exists_cons_of_ne_nil (m.segments_ne_nil cs)
      rw [m.segments_cons_some h hs, List.flatten_cons, List.cons_append, ← List.flatten_cons, ← hs, ih]
      simp [Keymap.corpus, h]

/-- The text's bigrams are exactly the bigrams inside each segment. -/
theorem Keymap.bigramsOf_eq_flatMap (m : Keymap K) :
    ∀ cs, m.bigramsOf cs = (m.segments cs).flatMap Ngram.bigrams
  | [] => rfl
  | [c] => by
    cases h : m.toKeycode c <;> simp [Keymap.bigramsOf, Keymap.segments, h]
  | c :: c₂ :: rest => by
    have ih := m.bigramsOf_eq_flatMap (c₂ :: rest)
    have hstep : m.bigramsOf (c :: c₂ :: rest) =
        (m.mapPair c c₂).toList ++ m.bigramsOf (c₂ :: rest) := by
      simp only [Keymap.bigramsOf, Ngram.bigrams_cons_cons, List.filterMap_cons]
      cases m.mapPair c c₂ <;> rfl
    rw [hstep, ih]
    obtain ⟨s', tl', hst⟩ := List.exists_cons_of_ne_nil (m.segments_ne_nil rest)
    cases h : m.toKeycode c with
    | none =>
      have hp : m.mapPair c c₂ = none := by simp [Keymap.mapPair, h]
      rw [hp, m.segments_cons_none _ h]
      simp
    | some k =>
      cases h₂ : m.toKeycode c₂ with
      | none =>
        have hp : m.mapPair c c₂ = none := by simp [Keymap.mapPair, h, h₂]
        rw [hp, m.segments_cons_some h (m.segments_cons_none rest h₂), m.segments_cons_none rest h₂]
        simp
      | some x =>
        have hp : m.mapPair c c₂ = some (k, x) := Keymap.mapPair_eq_some.mpr ⟨h, h₂⟩
        rw [hp, m.segments_cons_some h (m.segments_cons_some h₂ hst), m.segments_cons_some h₂ hst]
        simp [Ngram.bigrams_cons_cons]

variable [DecidableEq K]

/-- Same-finger bigrams of a text are the sum over its segments. -/
theorem Layout.sfbCountIn_bigramsOf (L : Layout K) (m : Keymap K) (cs : List Char) :
    L.sfbCountIn (m.bigramsOf cs) = ((m.segments cs).map L.sfbCount).sum := by
  rw [m.bigramsOf_eq_flatMap, Layout.sfbCountIn, List.countP_flatMap]
  rfl

end Fern.Ortholinear
