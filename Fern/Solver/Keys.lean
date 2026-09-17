module
public import Fern.Solver.Theorem

/-!
# The thirty keys and counting text

The solver's keys are the letters `a`–`z` and `, . ' ;`, numbered in that order. Text is read
case-folded: `A` is typed as `a`. Every other character, including the space and the newline, is
unmapped, so it breaks the stream of bigrams.

`countLines` tallies a text's bigrams in one pass, line by line, into a 900-cell array, and is proved
to agree with `bigramCount` of the whole text. That is the table `solveText_isLeast` speaks about.
-/

@[expose] public section

namespace Fern.Solver

open Fern.Ortholinear

/-- The thirty keys, in key-number order. -/
def keyChars : List Char := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', ',', '.', '\'', ';']

theorem length_keyChars : keyChars.length = 30 := rfl

/-- The key number of a character, folding case. -/
def keyOf (c : Char) : Option (Fin 30) :=
  (keyChars.finIdxOf? c.toLower).map (Fin.cast length_keyChars)

/-- The keymap for text: case-folded letters and `, . ' ;`. -/
def textKeymap : Keymap (Fin 30) := ⟨keyOf⟩

theorem keyOf_newline : keyOf '\n' = none := rfl

/-! ### Unmapped characters split the bigrams -/

theorem bigramsOf_cons_cons {K : Type} (m : Keymap K) (x y : Char) (rest : List Char) :
    m.bigramsOf (x :: y :: rest) = (m.mapPair x y).toList ++ m.bigramsOf (y :: rest) := by
  cases h : m.mapPair x y <;> simp [Keymap.bigramsOf, Fern.Ngram.bigrams_cons_cons, h]

theorem bigramsOf_cons_none {K : Type} (m : Keymap K) {c : Char} (h : m.toKeycode c = none)
    (ys : List Char) : m.bigramsOf (c :: ys) = m.bigramsOf ys := by
  cases ys with
  | nil => rfl
  | cons y ys => simp [bigramsOf_cons_cons, Keymap.mapPair, h]

/-- An unmapped character splits the text's bigrams into those before it and those after it. -/
theorem bigramsOf_append_none {K : Type} (m : Keymap K) {c : Char}
    (h : m.toKeycode c = none) (ys : List Char) :
    ∀ xs, m.bigramsOf (xs ++ c :: ys) = m.bigramsOf xs ++ m.bigramsOf ys
  | [] => by
    rw [List.nil_append, bigramsOf_cons_none m h]
    rfl
  | [x] => by
    simp only [List.cons_append, List.nil_append, bigramsOf_cons_cons, bigramsOf_cons_none m h]
    simp [Keymap.mapPair, h, Keymap.bigramsOf, Fern.Ngram.bigrams]
  | x :: x₂ :: xs => by
    simp only [List.cons_append, bigramsOf_cons_cons]
    rw [← List.cons_append, bigramsOf_append_none m h ys (x₂ :: xs), List.append_assoc]

/-- Lines joined by newlines. -/
def joinLines : List (List Char) → List Char
  | [] => []
  | [l] => l
  | l :: l₂ :: ls => l ++ '\n' :: joinLines (l₂ :: ls)

/-- A text's bigrams are its lines' bigrams. -/
theorem bigramsOf_joinLines : ∀ ls : List (List Char),
    textKeymap.bigramsOf (joinLines ls) = ls.flatMap textKeymap.bigramsOf
  | [] => rfl
  | [l] => by simp [joinLines]
  | l :: l₂ :: ls => by
    rw [joinLines, bigramsOf_append_none _ keyOf_newline, bigramsOf_joinLines (l₂ :: ls),
      List.flatMap_cons]
    rfl

/-! ### Counting in one pass -/

/-- Add one to cell `30 a + b` for each bigram `(a, b)`. -/
def countInto : Array ℕ → List (Bigram (Fin 30)) → Array ℕ
  | acc, [] => acc
  | acc, (a, b) :: bs => countInto (acc.modify (a.val * 30 + b.val) (· + 1)) bs

theorem size_countInto : ∀ (acc : Array ℕ) (bs : List (Bigram (Fin 30))),
    (countInto acc bs).size = acc.size
  | _, [] => rfl
  | acc, (a, b) :: bs => by rw [countInto, size_countInto, Array.size_modify]

theorem cell_eq_iff {a b x y : Fin 30} : x.val * 30 + y.val = a.val * 30 + b.val ↔ (x, y) = (a, b) := by
  constructor
  · intro h
    have hx := x.isLt
    have hy := y.isLt
    have ha := a.isLt
    have hb := b.isLt
    simp only [Prod.mk.injEq]
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]

theorem getD_countInto (a b : Fin 30) : ∀ (acc : Array ℕ) (bs : List (Bigram (Fin 30))),
    acc.size = 900 →
      (countInto acc bs).getD (a.val * 30 + b.val) 0 =
        acc.getD (a.val * 30 + b.val) 0 + bigramCount bs a b
  | acc, [], _ => by simp [countInto, bigramCount]
  | acc, (x, y) :: bs, hs => by
    have hi : a.val * 30 + b.val < 900 := by omega
    rw [countInto, getD_countInto a b _ bs (by rw [Array.size_modify, hs])]
    have hmod : (acc.modify (x.val * 30 + y.val) (· + 1)).getD (a.val * 30 + b.val) 0 =
        acc.getD (a.val * 30 + b.val) 0 + if (x, y) = (a, b) then 1 else 0 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, ← cell_eq_iff (a := a)]
      have : a.val * 30 + b.val < acc.size := by omega
      split <;> simp [Array.getElem?_eq_getElem this]
    rw [hmod]
    simp only [bigramCount, List.countP_cons, decide_eq_true_eq]
    split <;> omega

/-- The bigram counts of a text given as lines, in one pass per line. -/
def countLines (ls : List (List Char)) : Array ℕ :=
  ls.foldl (fun acc l => countInto acc (textKeymap.bigramsOf l)) (Array.replicate 900 0)

theorem getD_foldl_countInto (a b : Fin 30) : ∀ (ls : List (List Char)) (acc : Array ℕ),
    acc.size = 900 →
      (ls.foldl (fun acc l => countInto acc (textKeymap.bigramsOf l)) acc).getD (a.val * 30 + b.val) 0 =
        acc.getD (a.val * 30 + b.val) 0 + bigramCount (ls.flatMap textKeymap.bigramsOf) a b
  | [], acc, _ => by simp [bigramCount]
  | l :: ls, acc, hs => by
    rw [List.foldl_cons, getD_foldl_countInto a b ls _ (by rw [size_countInto, hs]),
      getD_countInto a b acc _ hs, List.flatMap_cons]
    simp only [bigramCount, List.countP_append]
    omega

/-- Counting line by line gives the bigram counts of the whole text. -/
theorem countLines_spec (ls : List (List Char)) (a b : Fin 30) :
    (countLines ls).getD (a.val * 30 + b.val) 0 = bigramCount (textKeymap.bigramsOf (joinLines ls)) a b := by
  rw [countLines, getD_foldl_countInto a b ls _ (by simp), bigramsOf_joinLines]
  have : a.val * 30 + b.val < 900 := by omega
  simp [Array.getD_eq_getD_getElem?, this]

end Fern.Solver
