module

/-!
# N-gram extraction

Generic extraction of consecutive windows from a list lives in the `Fern.Ngram` namespace and
is the single implementation. The top-level `unigrams`, `bigrams`, `trigrams`, `skipgrams` and
`trills` are `Char`-specific wrappers that render each window as a `String`; they are proved
below to satisfy exactly the recursions they were originally defined by.

The generic forms are what the layout model consumes: `Fern.Ngram.bigrams` on a list of
keycodes produces a `List (Fern.Ortholinear.Bigram Keycode)` directly.
-/

@[expose] public section

namespace Fern.Ngram

variable {α β : Type}

/-- Single elements. -/
def singles (l : List α) : List α := l

/-- Consecutive pairs: ab, bc, cd, ... -/
def bigrams (l : List α) : List (α × α) := l.zip l.tail

/-- Consecutive triples: abc, bcd, cde, ... -/
def trigrams (l : List α) : List (α × α × α) := l.zip (bigrams l.tail)

/-- Pairs with one skipped between: a_c, b_d, c_e ...
    Captures same-finger usage even with an intervening key. -/
def skipgrams (l : List α) : List (α × α) := l.zip l.tail.tail

/-- ABA patterns where the first and third elements are equal, reported as the `AB` pair.
    Detects alternation between two keys. Only `BEq` is required, matching the original
    definition, which used `==`. -/
def trills [BEq α] (l : List α) : List (α × α) :=
  (trigrams l).filterMap fun t => if t.1 == t.2.2 then some (t.1, t.2.1) else none

/-! ### Defining equations -/

@[simp] theorem singles_eq (l : List α) : singles l = l := rfl

@[simp] theorem bigrams_nil : bigrams ([] : List α) = [] := rfl
@[simp] theorem bigrams_singleton (a : α) : bigrams [a] = [] := rfl
@[simp] theorem bigrams_cons_cons (a b : α) (l : List α) :
    bigrams (a :: b :: l) = (a, b) :: bigrams (b :: l) := rfl

/-- A two-element list has exactly one bigram. -/
@[simp] theorem bigrams_pair (a b : α) : bigrams [a, b] = [(a, b)] := rfl

@[simp] theorem trigrams_nil : trigrams ([] : List α) = [] := rfl
@[simp] theorem trigrams_singleton (a : α) : trigrams [a] = [] := rfl
@[simp] theorem trigrams_pair (a b : α) : trigrams [a, b] = [] := rfl
@[simp] theorem trigrams_cons_cons_cons (a b c : α) (l : List α) :
    trigrams (a :: b :: c :: l) = (a, b, c) :: trigrams (b :: c :: l) := rfl

@[simp] theorem skipgrams_nil : skipgrams ([] : List α) = [] := rfl
@[simp] theorem skipgrams_singleton (a : α) : skipgrams [a] = [] := rfl
@[simp] theorem skipgrams_pair (a b : α) : skipgrams [a, b] = [] := rfl
@[simp] theorem skipgrams_cons_cons_cons (a b c : α) (l : List α) :
    skipgrams (a :: b :: c :: l) = (a, c) :: skipgrams (b :: c :: l) := rfl

@[simp] theorem trills_nil [BEq α] : trills ([] : List α) = [] := rfl
@[simp] theorem trills_singleton [BEq α] (a : α) : trills [a] = [] := rfl
@[simp] theorem trills_pair [BEq α] (a b : α) : trills [a, b] = [] := rfl
theorem trills_cons_cons_cons [BEq α] (a b c : α) (l : List α) :
    trills (a :: b :: c :: l) =
      if a == c then (a, b) :: trills (b :: c :: l) else trills (b :: c :: l) := by
  cases h : a == c <;> simp [trills, h]

/-! ### Structure -/

theorem length_bigrams (l : List α) : (bigrams l).length = l.length - 1 := by
  rw [bigrams, List.length_zip, List.length_tail]
  omega

theorem mem_bigrams {b : α × α} {l : List α} (h : b ∈ bigrams l) : b.1 ∈ l ∧ b.2 ∈ l := by
  obtain ⟨h1, h2⟩ := List.of_mem_zip h
  exact ⟨h1, List.mem_of_mem_tail h2⟩

theorem map_snd_bigrams (l : List α) : (bigrams l).map Prod.snd = l.tail := by
  rw [bigrams, List.map_snd_zip]
  simp [List.length_tail]

theorem map_fst_bigrams : ∀ l : List α, (bigrams l).map Prod.fst = l.dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [bigrams_cons_cons, List.map_cons, map_fst_bigrams (b :: l)]
    rfl

/-- Extraction commutes with a total relabelling of the alphabet. -/
theorem bigrams_map (f : α → β) (l : List α) :
    bigrams (l.map f) = (bigrams l).map (Prod.map f f) := by
  rw [bigrams, bigrams, ← List.map_tail, List.zip_map]

end Fern.Ngram

/-! ### Character wrappers

Each wrapper renders the generic windows as strings. The `*_spec` definitions below are
verbatim copies of the original recursions, and the `*_eq_spec` theorems check that nothing
changed. -/

/-- Single characters. -/
def unigrams (chars : List Char) : List String :=
  (Fern.Ngram.singles chars).map fun c => String.ofList [c]

/-- Consecutive pairs: ab, bc, cd, ... -/
def bigrams (chars : List Char) : List String :=
  (Fern.Ngram.bigrams chars).map fun p => String.ofList [p.1, p.2]

/-- Consecutive triples: abc, bcd, cde, ... -/
def trigrams (chars : List Char) : List String :=
  (Fern.Ngram.trigrams chars).map fun t => String.ofList [t.1, t.2.1, t.2.2]

/-- Pairs with one skipped between: a_c, b_d, c_e ...
    Captures same-finger usage even with an intervening key. -/
def skipgrams (chars : List Char) : List String :=
  (Fern.Ngram.skipgrams chars).map fun p => String.ofList [p.1, p.2]

/-- ABA patterns where the first and third characters are the same.
    Detects alternation between two keys. -/
def trills (chars : List Char) : List String :=
  (Fern.Ngram.trills chars).map fun p => String.ofList [p.1, p.2]

private def unigramsSpec (chars : List Char) : List String :=
  chars.map fun c => String.ofList [c]

private def bigramsSpec (chars : List Char) : List String :=
  match chars with
  | a :: b :: rest => String.ofList [a, b] :: bigramsSpec (b :: rest)
  | _ => []

private def trigramsSpec (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest => String.ofList [a, b, c] :: trigramsSpec (b :: c :: rest)
  | _ => []

private def skipgramsSpec (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest => String.ofList [a, c] :: skipgramsSpec (b :: c :: rest)
  | _ => []

private def trillsSpec (chars : List Char) : List String :=
  match chars with
  | a :: b :: c :: rest =>
    let next := trillsSpec (b :: c :: rest)
    if a == c then String.ofList [a, b] :: next
    else next
  | _ => []

private theorem unigrams_eq_spec (chars : List Char) : unigrams chars = unigramsSpec chars := rfl

private theorem bigrams_eq_spec : ∀ chars : List Char, bigrams chars = bigramsSpec chars
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    rw [bigrams, Fern.Ngram.bigrams_cons_cons, List.map_cons, ← bigrams,
      bigrams_eq_spec (b :: rest)]
    rfl

private theorem trigrams_eq_spec : ∀ chars : List Char, trigrams chars = trigramsSpec chars
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
    rw [trigrams, Fern.Ngram.trigrams_cons_cons_cons, List.map_cons, ← trigrams,
      trigrams_eq_spec (b :: c :: rest)]
    rfl

private theorem skipgrams_eq_spec : ∀ chars : List Char, skipgrams chars = skipgramsSpec chars
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
    rw [skipgrams, Fern.Ngram.skipgrams_cons_cons_cons, List.map_cons, ← skipgrams,
      skipgrams_eq_spec (b :: c :: rest)]
    rfl

private theorem trills_eq_spec : ∀ chars : List Char, trills chars = trillsSpec chars
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
    have ih := trills_eq_spec (b :: c :: rest)
    simp only [trills] at ih
    simp only [trills, Fern.Ngram.trills_cons_cons_cons, trillsSpec]
    cases a == c <;> simp [ih]
