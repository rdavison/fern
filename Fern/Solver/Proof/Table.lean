module
public import FernImpl.Table

/-!
# Correctness of packed 32-bit tables

Reads return what was appended, appends never disturb earlier cells, and a table built by
`tabulate32` satisfies any invariant that each new cell preserves given the cells before it.
-/

@[expose] public section

namespace FernImpl

theorem size_emptyWithCapacity (c : Nat) : (ByteArray.emptyWithCapacity c).size = 0 := rfl

theorem get!_push_of_lt (t : ByteArray) (b : UInt8) {j : Nat} (h : j < t.size) :
    (t.push b).get! j = t.get! j := by
  obtain ⟨bs⟩ := t
  show (bs.push b)[j]! = bs[j]!
  have h' : j < bs.size := h
  rw [getElem!_pos (bs.push b) j (by simp; omega), getElem!_pos bs j h', Array.getElem_push_lt h']

theorem get!_push_self (t : ByteArray) (b : UInt8) : (t.push b).get! t.size = b := by
  obtain ⟨bs⟩ := t
  show (bs.push b)[bs.size]! = b
  rw [getElem!_pos (bs.push b) bs.size (by simp), Array.getElem_push_eq]

theorem size_push32 (t : ByteArray) (v : UInt32) : (push32 t v).size = t.size + 4 := by
  simp only [push32, ByteArray.size_push]

/-- Appending a cell leaves every earlier byte unchanged. -/
theorem get!_push32_of_lt (t : ByteArray) (v : UInt32) {j : Nat} (h : j < t.size) :
    (push32 t v).get! j = t.get! j := by
  simp only [push32]
  rw [get!_push_of_lt, get!_push_of_lt, get!_push_of_lt, get!_push_of_lt]
  all_goals (try simp only [ByteArray.size_push]); omega

theorem get32_push32_of_lt (t : ByteArray) (v : UInt32) {i : Nat} (h : 4 * (i + 1) ≤ t.size) :
    get32 (push32 t v) i = get32 t i := by
  simp only [get32]
  rw [get!_push32_of_lt _ _ (by omega), get!_push32_of_lt _ _ (by omega),
    get!_push32_of_lt _ _ (by omega), get!_push32_of_lt _ _ (by omega)]

theorem bytes_recombine (v : UInt32) :
    v.toUInt8.toUInt32 + ((v >>> 8).toUInt8.toUInt32 <<< 8) +
      ((v >>> 16).toUInt8.toUInt32 <<< 16) + ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  apply UInt32.toNat_inj.mp
  have hv := v.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
    UInt32.toNat_toUInt8, UInt8.toNat_toUInt32, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow]
  omega

/-- A freshly appended cell reads back as the value appended. -/
theorem get32_push32_self (t : ByteArray) (v : UInt32) {i : Nat} (h : t.size = 4 * i) :
    get32 (push32 t v) i = v := by
  have b0 : (push32 t v).get! (4 * i) = v.toUInt8 := by
    simp only [push32]
    rw [get!_push_of_lt, get!_push_of_lt, get!_push_of_lt, ← h, get!_push_self]
    all_goals (try simp only [ByteArray.size_push]); omega
  have b1 : (push32 t v).get! (4 * i + 1) = (v >>> 8).toUInt8 := by
    simp only [push32]
    rw [get!_push_of_lt, get!_push_of_lt,
      show 4 * i + 1 = (t.push v.toUInt8).size by simp only [ByteArray.size_push]; omega,
      get!_push_self]
    all_goals (try simp only [ByteArray.size_push]); omega
  have b2 : (push32 t v).get! (4 * i + 2) = (v >>> 16).toUInt8 := by
    simp only [push32]
    rw [get!_push_of_lt,
      show 4 * i + 2 = ((t.push v.toUInt8).push (v >>> 8).toUInt8).size by
        simp only [ByteArray.size_push]; omega,
      get!_push_self]
    simp only [ByteArray.size_push]; omega
  have b3 : (push32 t v).get! (4 * i + 3) = (v >>> 24).toUInt8 := by
    simp only [push32]
    rw [show 4 * i + 3 = (((t.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).size by
        simp only [ByteArray.size_push]; omega,
      get!_push_self]
  simp only [get32, b0, b1, b2, b3]
  exact bytes_recombine v

theorem size_tabulate32Aux (f : ByteArray → Nat → UInt32) :
    ∀ fuel i t, (tabulate32Aux f fuel i t).size = t.size + 4 * fuel
  | 0, _, _ => rfl
  | fuel + 1, i, t => by
    rw [tabulate32Aux, size_tabulate32Aux f fuel, size_push32]
    omega

theorem size_tabulate32 (n : Nat) (f : ByteArray → Nat → UInt32) :
    (tabulate32 n f).size = 4 * n := by
  rw [tabulate32, size_tabulate32Aux, size_emptyWithCapacity]
  omega

theorem get32_tabulate32Aux (P : Nat → UInt32 → Prop) (f : ByteArray → Nat → UInt32)
    (hf : ∀ t i, t.size = 4 * i → (∀ j < i, P j (get32 t j)) → P i (f t i)) :
    ∀ fuel i t, t.size = 4 * i → (∀ j < i, P j (get32 t j)) →
      ∀ j < i + fuel, P j (get32 (tabulate32Aux f fuel i t) j)
  | 0, i, t, _, ht, j, hj => by
    rw [tabulate32Aux]
    exact ht j (by omega)
  | fuel + 1, i, t, hs, ht, j, hj => by
    rw [tabulate32Aux]
    refine get32_tabulate32Aux P f hf fuel (i + 1) (push32 t (f t i))
      (by rw [size_push32, hs]; omega) (fun k hk => ?_) j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [get32_push32_of_lt _ _ (by omega)]
      exact ht k hk
    · rw [get32_push32_self _ _ hs]
      exact hf t k hs ht

/-- Every cell of a tabulated table satisfies any invariant that each new cell preserves, given
the cells before it. -/
theorem get32_tabulate32 (P : Nat → UInt32 → Prop) (n : Nat) (f : ByteArray → Nat → UInt32)
    (hf : ∀ t i, t.size = 4 * i → (∀ j < i, P j (get32 t j)) → P i (f t i)) :
    ∀ j < n, P j (get32 (tabulate32 n f) j) := fun j hj =>
  get32_tabulate32Aux P f hf n 0 _ (size_emptyWithCapacity _) (fun _ h => absurd h (by omega)) j
    (by omega)

theorem size_mkBytesAux (f : Nat → UInt8) :
    ∀ fuel i t, (mkBytesAux f fuel i t).size = t.size + fuel
  | 0, _, _ => rfl
  | fuel + 1, i, t => by
    rw [mkBytesAux, size_mkBytesAux f fuel, ByteArray.size_push]
    omega

theorem get!_mkBytesAux (f : Nat → UInt8) :
    ∀ fuel i t, t.size = i → (∀ j < i, t.get! j = f j) →
      ∀ j < i + fuel, (mkBytesAux f fuel i t).get! j = f j
  | 0, i, t, _, ht, j, hj => by
    rw [mkBytesAux]
    exact ht j (by omega)
  | fuel + 1, i, t, hs, ht, j, hj => by
    rw [mkBytesAux]
    refine get!_mkBytesAux f fuel (i + 1) (t.push (f i)) (by rw [ByteArray.size_push, hs])
      (fun k hk => ?_) j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [get!_push_of_lt _ _ (by omega)]
      exact ht k hk
    · rw [← hs, get!_push_self]

/-- A byte table returns the byte its generating function gives. -/
theorem get!_mkBytes (n : Nat) (f : Nat → UInt8) {j : Nat} (hj : j < n) :
    (mkBytes n f).get! j = f j :=
  get!_mkBytesAux f n 0 _ (size_emptyWithCapacity _) (fun _ h => absurd h (by omega)) j (by omega)

end FernImpl
