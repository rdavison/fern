module
public import FernImpl.Bits
public import Fern.Solver.Proof.Table
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Correctness of bit operations on key masks

`decode m` is the set of keys whose bits are set in `m`. The table-driven `pop30` and `hibit` are
proved to compute its size and its largest element for every 30-bit mask.
-/

@[expose] public section

namespace FernImpl

open Finset

/-- The keys whose bits are set in a mask. -/
def decode (m : Nat) : Finset (Fin 30) := univ.filter fun i => m.testBit i.val

@[simp] theorem mem_decode {m : Nat} {i : Fin 30} : i ∈ decode m ↔ m.testBit i.val = true := by
  simp [decode]

/-! ### Population count -/

theorem natPop_eq_sum : ∀ fuel i, natPop fuel i = ∑ k ∈ range fuel, if i.testBit k then 1 else 0
  | 0, _ => rfl
  | fuel + 1, i => by
    rw [natPop, natPop_eq_sum fuel (i / 2), Finset.sum_range_succ']
    simp only [Nat.testBit_div_two, Nat.testBit_zero, decide_eq_true_eq]
    split <;> omega

theorem natPop_le : ∀ fuel i, natPop fuel i ≤ fuel
  | 0, _ => Nat.le_refl 0
  | fuel + 1, i => by
    have := natPop_le fuel (i / 2)
    have : i % 2 < 2 := Nat.mod_lt _ (by decide)
    rw [natPop]
    omega

theorem card_decode (m : Nat) :
    (decode m).card = ∑ k ∈ range 30, if m.testBit k then 1 else 0 := by
  rw [decode, card_filter]
  exact Fin.sum_univ_eq_sum_range (fun k => if m.testBit k then 1 else 0) 30

theorem popTable_get (k : Nat) (hk : k < 2 ^ 15) :
    (popTable.get! k).toUInt64.toNat = natPop 15 k := by
  rw [popTable, get!_mkBytes _ _ hk]
  have := natPop_le 15 k
  simp only [UInt8.toNat_toUInt64, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

section
-- The tables are exposed 32K-entry closed data; keep the unifier from evaluating them.
attribute [local irreducible] popTable hibTable

/-- The table-driven population count is the number of keys in the mask. -/
theorem pop30_eq (m : UInt64) (hm : m.toNat < 2 ^ 30) : (pop30 m).toNat = (decode m.toNat).card := by
  have hlo : (m &&& 0x7FFF).toNat = m.toNat % 2 ^ 15 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod m.toNat 15
  have hhi : (m >>> 15).toNat = m.toNat / 2 ^ 15 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hq : m.toNat / 2 ^ 15 < 2 ^ 15 := by omega
  have hr : m.toNat % 2 ^ 15 < 2 ^ 15 := Nat.mod_lt _ (by decide)
  have e1 : (popTable.get! (m &&& 0x7FFF).toNat).toUInt64.toNat = natPop 15 (m.toNat % 2 ^ 15) := by
    rw [hlo]
    exact popTable_get _ hr
  have e2 : (popTable.get! (m >>> 15).toNat).toUInt64.toNat = natPop 15 (m.toNat / 2 ^ 15) := by
    rw [hhi]
    exact popTable_get _ hq
  have hsum : natPop 15 (m.toNat % 2 ^ 15) + natPop 15 (m.toNat / 2 ^ 15) = (decode m.toNat).card := by
    have s1 : (∑ k ∈ range 15, if (m.toNat % 2 ^ 15).testBit k then 1 else 0) =
        ∑ k ∈ range 15, if m.toNat.testBit k then 1 else 0 :=
      Finset.sum_congr rfl fun k hk => by
        rw [Finset.mem_range] at hk
        rw [Nat.testBit_mod_two_pow]
        simp [hk]
    have s2 : (∑ k ∈ range 15, if (m.toNat / 2 ^ 15).testBit k then 1 else 0) =
        ∑ k ∈ range 15, if m.toNat.testBit (15 + k) then 1 else 0 :=
      Finset.sum_congr rfl fun k _ => by rw [Nat.testBit_div_two_pow, Nat.add_comm]
    rw [natPop_eq_sum, natPop_eq_sum, s1, s2, card_decode, show (30 : Nat) = 15 + 15 from rfl,
      Finset.sum_range_add]
  have p1 := natPop_le 15 (m.toNat % 2 ^ 15)
  have p2 := natPop_le 15 (m.toNat / 2 ^ 15)
  have hlt : natPop 15 (m.toNat % 2 ^ 15) + natPop 15 (m.toNat / 2 ^ 15) < 2 ^ 64 := by omega
  unfold pop30
  rw [UInt64.toNat_add, e1, e2, Nat.mod_eq_of_lt hlt, hsum]

end

theorem log2_lt_of_lt {k n : Nat} (h : k < 2 ^ n) (hn : 0 < n) : Nat.log2 k < n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Nat.log2_zero]; omega
  · exact (Nat.log2_lt (by omega)).mpr h

theorem hibTable_get (k : Nat) (hk : k < 2 ^ 15) :
    (hibTable.get! k).toUInt64.toNat = Nat.log2 k := by
  rw [hibTable, get!_mkBytes _ _ hk]
  have := log2_lt_of_lt hk (by decide)
  simp only [UInt8.toNat_toUInt64, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

theorem log2_eq_add_log2_div {n : Nat} (h : 2 ^ 15 ≤ n) :
    Nat.log2 n = 15 + Nat.log2 (n / 2 ^ 15) := by
  have hq : n / 2 ^ 15 ≠ 0 := by
    have : 1 ≤ n / 2 ^ 15 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    omega
  have l1 := Nat.log2_self_le hq
  have l2 := @Nat.lt_log2_self (n / 2 ^ 15)
  rw [Nat.log2_eq_iff (by omega)]
  constructor
  · rw [Nat.pow_add]
    calc 2 ^ 15 * 2 ^ Nat.log2 (n / 2 ^ 15) ≤ 2 ^ 15 * (n / 2 ^ 15) := Nat.mul_le_mul_left _ l1
      _ ≤ n := Nat.mul_div_le n (2 ^ 15)
  · have hl := (Nat.div_lt_iff_lt_mul (show 0 < 2 ^ 15 by decide)).mp l2
    rw [show 15 + Nat.log2 (n / 2 ^ 15) + 1 = 15 + (Nat.log2 (n / 2 ^ 15) + 1) by omega, Nat.pow_add,
      Nat.mul_comm]
    exact hl

section
attribute [local irreducible] popTable hibTable

/-- The table-driven highest bit is `Nat.log2` of the mask. -/
theorem hibit_eq (m : UInt64) (hm : m.toNat < 2 ^ 30) : (hibit m).toNat = Nat.log2 m.toNat := by
  have hhi : (m >>> 15).toNat = m.toNat / 2 ^ 15 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  unfold hibit
  split
  · rename_i h
    have h0 : (m >>> 15).toNat = 0 := by
      have := congrArg UInt64.toNat (eq_of_beq h)
      simpa using this
    rw [hhi] at h0
    have hsmall : m.toNat < 2 ^ 15 := by
      rcases Nat.lt_or_ge m.toNat (2 ^ 15) with h' | h'
      · exact h'
      · exact absurd h0 (by have := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega : 1 * 2 ^ 15 ≤ m.toNat); omega)
    exact hibTable_get _ hsmall
  · rename_i h
    have hne : (m >>> 15) ≠ 0 := fun h' => h (by simp [h'])
    have hge : 2 ^ 15 ≤ m.toNat := by
      by_contra hlt
      apply hne
      apply UInt64.toNat_inj.mp
      rw [hhi, Nat.div_eq_of_lt (by omega)]
      rfl
    have hq : m.toNat / 2 ^ 15 < 2 ^ 15 := by omega
    have hl := log2_lt_of_lt hq (by decide)
    rw [UInt64.toNat_add, hhi, hibTable_get _ hq, log2_eq_add_log2_div hge]
    simp only [UInt64.reduceToNat]
    omega

end

/-! ### Clearing the highest bit -/

theorem toNat_bit (b : UInt64) (hb : b.toNat < 64) : (bit b).toNat = 2 ^ b.toNat := by
  simp only [bit, UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb)

theorem log2_lt_thirty {n : Nat} (h : n < 2 ^ 30) : Nat.log2 n < 30 := log2_lt_of_lt h (by decide)

/-- Clearing the highest bit of a mask. -/
theorem clearHigh_toNat (r : UInt64) (hr : r.toNat < 2 ^ 30) :
    (r ^^^ bit (hibit r)).toNat = r.toNat ^^^ 2 ^ Nat.log2 r.toNat := by
  have hl := log2_lt_thirty hr
  rw [UInt64.toNat_xor, toNat_bit _ (by rw [hibit_eq r hr]; omega), hibit_eq r hr]

theorem clearHigh_lt (r : UInt64) (hr : r.toNat < 2 ^ 30) :
    (r ^^^ bit (hibit r)).toNat < 2 ^ 30 := by
  rw [clearHigh_toNat r hr]
  exact Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by decide) (log2_lt_thirty hr))

theorem log2_mem_decode (r : UInt64) (hr : r.toNat < 2 ^ 30) (h0 : r.toNat ≠ 0) :
    (⟨Nat.log2 r.toNat, log2_lt_thirty hr⟩ : Fin 30) ∈ decode r.toNat := by
  rw [mem_decode]
  exact Nat.testBit_log2 h0

/-- Clearing the highest bit removes exactly the largest key. -/
theorem decode_clearHigh (r : UInt64) (hr : r.toNat < 2 ^ 30) (h0 : r.toNat ≠ 0) :
    decode (r ^^^ bit (hibit r)).toNat =
      (decode r.toNat).erase ⟨Nat.log2 r.toNat, log2_lt_thirty hr⟩ := by
  ext i
  rw [clearHigh_toNat r hr, Finset.mem_erase, mem_decode, mem_decode, Nat.testBit_xor,
    Nat.testBit_two_pow]
  by_cases h : Nat.log2 r.toNat = i.val
  · have hl : r.toNat.testBit i.val = true := h ▸ Nat.testBit_log2 h0
    simp [hl, h]
  · have hne : i ≠ ⟨Nat.log2 r.toNat, log2_lt_thirty hr⟩ := fun e => h (by rw [e])
    simp [h, hne]

theorem card_decode_clearHigh (r : UInt64) (hr : r.toNat < 2 ^ 30) (h0 : r.toNat ≠ 0) :
    (decode (r ^^^ bit (hibit r)).toNat).card + 1 = (decode r.toNat).card := by
  rw [decode_clearHigh r hr h0, Finset.card_erase_of_mem (log2_mem_decode r hr h0)]
  have : 0 < (decode r.toNat).card := Finset.card_pos.mpr ⟨_, log2_mem_decode r hr h0⟩
  omega

theorem decode_zero : decode 0 = ∅ := by
  ext i
  simp

/-! ### Folding over set bits -/

/-- The set bits of `r`, highest first, in the order `foldBits` visits them. -/
def bitsDesc : Nat → UInt64 → List UInt64
  | 0, _ => []
  | fuel + 1, r => if r == 0 then [] else hibit r :: bitsDesc fuel (r ^^^ bit (hibit r))

theorem foldBits_eq_foldl {β : Type} (f : β → UInt64 → β) :
    ∀ fuel r acc, foldBits f fuel r acc = (bitsDesc fuel r).foldl f acc
  | 0, _, _ => rfl
  | fuel + 1, r, acc => by
    simp only [foldBits, bitsDesc]
    split
    · rfl
    · rw [List.foldl_cons, foldBits_eq_foldl f fuel]

/-- `foldBits` visits each key of the mask exactly once, given enough fuel. -/
theorem bitsDesc_spec : ∀ fuel (r : UInt64), r.toNat < 2 ^ 30 → (decode r.toNat).card ≤ fuel →
    ((bitsDesc fuel r).map UInt64.toNat).Nodup ∧
      ∀ n, n ∈ (bitsDesc fuel r).map UInt64.toNat ↔ ∃ i ∈ decode r.toNat, i.val = n
  | 0, r, _, hc => by
    have hempty : decode r.toNat = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [bitsDesc, hempty]
  | fuel + 1, r, hr, hc => by
    by_cases h0 : r = 0
    · subst h0
      simp [bitsDesc, decode_zero]
    · have h0' : r.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
      have hcard := card_decode_clearHigh r hr h0'
      obtain ⟨ih1, ih2⟩ := bitsDesc_spec fuel _ (clearHigh_lt r hr) (by omega)
      have hne : (r == 0) = false := by simpa using h0
      simp only [bitsDesc, hne, Bool.false_eq_true, ↓reduceIte, List.map_cons, hibit_eq r hr]
      refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, ih1⟩, fun n => ?_⟩
      · obtain ⟨i, hi, hv⟩ := (ih2 _).mp hmem
        rw [decode_clearHigh r hr h0', Finset.mem_erase] at hi
        exact hi.1 (Fin.ext hv)
      · rw [List.mem_cons, ih2, decode_clearHigh r hr h0']
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨_, log2_mem_decode r hr h0', rfl⟩
          · exact ⟨i, (Finset.mem_erase.mp hi).2, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          by_cases he : i = ⟨Nat.log2 r.toNat, log2_lt_thirty hr⟩
          · exact Or.inl (by rw [he])
          · exact Or.inr ⟨i, Finset.mem_erase.mpr ⟨he, hi⟩, rfl⟩

/-- Summing over the visited bits is summing over the decoded keys. -/
theorem sum_bitsDesc (g : Nat → Nat) (fuel : Nat) (r : UInt64) (hr : r.toNat < 2 ^ 30)
    (hc : (decode r.toNat).card ≤ fuel) :
    ((bitsDesc fuel r).map fun b => g b.toNat).sum = ∑ i ∈ decode r.toNat, g i.val := by
  obtain ⟨hnd, hmem⟩ := bitsDesc_spec fuel r hr hc
  have himg : ((bitsDesc fuel r).map UInt64.toNat).toFinset = (decode r.toNat).image Fin.val := by
    ext n
    rw [List.mem_toFinset, hmem, Finset.mem_image]
  rw [show ((bitsDesc fuel r).map fun b => g b.toNat) = ((bitsDesc fuel r).map UInt64.toNat).map g by
      rw [List.map_map]; rfl,
    ← List.sum_toFinset g hnd, himg, Finset.sum_image (fun a _ b _ h => Fin.ext h)]

end FernImpl
