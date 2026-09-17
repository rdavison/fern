module
public import Fern.Solver.Proof.Step

/-!
# Correctness of the table fill

`fill` appends one cell per mask in increasing order. A proper submask is numerically smaller, so
when `step` reads the cells for smaller key sets they are already correct. Every key set of size at
most fifteen whose size is a multiple of three then holds its cheapest partition into triples.
-/

@[expose] public section

namespace FernImpl

open Finset Fern.Ortholinear Fern.Solver

/-! ### Submasks are smaller -/

theorem le_of_decode_subset {a b : Nat} (ha : a < 2 ^ 30) (h : decode a ⊆ decode b) : a ≤ b :=
  Nat.le_of_testBit fun k hk => by
    have hk30 : k < 30 := by
      by_contra h'
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))]
        at hk
      exact absurd hk (by decide)
    exact mem_decode.mp (h (mem_decode.mpr (show a.testBit (⟨k, hk30⟩ : Fin 30).val = true from hk)))

theorem lt_of_decode_ssubset {a b : Nat} (ha : a < 2 ^ 30) (h : decode a ⊆ decode b)
    (hc : (decode a).card < (decode b).card) : a < b :=
  lt_of_le_of_ne (le_of_decode_subset ha h) fun e => by
    rw [e] at hc
    exact lt_irrefl _ hc

/-- Masks below `2 ^ 30` are determined by their keys. -/
theorem decode_injOn {a b : Nat} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) (h : decode a = decode b) :
    a = b :=
  le_antisymm (le_of_decode_subset ha h.le) (le_of_decode_subset hb h.ge)

/-! ### Which masks are tabulated -/

section
attribute [local irreducible] hibTable popTable

theorem tabulated_iff {m : UInt64} (hm : m.toNat < 2 ^ 30) :
    tabulated m = true ↔
      (decode m.toNat).card ≠ 0 ∧ 3 ∣ (decode m.toNat).card ∧ (decode m.toNat).card ≤ 15 := by
  have hp := pop30_eq m hm
  simp only [tabulated, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq,
    ← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.le_iff_toNat_le, hp, Nat.dvd_iff_mod_eq_zero]
  simp [and_assoc]

end

theorem bestTriplesRef_empty (w : Fin 30 → Fin 30 → ℕ) : bestTriplesRef w ∅ = 0 := by
  simp [bestTriplesRef, bestTriplesTop]

theorem toNat_natToUInt64 {i : Nat} (hi : i < 2 ^ 30) : i.toUInt64.toNat = i := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

/-! ### The fill -/

/-- Every tabulated cell holds the cheapest partition of its keys into triples. -/
theorem fill_spec {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {j : Nat}
    (hj : j < 2 ^ 30) (h3 : 3 ∣ (decode j).card) (h15 : (decode j).card ≤ 15) :
    (get32 (fill (swTable cnt)) j).toNat = bestTriplesRef (fun a b => cnt a.val b.val) (decode j) := by
  let P : Nat → UInt32 → Prop := fun j v => j < 2 ^ 30 → 3 ∣ (decode j).card →
    (decode j).card ≤ 15 → v.toNat = bestTriplesRef (fun a b => cnt a.val b.val) (decode j)
  refine get32_tabulate32 P (2 ^ 30) _ (fun t i _ hprev hi hi3 hi15 => ?_) j hj hj h3 h15
  have hm := toNat_natToUInt64 hi
  show (if tabulated i.toUInt64 then (step (swTable cnt) t i.toUInt64).toUInt32 else 0).toNat = _
  by_cases h0 : (decode i).card = 0
  · have hnt : tabulated i.toUInt64 = false := by
      cases htab : tabulated i.toUInt64
      · rfl
      · exact absurd ((tabulated_iff (by rw [hm]; exact hi)).mp htab).1 (by rw [hm]; exact not_not.mpr h0)
    rw [hnt, Finset.card_eq_zero.mp h0, bestTriplesRef_empty]
    rfl
  · have htab : tabulated i.toUInt64 = true :=
      (tabulated_iff (by rw [hm]; exact hi)).mpr (by rw [hm]; exact ⟨h0, hi3, hi15⟩)
    rw [if_pos htab]
    have hs := step_spec hbound (t := t) (m := i.toUInt64) (by rw [hm]; exact hi)
      (by rw [hm]; exact Finset.card_pos.mp (by omega)) (by rw [hm]; exact hi3)
      (fun m' hm' hsub hc => by
        rw [hm] at hsub hc
        exact hprev _ (lt_of_decode_ssubset hm' hsub (by omega)) hm' (by omega) (by omega))
    rw [hm] at hs
    have hlt : bestTriplesRef (fun a b => cnt a.val b.val) (decode i) < 2 ^ 32 :=
      lt_of_le_of_lt ((bestTriplesRef_le_pieceWeight hi3).trans (pieceWeight_le_totalWeight cnt _)) hbound
    rw [UInt64.toNat_toUInt32, hs, Nat.mod_eq_of_lt hlt]

end FernImpl
