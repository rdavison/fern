module
public import FernImpl.Solve
public import Fern.Solver.Proof.Bits
public import Fern.Solver.Spec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Correctness of the weight table

The pair-weight table holds both directions of each pair of keys, a key's row sum over a mask is
the sum over the decoded keys, and adding a key to a piece adds exactly its row sum.
-/

@[expose] public section

namespace FernImpl

open Finset Fern.Ortholinear

theorem get32_tabulate32_const (n : Nat) (g : Nat → UInt32) {i : Nat} (hi : i < n) :
    get32 (tabulate32 n fun _ j => g j) i = g i :=
  get32_tabulate32 (fun j v => v = g j) n _ (fun _ _ _ _ => rfl) i hi

theorem sumBelow_eq (f : Nat → Nat) : ∀ n, sumBelow f n = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by rw [sumBelow, sumBelow_eq f n, Finset.sum_range_succ]

theorem totalWeight_eq (cnt : Nat → Nat → Nat) :
    totalWeight cnt = ∑ p ∈ range 30 ×ˢ range 30, cnt p.1 p.2 := by
  rw [totalWeight, sumBelow_eq, Finset.sum_product]
  exact Finset.sum_congr rfl fun a _ => sumBelow_eq (cnt a) 30

/-- Both directions of a pair of distinct keys fit within the total weight. -/
theorem pair_le_totalWeight (cnt : Nat → Nat → Nat) {a b : Nat} (ha : a < 30) (hb : b < 30)
    (hab : a ≠ b) : cnt a b + cnt b a ≤ totalWeight cnt := by
  rw [totalWeight_eq]
  have hsub : ({(a, b), (b, a)} : Finset (Nat × Nat)) ⊆ range 30 ×ˢ range 30 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [ha, hb]
  have hne : (a, b) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
  calc cnt a b + cnt b a = ∑ p ∈ ({(a, b), (b, a)} : Finset (Nat × Nat)), cnt p.1 p.2 := by
        rw [Finset.sum_pair hne]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- The table holds both directions of every pair of distinct keys. -/
theorem sw32_swTable {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {a b : UInt64}
    (ha : a.toNat < 30) (hb : b.toNat < 30) (hab : a.toNat ≠ b.toNat) :
    (sw32 (swTable cnt) a b).toNat = cnt a.toNat b.toNat + cnt b.toNat a.toNat := by
  have hk : a.toNat * 30 + b.toNat < 900 := by omega
  have hdiv : (a.toNat * 30 + b.toNat) / 30 = a.toNat := by omega
  have hmod : (a.toNat * 30 + b.toNat) % 30 = b.toNat := by omega
  have hle := pair_le_totalWeight cnt ha hb hab
  unfold sw32 swTable
  rw [get32_tabulate32_const _ _ hk, hdiv, hmod]
  simp only [UInt32.toNat_toUInt64, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

/-- Adding a key to a piece adds both directions of its pairs with the piece's keys. -/
theorem pieceWeight_insert {α : Type} [DecidableEq α] (w : α → α → ℕ) {x : α} {A : Finset α}
    (hx : x ∉ A) : pieceWeight w (insert x A) = pieceWeight w A + ∑ y ∈ A, (w x y + w y x) := by
  have d1 : Disjoint A.offDiag ({x} ×ˢ A) := Finset.disjoint_left.mpr fun p hp hq => by
    rw [Finset.mem_offDiag] at hp
    rw [Finset.mem_product, Finset.mem_singleton] at hq
    exact hx (hq.1 ▸ hp.1)
  have d2 : Disjoint (A.offDiag ∪ {x} ×ˢ A) (A ×ˢ {x}) := Finset.disjoint_left.mpr fun p hp hq => by
    rw [Finset.mem_product, Finset.mem_singleton] at hq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hx (hq.2 ▸ (Finset.mem_offDiag.mp hp).2.1)
    · rw [Finset.mem_product, Finset.mem_singleton] at hp
      exact hx (hq.2 ▸ hp.2)
  rw [pieceWeight, Finset.offDiag_insert hx, Finset.sum_union d2, Finset.sum_union d1,
    Finset.sum_product, Finset.sum_product, Finset.sum_singleton, Finset.sum_add_distrib,
    Finset.sum_congr rfl fun y _ => Finset.sum_singleton (fun b => w y b) x]
  rw [pieceWeight, Nat.add_assoc]

theorem length_bitsDesc_le : ∀ (fuel : Nat) (r : UInt64), (bitsDesc fuel r).length ≤ fuel
  | 0, _ => Nat.le_refl 0
  | fuel + 1, r => by
    simp only [bitsDesc]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (length_bitsDesc_le fuel _)

/-- Summing `UInt64`s along a list matches the natural-number sum while it cannot overflow. -/
theorem toNat_foldl_add {α : Type} (g : α → UInt64) :
    ∀ (l : List α) (acc : UInt64), acc.toNat + (l.map fun y => (g y).toNat).sum < 2 ^ 64 →
      (l.foldl (fun acc y => acc + g y) acc).toNat = acc.toNat + (l.map fun y => (g y).toNat).sum
  | [], acc, _ => by simp
  | y :: l, acc, h => by
    simp only [List.map_cons, List.sum_cons] at h
    rw [List.foldl_cons, toNat_foldl_add g l (acc + g y) (by rw [UInt64.toNat_add]; omega),
      UInt64.toNat_add, List.map_cons, List.sum_cons]
    omega

theorem mem_bitsDesc_thirty {r : UInt64} (hr : r.toNat < 2 ^ 30) {b : UInt64}
    (hb : b ∈ bitsDesc 30 r) : b.toNat < 30 ∧ r.toNat.testBit b.toNat = true := by
  have hc : (decode r.toNat).card ≤ 30 := by
    simpa using Finset.card_le_univ (decode r.toNat)
  obtain ⟨i, hi, hv⟩ := ((bitsDesc_spec 30 r hr hc).2 b.toNat).mp (List.mem_map_of_mem hb)
  exact ⟨hv ▸ i.isLt, hv ▸ mem_decode.mp hi⟩

/-- A key's row sum over a mask is the sum over the decoded keys. -/
theorem rowSum_swTable {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {x A : UInt64}
    (hx : x.toNat < 30) (hA : A.toNat < 2 ^ 30) (hxA : A.toNat.testBit x.toNat = false) :
    (rowSum (swTable cnt) x A).toNat =
      ∑ i ∈ decode A.toNat, (cnt x.toNat i.val + cnt i.val x.toNat) := by
  have hc : (decode A.toNat).card ≤ 30 := by simpa using Finset.card_le_univ (decode A.toNat)
  have hterm : ∀ b ∈ bitsDesc 30 A, (sw32 (swTable cnt) x b).toNat =
      cnt x.toNat b.toNat + cnt b.toNat x.toNat := fun b hb => by
    obtain ⟨hb30, hbit⟩ := mem_bitsDesc_thirty hA hb
    exact sw32_swTable hbound hx hb30 fun h => by rw [h] at hxA; rw [hbit] at hxA; exact absurd hxA (by decide)
  have hmap : (bitsDesc 30 A).map (fun b => (sw32 (swTable cnt) x b).toNat) =
      (bitsDesc 30 A).map (fun b => (fun n => cnt x.toNat n + cnt n x.toNat) b.toNat) :=
    List.map_congr_left hterm
  have hsum := sum_bitsDesc (fun n => cnt x.toNat n + cnt n x.toNat) 30 A hA hc
  have hbnd : ((bitsDesc 30 A).map (fun b => (sw32 (swTable cnt) x b).toNat)).sum < 2 ^ 64 := by
    have hle : ∀ v ∈ (bitsDesc 30 A).map (fun b => (sw32 (swTable cnt) x b).toNat), v ≤ 2 ^ 32 :=
      fun v hv => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
        have := (get32 (swTable cnt) (x.toNat * 30 + b.toNat)).toNat_lt
        simp only [sw32, UInt32.toNat_toUInt64]
        omega
    have := List.sum_le_card_nsmul _ (2 ^ 32) hle
    rw [List.length_map, smul_eq_mul] at this
    have := length_bitsDesc_le 30 A
    have : (bitsDesc 30 A).length * 2 ^ 32 ≤ 30 * 2 ^ 32 := Nat.mul_le_mul_right _ this
    omega
  rw [rowSum, foldBits_eq_foldl, toNat_foldl_add _ _ 0 (by simpa using hbnd)]
  simp only [UInt64.reduceToNat, Nat.zero_add]
  rw [hmap, hsum]

end FernImpl
