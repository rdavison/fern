module
public import Fern.Solver.Proof.Fill

/-!
# Correctness of the index split

`splitMin` hands out the remaining keys highest first, each to block `A` or block `C` while that
block still has room, and keeps the cheapest result. It is the infimum over the ways to choose which
remaining keys join `A`. `indexCost` starts it with the highest index key already in `A`, which is
exactly `indexCostTop`.
-/

@[expose] public section

namespace FernImpl

open Finset Fern.Ortholinear Fern.Solver

/-! ### Setting a bit -/

theorem toNat_or_bit {A x : UInt64} (hx : x.toNat < 30) :
    (A ||| bit x).toNat = A.toNat ||| 2 ^ x.toNat := by
  rw [UInt64.toNat_or, toNat_bit x (by omega)]

theorem or_bit_lt {A x : UInt64} (hA : A.toNat < 2 ^ 30) (hx : x.toNat < 30) :
    (A ||| bit x).toNat < 2 ^ 30 := by
  rw [toNat_or_bit hx]
  exact Nat.or_lt_two_pow hA (Nat.pow_lt_pow_right (by decide) hx)

/-- Setting a bit adds exactly that key. -/
theorem decode_or_bit {A x : UInt64} (hx : x.toNat < 30) :
    decode (A ||| bit x).toNat = insert ⟨x.toNat, hx⟩ (decode A.toNat) := by
  ext i
  rw [toNat_or_bit hx, Finset.mem_insert, mem_decode, mem_decode, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : x.toNat = i.val
  · have hi : i = ⟨x.toNat, hx⟩ := Fin.ext h.symm
    subst hi
    simp
  · have hne : i ≠ ⟨x.toNat, hx⟩ := fun e => h (by rw [e])
    simp [h, hne]

theorem decode_bit {x : UInt64} (hx : x.toNat < 30) : decode (bit x).toNat = {⟨x.toNat, hx⟩} := by
  have h := decode_or_bit (A := 0) hx
  rw [show ((0 : UInt64) ||| bit x) = bit x from UInt64.zero_or, UInt64.toNat_zero, decode_zero] at h
  rw [h]
  rfl

/-! ### Weights of split blocks -/

theorem pieceWeight_add_le {α : Type} [DecidableEq α] (w : α → α → ℕ) {P Q : Finset α}
    (h : Disjoint P Q) : pieceWeight w P + pieceWeight w Q ≤ pieceWeight w (P ∪ Q) := by
  unfold pieceWeight
  rw [← Finset.sum_union (offDiag_disjoint h)]
  exact Finset.sum_le_sum_of_subset
    (Finset.union_subset (Finset.offDiag_mono Finset.subset_union_left)
      (Finset.offDiag_mono Finset.subset_union_right))

/-- The cost of sending keys `X` of `R` to block `A` and the rest of `R` to block `C`. -/
def splitCost (w : Fin 30 → Fin 30 → ℕ) (A C R X : Finset (Fin 30)) : ℕ :=
  pieceWeight w (A ∪ X) + pieceWeight w (C ∪ (R \ X))

theorem splitCost_le_totalWeight (cnt : Nat → Nat → Nat) {A C R X : Finset (Fin 30)}
    (hRA : Disjoint R A) (hRC : Disjoint R C) (hAC : Disjoint A C) (hX : X ⊆ R) :
    splitCost (fun a b => cnt a.val b.val) A C R X ≤ totalWeight cnt := by
  have hd : Disjoint (A ∪ X) (C ∪ (R \ X)) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨hAC, hRA.symm.mono_right Finset.sdiff_subset⟩,
      ⟨hRC.mono_left hX, Finset.disjoint_sdiff⟩⟩
  exact (pieceWeight_add_le _ hd).trans (pieceWeight_le_totalWeight cnt _)

/-- A value equal to a nonempty infimum of bounded values is bounded. -/
theorem toNat_le_of_eq_inf {ι : Type} {v : UInt64} {s : Finset ι} {f : ι → ℕ} {B : ℕ}
    (h : (v.toNat : WithTop ℕ) = s.inf fun x => (f x : WithTop ℕ)) (hs : s.Nonempty)
    (hB : ∀ x ∈ s, f x ≤ B) : v.toNat ≤ B := by
  obtain ⟨x, hx⟩ := hs
  have hle : s.inf (fun x => (f x : WithTop ℕ)) ≤ (f x : WithTop ℕ) :=
    Finset.inf_le (f := fun x => (f x : WithTop ℕ)) hx
  rw [← h] at hle
  exact (by exact_mod_cast hle : v.toNat ≤ f x).trans (hB x hx)

theorem toTop_ite_lt (x y : UInt64) :
    (((if x < y then x else y).toNat : ℕ) : WithTop ℕ) = min (x.toNat : WithTop ℕ) (y.toNat : WithTop ℕ) := by
  split
  · rename_i h
    rw [min_eq_left (by exact_mod_cast le_of_lt (UInt64.lt_iff_toNat_lt.mp h))]
  · rename_i h
    rw [min_eq_right (by exact_mod_cast (Nat.not_lt.mp fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')))]

theorem toNat_SENTINEL : SENTINEL.toNat = 2 ^ 62 := by decide

/-! ### The split recursion -/

section
attribute [local irreducible] hibTable popTable

/-- Adding a key to a block's running weight. -/
theorem add_rowSum_swTable {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {A wA x : UInt64}
    (hA : A.toNat < 2 ^ 30) (hx : x.toNat < 30) (hxA : (⟨x.toNat, hx⟩ : Fin 30) ∉ decode A.toNat)
    (hwA : wA.toNat = pieceWeight (fun a b => cnt a.val b.val) (decode A.toNat)) :
    (wA + rowSum (swTable cnt) x A).toNat =
      pieceWeight (fun a b => cnt a.val b.val) (decode (A ||| bit x).toNat) := by
  have htb : A.toNat.testBit x.toNat = false := by
    cases h : A.toNat.testBit x.toNat
    · rfl
    · exact absurd (mem_decode.mpr h) hxA
  rw [decode_or_bit hx, pieceWeight_insert _ hxA]
  have hle := pieceWeight_le_totalWeight cnt (insert ⟨x.toNat, hx⟩ (decode A.toNat))
  rw [pieceWeight_insert _ hxA] at hle
  dsimp only at hle ⊢
  rw [UInt64.toNat_add, hwA, rowSum_swTable hbound hx hA htb, Nat.mod_eq_of_lt (by omega)]

theorem splitMin_base {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32)
    {rest A wA C wC : UInt64} {nA nC : Nat} (hR : decode rest.toNat = ∅)
    (hcard : (decode rest.toNat).card = nA + nC)
    (hwA : wA.toNat = pieceWeight (fun a b => cnt a.val b.val) (decode A.toNat))
    (hwC : wC.toNat = pieceWeight (fun a b => cnt a.val b.val) (decode C.toNat)) :
    ((wA + wC).toNat : WithTop ℕ) =
      ((decode rest.toNat).powersetCard nA).inf fun X =>
        ((splitCost (fun a b => cnt a.val b.val) (decode A.toNat) (decode C.toNat)
          (decode rest.toNat) X : ℕ) : WithTop ℕ) := by
  rw [hR, Finset.card_empty] at *
  obtain rfl : nA = 0 := by omega
  have h1 := pieceWeight_le_totalWeight cnt (decode A.toNat)
  have h2 := pieceWeight_le_totalWeight cnt (decode C.toNat)
  rw [Finset.powersetCard_zero, Finset.inf_singleton, UInt64.toNat_add, hwA, hwC,
    Nat.mod_eq_of_lt (by omega)]
  simp [splitCost]

/-- The infimum over subsets of size `n + 1`, split by whether they contain `x`. -/
theorem inf_powersetCard_succ_erase {α : Type} [DecidableEq α] {R : Finset α} {x : α} (hx : x ∈ R)
    (n : ℕ) (F : Finset α → WithTop ℕ) :
    (R.powersetCard (n + 1)).inf F =
      min (((R.erase x).powersetCard (n + 1)).inf F)
        (((R.erase x).powersetCard n).inf fun X => F (insert x X)) := by
  conv_lhs => rw [← Finset.insert_erase hx]
  rw [Finset.powersetCard_succ_insert (Finset.notMem_erase x R), Finset.inf_union, Finset.inf_image]
  rfl

theorem splitCost_insert_left (w : Fin 30 → Fin 30 → ℕ) (A C R X : Finset (Fin 30)) (x : Fin 30) :
    splitCost w (insert x A) C (R.erase x) X = splitCost w A C R (insert x X) := by
  unfold splitCost
  rw [Finset.insert_union, ← Finset.union_insert, Finset.sdiff_insert, Finset.erase_sdiff_comm]

theorem splitCost_insert_right (w : Fin 30 → Fin 30 → ℕ) (A C R X : Finset (Fin 30)) {x : Fin 30}
    (hxR : x ∈ R) (hxX : x ∉ X) :
    splitCost w A (insert x C) (R.erase x) X = splitCost w A C R X := by
  unfold splitCost
  rw [Finset.insert_union, ← Finset.union_insert, Finset.erase_sdiff_comm,
    Finset.insert_erase (Finset.mem_sdiff.mpr ⟨hxR, hxX⟩)]

theorem splitMin_spec {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) :
    ∀ (fuel : Nat) (rest A wA : UInt64) (nA : Nat) (C wC : UInt64) (nC : Nat),
      rest.toNat < 2 ^ 30 → A.toNat < 2 ^ 30 → C.toNat < 2 ^ 30 →
      Disjoint (decode rest.toNat) (decode A.toNat) → Disjoint (decode rest.toNat) (decode C.toNat) →
      Disjoint (decode A.toNat) (decode C.toNat) →
      (decode rest.toNat).card = nA + nC → (decode rest.toNat).card ≤ fuel →
      wA.toNat = pieceWeight (fun a b => cnt a.val b.val) (decode A.toNat) →
      wC.toNat = pieceWeight (fun a b => cnt a.val b.val) (decode C.toNat) →
      ((splitMin (swTable cnt) fuel rest A wA nA C wC nC).toNat : WithTop ℕ) =
        ((decode rest.toNat).powersetCard nA).inf fun X =>
          ((splitCost (fun a b => cnt a.val b.val) (decode A.toNat) (decode C.toNat)
            (decode rest.toNat) X : ℕ) : WithTop ℕ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rest A wA nA C wC nC _ _ _ _ _ _ hcard hfuel hwA hwC
    rw [splitMin]
    exact splitMin_base hbound (Finset.card_eq_zero.mp (by omega)) hcard hwA hwC
  | succ fuel ih =>
    intro rest A wA nA C wC nC hr hA hC hRA hRC hAC hcard hfuel hwA hwC
    by_cases h0 : rest = 0
    · have hbeq : (rest == 0) = true := by simp [h0]
      rw [splitMin, if_pos hbeq]
      exact splitMin_base hbound (by rw [h0]; exact decode_zero) hcard hwA hwC
    have hbeq : (rest == 0) = false := by simpa using h0
    have h0' : rest.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    set w : Fin 30 → Fin 30 → ℕ := fun a b => cnt a.val b.val with hw
    set R := decode rest.toNat with hRdef
    set sw := swTable cnt with hsw
    have hx30 : (hibit rest).toNat < 30 := by rw [hibit_eq rest hr]; exact log2_lt_thirty hr
    set xF : Fin 30 := ⟨(hibit rest).toNat, hx30⟩ with hxF
    have hxeq : xF = ⟨Nat.log2 rest.toNat, log2_lt_thirty hr⟩ := Fin.ext (hibit_eq rest hr)
    have hxR : xF ∈ R := hxeq ▸ log2_mem_decode rest hr h0'
    have hR' : decode (rest ^^^ bit (hibit rest)).toNat = R.erase xF := by
      rw [decode_clearHigh rest hr h0', hxeq]
    have hr' := clearHigh_lt rest hr
    have hxA : xF ∉ decode A.toNat := Finset.disjoint_left.mp hRA hxR
    have hxC : xF ∉ decode C.toNat := Finset.disjoint_left.mp hRC hxR
    have hcardE : (R.erase xF).card + 1 = R.card := Finset.card_erase_add_one hxR
    have hEA : Disjoint (R.erase xF) (decode A.toNat) := hRA.mono_left (Finset.erase_subset _ _)
    have hEC : Disjoint (R.erase xF) (decode C.toNat) := hRC.mono_left (Finset.erase_subset _ _)
    have hEA' : Disjoint (R.erase xF) (insert xF (decode A.toNat)) :=
      Finset.disjoint_insert_right.mpr ⟨Finset.notMem_erase xF R, hEA⟩
    have hEC' : Disjoint (R.erase xF) (insert xF (decode C.toNat)) :=
      Finset.disjoint_insert_right.mpr ⟨Finset.notMem_erase xF R, hEC⟩
    have hAC' : Disjoint (insert xF (decode A.toNat)) (decode C.toNat) :=
      Finset.disjoint_insert_left.mpr ⟨hxC, hAC⟩
    have hCA' : Disjoint (decode A.toNat) (insert xF (decode C.toNat)) :=
      Finset.disjoint_insert_right.mpr ⟨hxA, hAC⟩
    -- Sending the highest key to `A`.
    have viaA : ∀ nA', nA = nA' + 1 →
        ((splitMin sw fuel (rest ^^^ bit (hibit rest)) (A ||| bit (hibit rest))
            (wA + rowSum sw (hibit rest) A) nA' C wC nC).toNat : WithTop ℕ) =
          ((R.erase xF).powersetCard nA').inf (fun X => ((splitCost w (decode A.toNat)
            (decode C.toNat) R (insert xF X) : ℕ) : WithTop ℕ)) ∧
        (splitMin sw fuel (rest ^^^ bit (hibit rest)) (A ||| bit (hibit rest))
            (wA + rowSum sw (hibit rest) A) nA' C wC nC).toNat ≤ totalWeight cnt := by
      intro nA' hnA
      have h := ih _ _ _ nA' _ _ nC hr' (or_bit_lt hA hx30) hC
        (by rw [hR', decode_or_bit hx30]; exact hEA') (by rw [hR']; exact hEC)
        (by rw [decode_or_bit hx30]; exact hAC') (by rw [hR']; omega) (by rw [hR']; omega)
        (add_rowSum_swTable hbound hA hx30 hxA hwA) hwC
      rw [hR', decode_or_bit hx30] at h
      refine ⟨h.trans (Finset.inf_congr rfl fun X _ => by rw [splitCost_insert_left]), ?_⟩
      exact toNat_le_of_eq_inf h (Finset.powersetCard_nonempty.mpr (by omega)) fun X hX =>
        splitCost_le_totalWeight cnt hEA' hEC hAC' (Finset.mem_powersetCard.mp hX).1
    -- Sending the highest key to `C`.
    have viaC : ∀ nC', nC = nC' + 1 →
        ((splitMin sw fuel (rest ^^^ bit (hibit rest)) A wA nA (C ||| bit (hibit rest))
            (wC + rowSum sw (hibit rest) C) nC').toNat : WithTop ℕ) =
          ((R.erase xF).powersetCard nA).inf (fun X => ((splitCost w (decode A.toNat)
            (decode C.toNat) R X : ℕ) : WithTop ℕ)) ∧
        (splitMin sw fuel (rest ^^^ bit (hibit rest)) A wA nA (C ||| bit (hibit rest))
            (wC + rowSum sw (hibit rest) C) nC').toNat ≤ totalWeight cnt := by
      intro nC' hnC
      have h := ih _ _ _ nA _ _ nC' hr' hA (or_bit_lt hC hx30)
        (by rw [hR']; exact hEA) (by rw [hR', decode_or_bit hx30]; exact hEC')
        (by rw [decode_or_bit hx30]; exact hCA') (by rw [hR']; omega) (by rw [hR']; omega)
        hwA (add_rowSum_swTable hbound hC hx30 hxC hwC)
      rw [hR', decode_or_bit hx30] at h
      refine ⟨h.trans (Finset.inf_congr rfl fun X hX => by
        rw [splitCost_insert_right _ _ _ _ _ hxR fun hx =>
          Finset.notMem_erase xF R ((Finset.mem_powersetCard.mp hX).1 hx)]), ?_⟩
      exact toNat_le_of_eq_inf h (Finset.powersetCard_nonempty.mpr (by omega)) fun X hX =>
        splitCost_le_totalWeight cnt hEA hEC' hCA' (Finset.mem_powersetCard.mp hX).1
    have hsent : totalWeight cnt < SENTINEL.toNat := by rw [toNat_SENTINEL]; omega
    rcases nA with _ | nA' <;> rcases nC with _ | nC'
    · have := Finset.card_pos.mpr ⟨xF, hxR⟩
      omega
    · obtain ⟨hv, hb⟩ := viaC nC' rfl
      simp only [splitMin, hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [toTop_ite_lt, min_eq_right (by exact_mod_cast (hb.trans hsent.le)), hv,
        Finset.powersetCard_zero, Finset.powersetCard_zero]
    · obtain ⟨hv, hb⟩ := viaA nA' rfl
      simp only [splitMin, hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [toTop_ite_lt, min_eq_left (by exact_mod_cast (hb.trans hsent.le)), hv,
        inf_powersetCard_succ_erase hxR, Finset.powersetCard_eq_empty.mpr (show (R.erase xF).card < nA' + 1 by omega), Finset.inf_empty,
        min_eq_right le_top]
    · obtain ⟨hvA, -⟩ := viaA nA' rfl
      obtain ⟨hvC, -⟩ := viaC nC' rfl
      simp only [splitMin, hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [toTop_ite_lt, hvA, hvC, inf_powersetCard_succ_erase hxR, min_comm]

/-- The index split computes the cheapest split of twelve keys into two blocks of six. -/
theorem indexCost_spec {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {S : UInt64}
    (hS : S.toNat < 2 ^ 30) (h12 : (decode S.toNat).card = 12) :
    ((indexCost (swTable cnt) S).toNat : WithTop ℕ) =
      indexCostTop (fun a b => cnt a.val b.val) (decode S.toNat) := by
  have hne : (decode S.toNat).Nonempty := Finset.card_pos.mp (by omega)
  have h0 := decode_nonempty_iff hne
  have hx30 : (hibit S).toNat < 30 := by rw [hibit_eq S hS]; exact log2_lt_thirty hS
  have hxeq : (⟨(hibit S).toNat, hx30⟩ : Fin 30) = ⟨Nat.log2 S.toNat, log2_lt_thirty hS⟩ :=
    Fin.ext (hibit_eq S hS)
  have hxS : (⟨(hibit S).toNat, hx30⟩ : Fin 30) ∈ decode S.toNat := hxeq ▸ log2_mem_decode S hS h0
  have hR : decode (S ^^^ bit (hibit S)).toNat = (decode S.toNat).erase ⟨(hibit S).toNat, hx30⟩ := by
    rw [decode_clearHigh S hS h0, hxeq]
  have hcardR : ((decode S.toNat).erase ⟨(hibit S).toNat, hx30⟩).card = 11 := by
    rw [Finset.card_erase_of_mem hxS, h12]
  have hbitlt : (bit (hibit S)).toNat < 2 ^ 30 := by
    rw [toNat_bit _ (by omega)]
    exact Nat.pow_lt_pow_right (by decide) hx30
  have hz : decode (0 : UInt64).toNat = ∅ := decode_zero
  unfold indexCost
  rw [splitMin_spec hbound 11 _ _ 0 5 0 0 6 (clearHigh_lt S hS) hbitlt (by decide)
    (by rw [hR, decode_bit hx30]; exact Finset.disjoint_singleton_right.mpr (Finset.notMem_erase _ _))
    (by rw [hz]; exact Finset.disjoint_empty_right _) (by rw [hz]; exact Finset.disjoint_empty_right _)
    (by rw [hR, hcardR]) (by rw [hR, hcardR]) (by rw [decode_bit hx30]; simp [pieceWeight])
    (by rw [hz]; simp [pieceWeight])]
  unfold indexCostTop
  rw [dif_pos hne, max'_decode hS hne, ← hxeq, hR, decode_bit hx30, hz]
  refine Finset.inf_congr rfl fun X _ => ?_
  unfold splitCost
  rw [← Finset.insert_eq, Finset.empty_union, Finset.sdiff_insert, Finset.erase_sdiff_comm]

end

end FernImpl
