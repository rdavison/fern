module
public import Fern.Solver.Proof.Split

/-!
# Correctness of the scan

`scanRange` visits consecutive masks and keeps the cheapest total over those holding twelve keys:
the index split of the mask plus one `step` on its eighteen-key complement, which reads the filled
table. `solveValue` covers all `2 ^ 30` masks in 1024 chunks, so it computes the infimum over every
mask, and through `decode` that is the infimum over every twelve-key set, `optimumTop`.
-/

@[expose] public section

namespace FernImpl

open Finset Fern.Ortholinear Fern.Solver

variable {cnt : Nat → Nat → Nat}

/-- What a mask contributes to the search: its total when it holds twelve keys, otherwise nothing. -/
noncomputable def maskCost (w : Fin 30 → Fin 30 → ℕ) (S : Finset (Fin 30)) : WithTop ℕ :=
  if S.card = 12 then indexCostTop w S + bestTriplesTop w 6 (univ \ S) else ⊤

/-! ### The complement of the index keys -/

theorem toNat_FULL : FULL.toNat = 2 ^ 30 - 1 := by decide

theorem compl_lt {m : UInt64} (hm : m.toNat < 2 ^ 30) : (FULL ^^^ m).toNat < 2 ^ 30 := by
  rw [UInt64.toNat_xor, toNat_FULL]
  exact Nat.xor_lt_two_pow (by decide) hm

theorem decode_compl {m : UInt64} : decode (FULL ^^^ m).toNat = univ \ decode m.toNat := by
  ext i
  rw [UInt64.toNat_xor, toNat_FULL, Finset.mem_sdiff, mem_decode, mem_decode, Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one]
  simp [i.isLt]

section
attribute [local irreducible] hibTable popTable

theorem pop30_beq_iff {m : UInt64} (hm : m.toNat < 2 ^ 30) :
    (pop30 m == 12) = true ↔ (decode m.toNat).card = 12 := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, pop30_eq m hm]
  rfl

/-- One mask's total: the index split plus the best triples on the complement. -/
theorem maskValue_spec (hbound : totalWeight cnt < 2 ^ 32) {m : UInt64} (hm : m.toNat < 2 ^ 30)
    (h12 : (decode m.toNat).card = 12) :
    ((indexCost (swTable cnt) m + step (swTable cnt) (fill (swTable cnt)) (FULL ^^^ m)).toNat :
        WithTop ℕ) = maskCost (fun a b => cnt a.val b.val) (decode m.toNat) ∧
      (indexCost (swTable cnt) m + step (swTable cnt) (fill (swTable cnt)) (FULL ^^^ m)).toNat <
        2 ^ 33 := by
  set w : Fin 30 → Fin 30 → ℕ := fun a b => cnt a.val b.val with hw
  have h18 : (univ \ decode m.toNat).card = 18 := card_compl_of_card_twelve h12
  -- The index split.
  have hI := indexCost_spec hbound hm h12
  obtain ⟨A, B, hAB, hc⟩ := indexCostTop_achieved h12 hI.symm
  have hIle : (indexCost (swTable cnt) m).toNat ≤ totalWeight cnt := by
    rw [← hc]
    exact (pieceWeight_add_le _ hAB.disjoint).trans (pieceWeight_le_totalWeight cnt _)
  -- The triples on the complement.
  have hS := step_spec hbound (t := fill (swTable cnt)) (m := FULL ^^^ m) (compl_lt hm)
    (by rw [decode_compl]; exact Finset.card_pos.mp (by omega)) (by rw [decode_compl, h18]; decide)
    (fun m' hm' _ hc' => by
      rw [decode_compl, h18] at hc'
      exact fill_spec hbound hm' (by omega) (by omega))
  rw [decode_compl] at hS
  have hSle : (step (swTable cnt) (fill (swTable cnt)) (FULL ^^^ m)).toNat ≤ totalWeight cnt := by
    rw [hS]
    exact (bestTriplesRef_le_pieceWeight (by rw [h18]; decide)).trans (pieceWeight_le_totalWeight cnt _)
  have hsum : (indexCost (swTable cnt) m + step (swTable cnt) (fill (swTable cnt)) (FULL ^^^ m)).toNat =
      (indexCost (swTable cnt) m).toNat + (step (swTable cnt) (fill (swTable cnt)) (FULL ^^^ m)).toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, by omega⟩
  rw [maskCost, if_pos h12, hsum, Nat.cast_add, hI, hS,
    bestTriplesTop_eq_ref (by rw [h18]) (by rw [h18]; decide)]

end

/-! ### Scanning a range of masks -/

theorem withTop_inf_eq_min (a b : WithTop ℕ) : a ⊓ b = min a b := rfl

theorem scanRange_spec (hbound : totalWeight cnt < 2 ^ 32) :
    ∀ (fuel : Nat) (m best : UInt64), m.toNat + fuel ≤ 2 ^ 30 →
      ((scanRange (swTable cnt) (fill (swTable cnt)) fuel m best).toNat : WithTop ℕ) =
        min (best.toNat : WithTop ℕ)
          ((Finset.Ico m.toNat (m.toNat + fuel)).inf fun k =>
            maskCost (fun a b => cnt a.val b.val) (decode k)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m best _
    simp [scanRange, scanWith]
  | succ fuel ih =>
    intro m best hle
    have hm : m.toNat < 2 ^ 30 := by omega
    have hm1 : (m + 1).toNat = m.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]
      omega
    rw [scanRange, scanWith, ← scanRange, ih _ _ (by rw [hm1]; omega), hm1, show m.toNat + 1 + fuel = m.toNat + (fuel + 1) by omega,
      ← Finset.insert_Ico_add_one_left_eq_Ico (show m.toNat < m.toNat + (fuel + 1) by omega),
      Finset.inf_insert, withTop_inf_eq_min]
    by_cases h12 : (decode m.toNat).card = 12
    · rw [scanStep, if_pos ((pop30_beq_iff hm).mpr h12), toTop_ite_lt, (maskValue_spec hbound hm h12).1,
        min_comm _ (best.toNat : WithTop ℕ), min_assoc]
    · have hb : (pop30 m == 12) = false := by
        cases h : (pop30 m == 12)
        · rfl
        · exact absurd ((pop30_beq_iff hm).mp h) h12
      rw [scanStep, if_neg (by rw [hb]; decide), maskCost, if_neg h12, min_eq_right le_top]

/-! ### All masks, in parallel chunks -/

theorem inf_min_const {ι : Type} {s : Finset ι} (hs : s.Nonempty) (a : WithTop ℕ) (f : ι → WithTop ℕ) :
    (s.inf fun i => min a (f i)) = min a (s.inf f) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hs
    exact le_min ((Finset.inf_le (f := fun i => min a (f i)) hi).trans (min_le_left _ _))
      (Finset.le_inf fun j hj => (Finset.inf_le (f := fun i => min a (f i)) hj).trans (min_le_right _ _))
  · exact Finset.le_inf fun i hi => min_le_min le_rfl (Finset.inf_le hi)

theorem biUnion_chunks :
    (Finset.range 1024).biUnion (fun c => Finset.Ico (c * 2 ^ 20) (c * 2 ^ 20 + 2 ^ 20)) =
      Finset.range (2 ^ 30) := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨c, hc, -, h2⟩
    omega
  · intro hk
    exact ⟨k / 2 ^ 20, by omega, by omega, by omega⟩

theorem toFinset_listRange (n : Nat) : (List.range n).toFinset = Finset.range n := by
  ext c
  simp

/-- Waiting on each spawned task is running it: `Task.get (Task.spawn f) = f ()` by definition. Stated
for any list, since unfolding against the concrete chunk list would evaluate it. -/
theorem foldl_spawn_eq (l : List Nat) (F : Nat → UInt64) :
    (l.map fun c => Task.spawn fun _ => F c).foldl
        (fun acc tk => let v := tk.get; if v < acc then v else acc) SENTINEL =
      l.foldl (fun acc c => if F c < acc then F c else acc) SENTINEL := by
  rw [List.foldl_map]
  rfl

theorem solveValue_eq_foldl (sw t : ByteArray) :
    solveValue sw t = (List.range 1024).foldl (fun acc c =>
      if scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL < acc
      then scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL else acc) SENTINEL := by
  unfold solveValue
  rw [foldl_spawn_eq]

theorem foldl_chunks_toTop (sw t : ByteArray) (l : List Nat) :
    ((l.foldl (fun acc c =>
        if scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL < acc
        then scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL else acc) SENTINEL).toNat :
          WithTop ℕ) =
      min (SENTINEL.toNat : WithTop ℕ) (l.toFinset.inf fun c =>
        ((scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL).toNat : WithTop ℕ)) := by
  rw [foldl_min_toTop]

theorem inf_toFinset_listRange (n : Nat) (F : Nat → WithTop ℕ) :
    (List.range n).toFinset.inf F = (Finset.range n).inf F := by
  rw [toFinset_listRange]

/-- The parallel scan is the minimum over its chunks.

The kernel checks this slowly (minutes) when `foldl_min_toTop` is rewritten at the concrete chunk
list, but quickly when it is composed from lemmas stated for an arbitrary list, as here. -/
theorem solveValue_toTop (sw t : ByteArray) :
    ((solveValue sw t).toNat : WithTop ℕ) =
      min (SENTINEL.toNat : WithTop ℕ) ((Finset.range 1024).inf fun c =>
        ((scanRange sw t (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL).toNat : WithTop ℕ)) := by
  rw [solveValue_eq_foldl, foldl_chunks_toTop, inf_toFinset_listRange]

/-- Combining chunk minimums, each already including the start value `a`.

The chunk size `B` is a parameter on purpose: with the literal `2 ^ 20` inside the chunk-bounds
lambda, the kernel unfolds the offset `c * 2 ^ 20 + 2 ^ 20` into successors and overflows its
stack. -/
theorem inf_chunks {n B : ℕ} (hs : (Finset.range n).Nonempty) (a : WithTop ℕ) (g F : ℕ → WithTop ℕ)
    (hF : ∀ c ∈ Finset.range n, F c = min a ((Finset.Ico (c * B) (c * B + B)).inf g)) :
    min a ((Finset.range n).inf F) =
      min a (((Finset.range n).biUnion fun c => Finset.Ico (c * B) (c * B + B)).inf g) := by
  rw [Finset.inf_congr rfl hF, inf_min_const hs, ← min_assoc, min_self, Finset.inf_biUnion]

/-- The parallel scan is the cheapest total over every mask. -/
theorem solveValue_spec (hbound : totalWeight cnt < 2 ^ 32) :
    ((solveValue (swTable cnt) (fill (swTable cnt))).toNat : WithTop ℕ) =
      min (SENTINEL.toNat : WithTop ℕ)
        ((Finset.range (2 ^ 30)).inf fun k => maskCost (fun a b => cnt a.val b.val) (decode k)) := by
  have hchunk : ∀ c ∈ Finset.range 1024,
      ((scanRange (swTable cnt) (fill (swTable cnt)) (2 ^ 20) (c * 2 ^ 20).toUInt64 SENTINEL).toNat :
          WithTop ℕ) =
        min (SENTINEL.toNat : WithTop ℕ) ((Finset.Ico (c * 2 ^ 20) (c * 2 ^ 20 + 2 ^ 20)).inf fun k =>
          maskCost (fun a b => cnt a.val b.val) (decode k)) := by
    intro c hc
    have hc' := Finset.mem_range.mp hc
    have h1 : (c * 2 ^ 20).toUInt64.toNat = c * 2 ^ 20 := toNat_natToUInt64 (by omega)
    rw [scanRange_spec hbound _ _ _ (by rw [h1]; omega), h1]
  have hne : (Finset.range 1024).Nonempty := ⟨0, Finset.mem_range.mpr (by decide)⟩
  rw [solveValue_toTop, inf_chunks hne _ _ _ hchunk, biUnion_chunks]

/-! ### From masks to key sets -/

theorem image_decode_range : (Finset.range (2 ^ 30)).image decode = univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn fun a ha b hb h =>
      decode_injOn (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h,
    Finset.card_range, Fintype.card_finset, Fintype.card_fin]

theorem filter_card_twelve :
    (univ : Finset (Finset (Fin 30))).filter (fun S => S.card = 12) = univ.powersetCard 12 := by
  ext S
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨Finset.subset_univ _, h.2⟩, fun h => ⟨Finset.mem_univ _, h.2⟩⟩

/-- Stated for any `U` that filters to the twelve-key sets: rewriting against the concrete set of
all key sets makes the kernel evaluate it. -/
theorem inf_maskCost_of (w : Fin 30 → Fin 30 → ℕ) {U : Finset (Finset (Fin 30))}
    (hU : U.filter (fun S => S.card = 12) = univ.powersetCard 12) :
    U.inf (maskCost w) = optimumTop w := by
  unfold maskCost optimumTop
  rw [Finset.inf_ite, Finset.inf_top, inf_top_eq, hU]

/-- Every key set is some mask, so the infimum over masks is the reference search. -/
theorem inf_maskCost (w : Fin 30 → Fin 30 → ℕ) :
    ((Finset.range (2 ^ 30)).inf fun k => maskCost w (decode k)) = optimumTop w := by
  rw [← inf_maskCost_of w filter_card_twelve, ← image_decode_range, Finset.inf_image]
  rfl

theorem optimumRef_lt (hbound : totalWeight cnt < 2 ^ 32) :
    optimumRef (fun a b => cnt a.val b.val) < 2 ^ 33 := by
  obtain ⟨S0, hS0⟩ := Finset.powersetCard_nonempty.mpr
    (by simp : 12 ≤ (univ : Finset (Fin 30)).card)
  have hS0u : S0 ∈ (Finset.range (2 ^ 30)).image decode := by
    rw [image_decode_range]
    exact Finset.mem_univ _
  obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.mp hS0u
  have hk0' := Finset.mem_range.mp hk0
  have hm := toNat_natToUInt64 hk0'
  have h12 : (decode k0).card = 12 := (Finset.mem_powersetCard.mp hS0).2
  obtain ⟨hv, hlt⟩ := maskValue_spec hbound (m := k0.toUInt64) (by rw [hm]; exact hk0')
    (by rw [hm]; exact h12)
  rw [hm] at hv
  have hle : optimumTop (fun a b => cnt a.val b.val) ≤ maskCost (fun a b => cnt a.val b.val) (decode k0) := by
    rw [← inf_maskCost]
    exact Finset.inf_le (f := fun k => maskCost (fun a b => cnt a.val b.val) (decode k)) hk0
  rw [← hv, optimumTop_eq_ref] at hle
  exact lt_of_le_of_lt (by exact_mod_cast hle) hlt

end FernImpl
