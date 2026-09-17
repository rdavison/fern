module
public import Fern.Solver.Proof.Weights

/-!
# Correctness of one dynamic-programming step

`step` places the highest key of a mask with each possible pair and keeps the cheapest total. Given a
table that is correct on the smaller key sets it reads, it computes `bestTriplesRef` exactly.
-/

@[expose] public section

namespace FernImpl

open Finset Fern.Ortholinear Fern.Solver

/-! ### Minimum folds -/

/-- A `UInt64` running minimum is the infimum of the values it saw, together with its start. -/
theorem foldl_min_toTop {α : Type} [DecidableEq α] (f : α → UInt64) :
    ∀ (l : List α) (init : UInt64),
      ((l.foldl (fun acc x => if f x < acc then f x else acc) init).toNat : WithTop ℕ) =
        min (init.toNat : WithTop ℕ) (l.toFinset.inf fun x => ((f x).toNat : WithTop ℕ))
  | [], init => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_min_toTop f l, List.toFinset_cons, Finset.inf_insert]
    have hstep : (((if f x < init then f x else init).toNat : ℕ) : WithTop ℕ) =
        min (init.toNat : WithTop ℕ) ((f x).toNat : WithTop ℕ) := by
      split
      · rename_i h
        rw [min_eq_right (by exact_mod_cast le_of_lt (UInt64.lt_iff_toNat_lt.mp h))]
      · rename_i h
        rw [min_eq_left (by exact_mod_cast (Nat.not_lt.mp fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')))]
    rw [hstep, min_assoc]

/-- Two nested running minimums are the infimum over pairs. -/
theorem foldl_nested_min_toTop {α β : Type} [DecidableEq α] [DecidableEq β] (M : α → List β)
    (f : α → β → UInt64) :
    ∀ (L : List α) (init : UInt64),
      ((L.foldl (fun acc b => (M b).foldl (fun acc c => if f b c < acc then f b c else acc) acc)
          init).toNat : WithTop ℕ) =
        min (init.toNat : WithTop ℕ)
          (L.toFinset.inf fun b => (M b).toFinset.inf fun c => ((f b c).toNat : WithTop ℕ))
  | [], init => by simp
  | b :: L, init => by
    rw [List.foldl_cons, foldl_nested_min_toTop M f L, foldl_min_toTop (f b), List.toFinset_cons,
      Finset.inf_insert, min_assoc]

/-- The infimum over two-element subsets, enumerated as a larger element with a smaller one. -/
theorem inf_powersetCard_two {α : Type} [LinearOrder α] (s : Finset α) (F : Finset α → WithTop ℕ) :
    (s.powersetCard 2).inf F = s.inf fun i => (s.filter (· < i)).inf fun j => F {i, j} := by
  apply le_antisymm
  · refine Finset.le_inf fun i hi => Finset.le_inf fun j hj => Finset.inf_le ?_
    obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hjs), ?_⟩
    rw [Finset.card_pair (ne_of_gt hji)]
  · refine Finset.le_inf fun p hp => ?_
    obtain ⟨hps, hp2⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp2
    have hx : x ∈ s := hps (Finset.mem_insert_self x {y})
    have hy : y ∈ s := hps (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · rw [Finset.pair_comm]
      exact (Finset.inf_le hy).trans (Finset.inf_le (Finset.mem_filter.mpr ⟨hx, hlt⟩))
    · exact (Finset.inf_le hx).trans (Finset.inf_le (Finset.mem_filter.mpr ⟨hy, hgt⟩))

/-! ### Decoding the bit manipulation -/

theorem toNat_xor_bit {r b : UInt64} (hb : b.toNat < 30) :
    (r ^^^ bit b).toNat = r.toNat ^^^ 2 ^ b.toNat := by
  rw [UInt64.toNat_xor, toNat_bit b (by omega)]

theorem xor_bit_lt {r b : UInt64} (hr : r.toNat < 2 ^ 30) (hb : b.toNat < 30) :
    (r ^^^ bit b).toNat < 2 ^ 30 := by
  rw [toNat_xor_bit hb]
  exact Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by decide) hb)

/-- Clearing a set bit removes exactly that key. -/
theorem decode_xor_bit {r b : UInt64} (hb : b.toNat < 30) (hbit : r.toNat.testBit b.toNat = true) :
    decode (r ^^^ bit b).toNat = (decode r.toNat).erase ⟨b.toNat, hb⟩ := by
  ext i
  rw [toNat_xor_bit hb, Finset.mem_erase, mem_decode, mem_decode, Nat.testBit_xor,
    Nat.testBit_two_pow]
  by_cases h : b.toNat = i.val
  · have hi : i = ⟨b.toNat, hb⟩ := Fin.ext h.symm
    subst hi
    simp [hbit]
  · have hne : i ≠ ⟨b.toNat, hb⟩ := fun e => h (by rw [e])
    simp [h, hne]

theorem toNat_bit_sub_one {b : UInt64} (hb : b.toNat < 30) : (bit b - 1).toNat = 2 ^ b.toNat - 1 := by
  have h1 := toNat_bit b (by omega)
  have hle : (1 : UInt64) ≤ bit b := by
    rw [UInt64.le_iff_toNat_le, h1]
    exact Nat.one_le_two_pow
  rw [UInt64.toNat_sub_of_le _ _ hle, h1]
  rfl

/-- Masking below a key keeps exactly the smaller keys. -/
theorem decode_and_below {r b : UInt64} (hb : b.toNat < 30) :
    decode (r &&& (bit b - 1)).toNat = (decode r.toNat).filter fun j => j.val < b.toNat := by
  ext i
  rw [UInt64.toNat_and, toNat_bit_sub_one hb, Finset.mem_filter, mem_decode, mem_decode,
    Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  simp

theorem and_below_lt {r b : UInt64} (hr : r.toNat < 2 ^ 30) : (r &&& (bit b - 1)).toNat < 2 ^ 30 := by
  rw [UInt64.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_left hr

theorem decode_nonempty_iff {m : Nat} : (decode m).Nonempty → m ≠ 0 := by
  rintro ⟨i, hi⟩ rfl
  rw [decode_zero] at hi
  exact absurd hi (Finset.notMem_empty i)

/-- The largest key of a mask is its highest set bit. -/
theorem max'_decode {m : UInt64} (hm : m.toNat < 2 ^ 30) (h : (decode m.toNat).Nonempty) :
    (decode m.toNat).max' h = ⟨Nat.log2 m.toNat, log2_lt_thirty hm⟩ := by
  have h0 := decode_nonempty_iff h
  apply le_antisymm
  · refine Finset.max'_le _ _ _ fun j hj => Fin.le_iff_val_le_val.mpr ?_
    rw [mem_decode] at hj
    show j.val ≤ Nat.log2 m.toNat
    by_contra hlt
    have hlt' : m.toNat < 2 ^ j.val :=
      lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hlt'] at hj
    exact absurd hj (by decide)
  · exact Finset.le_max' _ _ (log2_mem_decode m hm h0)

/-! ### Bounds -/

theorem pieceWeight_le_totalWeight (cnt : Nat → Nat → Nat) (T : Finset (Fin 30)) :
    pieceWeight (fun a b : Fin 30 => cnt a.val b.val) T ≤ totalWeight cnt := by
  rw [pieceWeight, totalWeight_eq]
  have hinj : Set.InjOn (fun p : Fin 30 × Fin 30 => (p.1.val, p.2.val)) T.offDiag :=
    fun p _ q _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  calc ∑ p ∈ T.offDiag, cnt p.1.val p.2.val
      = ∑ q ∈ T.offDiag.image (fun p : Fin 30 × Fin 30 => (p.1.val, p.2.val)), cnt q.1 q.2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ q ∈ range 30 ×ˢ range 30, cnt q.1 q.2 := Finset.sum_le_sum_of_subset fun q hq => by
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
        simp [p.1.isLt, p.2.isLt]

theorem pieceCost_le_pieceWeight {T : Finset (Fin 30)} {Q : Finset (Finset (Fin 30))}
    (hQ : IsTriplePartition T Q) (w : Fin 30 → Fin 30 → ℕ) : pieceCost w Q ≤ pieceWeight w T := by
  have hdisj : (Q : Set (Finset (Fin 30))).PairwiseDisjoint Finset.offDiag :=
    fun p hp q hq hpq => offDiag_disjoint (hQ.disjoint hp hq hpq)
  have hsum : pieceCost w Q = ∑ x ∈ Q.biUnion Finset.offDiag, w x.1 x.2 := by
    rw [Finset.sum_biUnion hdisj]
    rfl
  rw [hsum, pieceWeight]
  exact Finset.sum_le_sum_of_subset
    (Finset.biUnion_subset.mpr fun q hq => Finset.offDiag_mono (hQ.subset hq))

theorem bestTriplesRef_le_pieceWeight {w : Fin 30 → Fin 30 → ℕ} {T : Finset (Fin 30)}
    (h3 : 3 ∣ T.card) : bestTriplesRef w T ≤ pieceWeight w T := by
  obtain ⟨Q, hQ, hc⟩ := (bestTriplesRef_isLeast (w := w) h3).1
  rw [← hc]
  exact pieceCost_le_pieceWeight hQ w

/-! ### The visited bits as keys -/

theorem toNat_finToUInt64 (i : Fin 30) : ((i.val : Nat).toUInt64).toNat = i.val := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans i.isLt (by decide))

/-- The bits `foldBits` visits, as a set, are the decoded keys. -/
theorem toFinset_bitsDesc {r : UInt64} (hr : r.toNat < 2 ^ 30) :
    (bitsDesc 30 r).toFinset = (decode r.toNat).image fun i : Fin 30 => (i.val : Nat).toUInt64 := by
  have hc : (decode r.toNat).card ≤ 30 := by simpa using Finset.card_le_univ (decode r.toNat)
  have hmem := (bitsDesc_spec 30 r hr hc).2
  ext b
  rw [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hb
    obtain ⟨i, hi, hv⟩ := (hmem b.toNat).mp (List.mem_map_of_mem hb)
    exact ⟨i, hi, by rw [hv, Nat.toUInt64_eq, UInt64.ofNat_toNat]⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp ((hmem i.val).mpr ⟨i, hi, rfl⟩)
    have hbeq : b = (i.val : Nat).toUInt64 := by rw [← hbv, Nat.toUInt64_eq, UInt64.ofNat_toNat]
    exact hbeq ▸ hb

/-- The weight of a triple is its three pairs, both directions each. -/
theorem pieceWeight_triple {α : Type} [DecidableEq α] (w : α → α → ℕ) {a i j : α} (hai : a ≠ i)
    (haj : a ≠ j) (hij : i ≠ j) :
    pieceWeight w (insert a (insert i ({j} : Finset α))) =
      (w a i + w i a) + (w a j + w j a) + (w i j + w j i) := by
  have ha : a ∉ insert i ({j} : Finset α) := by simp [hai, haj]
  have hi : i ∉ ({j} : Finset α) := by simp [hij]
  rw [pieceWeight_insert w ha, pieceWeight_insert w hi, Finset.sum_insert hi, Finset.sum_singleton,
    Finset.sum_singleton]
  have hj : pieceWeight w ({j} : Finset α) = 0 := by simp [pieceWeight]
  rw [hj]
  omega

/-! ### The step -/

theorem sw32_lt (sw : ByteArray) (a b : UInt64) : (sw32 sw a b).toNat < 2 ^ 32 := by
  unfold sw32
  rw [UInt32.toNat_toUInt64]
  exact UInt32.toNat_lt _

section
-- Exposed closed tables; keep the unifier from evaluating them.
attribute [local irreducible] hibTable popTable

theorem step_spec {cnt : Nat → Nat → Nat} (hbound : totalWeight cnt < 2 ^ 32) {t : ByteArray}
    {m : UInt64} (hm : m.toNat < 2 ^ 30) (hne : (decode m.toNat).Nonempty)
    (h3 : 3 ∣ (decode m.toNat).card)
    (ht : ∀ m' : UInt64, m'.toNat < 2 ^ 30 → decode m'.toNat ⊆ decode m.toNat →
      (decode m'.toNat).card + 3 = (decode m.toNat).card →
      (get32 t m'.toNat).toNat = bestTriplesRef (fun a b => cnt a.val b.val) (decode m'.toNat)) :
    (step (swTable cnt) t m).toNat = bestTriplesRef (fun a b => cnt a.val b.val) (decode m.toNat) := by
  set w : Fin 30 → Fin 30 → ℕ := fun a b => cnt a.val b.val with hw
  set sw := swTable cnt with hsw
  set T := decode m.toNat with hT
  have h0 : m.toNat ≠ 0 := decode_nonempty_iff hne
  have ha : (hibit m).toNat = Nat.log2 m.toNat := hibit_eq m hm
  set aF : Fin 30 := ⟨Nat.log2 m.toNat, log2_lt_thirty hm⟩ with haF
  have hmax : T.max' hne = aF := max'_decode hm hne
  set r := m ^^^ bit (hibit m) with hr_def
  have hr : r.toNat < 2 ^ 30 := clearHigh_lt m hm
  have hdr : decode r.toNat = T.erase aF := decode_clearHigh m hm h0
  set V : UInt64 → UInt64 → UInt64 := fun b c =>
    sw32 sw (hibit m) b + sw32 sw (hibit m) c + sw32 sw b c +
      (get32 t ((r ^^^ bit b) ^^^ bit c).toNat).toUInt64 with hV
  set M : UInt64 → List UInt64 := fun b => bitsDesc 30 (r &&& (bit b - 1)) with hM
  have hunfold : step sw t m = (bitsDesc 30 r).foldl
      (fun acc b => (M b).foldl (fun acc c => if V b c < acc then V b c else acc) acc) SENTINEL := by
    simp only [step, foldBits_eq_foldl]
    rfl
  have hbest_lt : bestTriplesRef w T < 2 ^ 32 :=
    lt_of_le_of_lt ((bestTriplesRef_le_pieceWeight h3).trans (pieceWeight_le_totalWeight cnt T)) hbound
  have key : ((step sw t m).toNat : WithTop ℕ) = (bestTriplesRef w T : WithTop ℕ) := by
    calc ((step sw t m).toNat : WithTop ℕ)
        = min (SENTINEL.toNat : WithTop ℕ) ((bitsDesc 30 r).toFinset.inf fun b =>
            (M b).toFinset.inf fun c => ((V b c).toNat : WithTop ℕ)) := by
          rw [hunfold]
          exact foldl_nested_min_toTop M V _ _
      _ = min (SENTINEL.toNat : WithTop ℕ) ((T.erase aF).inf fun i =>
            ((T.erase aF).filter (· < i)).inf fun j =>
              ((pieceWeight w (insert aF (insert i {j})) +
                bestTriplesRef w (T \ insert aF (insert i {j})) : ℕ) : WithTop ℕ)) := by
          refine congrArg (min _) ?_
          rw [toFinset_bitsDesc hr, Finset.inf_image, hdr]
          refine Finset.inf_congr rfl fun i hi => ?_
          have hi30 : ((i.val : Nat).toUInt64).toNat < 30 := by rw [toNat_finToUInt64]; exact i.isLt
          have hiF : i ≠ aF := (Finset.mem_erase.mp hi).1
          have hiT : i ∈ T := (Finset.mem_erase.mp hi).2
          have hfilt : decode (r &&& (bit (i.val : Nat).toUInt64 - 1)).toNat = (T.erase aF).filter (· < i) := by
            rw [decode_and_below hi30, hdr, toNat_finToUInt64]
            exact Finset.filter_congr fun j _ => Fin.lt_def.symm
          simp only [Function.comp, hM]
          rw [toFinset_bitsDesc (and_below_lt hr), Finset.inf_image, hfilt]
          refine Finset.inf_congr rfl fun j hj => ?_
          obtain ⟨hj', hji⟩ := Finset.mem_filter.mp hj
          have hjF : j ≠ aF := (Finset.mem_erase.mp hj').1
          have hjT : j ∈ T := (Finset.mem_erase.mp hj').2
          have hij : i ≠ j := (ne_of_lt hji).symm
          have hv : (V (i.val : Nat).toUInt64 (j.val : Nat).toUInt64).toNat =
              pieceWeight w (insert aF (insert i {j})) + bestTriplesRef w (T \ insert aF (insert i {j})) := by
            have hi64 := toNat_finToUInt64 i
            have hj64 := toNat_finToUInt64 j
            have hj30 : ((j.val : Nat).toUInt64).toNat < 30 := by rw [hj64]; exact j.isLt
            have ha30 : (hibit m).toNat < 30 := by rw [ha]; exact log2_lt_thirty hm
            have hfi : (⟨((i.val : Nat).toUInt64).toNat, hi30⟩ : Fin 30) = i := Fin.ext hi64
            have hfj : (⟨((j.val : Nat).toUInt64).toNat, hj30⟩ : Fin 30) = j := Fin.ext hj64
            have haT : aF ∈ T := hmax ▸ T.max'_mem hne
            -- The three pair weights.
            have e1 : (sw32 sw (hibit m) (i.val : Nat).toUInt64).toNat = w aF i + w i aF := by
              rw [hsw, sw32_swTable hbound ha30 hi30 (by rw [ha, hi64]; exact fun h => hiF (Fin.ext h.symm)),
                ha, hi64]
            have e2 : (sw32 sw (hibit m) (j.val : Nat).toUInt64).toNat = w aF j + w j aF := by
              rw [hsw, sw32_swTable hbound ha30 hj30 (by rw [ha, hj64]; exact fun h => hjF (Fin.ext h.symm)),
                ha, hj64]
            have e3 : (sw32 sw (i.val : Nat).toUInt64 (j.val : Nat).toUInt64).toNat = w i j + w j i := by
              rw [hsw, sw32_swTable hbound hi30 hj30 (by rw [hi64, hj64]; exact fun h => hij (Fin.ext h)),
                hi64, hj64]
            -- The remaining keys, read from the table.
            have hr1 := xor_bit_lt hr hi30
            have hr2 := xor_bit_lt hr1 hj30
            have hbi : r.toNat.testBit ((i.val : Nat).toUInt64).toNat = true := by
              rw [hi64, ← mem_decode, hdr]
              exact hi
            have hd1 : decode (r ^^^ bit (i.val : Nat).toUInt64).toNat = (T.erase aF).erase i := by
              rw [decode_xor_bit hi30 hbi, hdr, hfi]
            have hbj : (r ^^^ bit (i.val : Nat).toUInt64).toNat.testBit ((j.val : Nat).toUInt64).toNat = true := by
              rw [hj64, ← mem_decode, hd1]
              exact Finset.mem_erase.mpr ⟨hij.symm, hj'⟩
            have hrest : ((T.erase aF).erase i).erase j = T \ insert aF (insert i {j}) := by
              ext x
              simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
                ne_eq]
              exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h4, h3, h2, h1⟩, fun ⟨h4, h3, h2, h1⟩ => ⟨h1, h2, h3, h4⟩⟩
            have hd2 : decode ((r ^^^ bit (i.val : Nat).toUInt64) ^^^ bit (j.val : Nat).toUInt64).toNat =
                T \ insert aF (insert i {j}) := by
              rw [decode_xor_bit hj30 hbj, hd1, hfj, hrest]
            have hsub : insert aF (insert i ({j} : Finset (Fin 30))) ⊆ T := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            have hcard3 : (insert aF (insert i ({j} : Finset (Fin 30)))).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hiF.symm, hjF.symm]), Finset.card_pair hij]
            have e4 := ht _ hr2 (by rw [hd2]; exact Finset.sdiff_subset)
              (by rw [hd2, ← hcard3]; exact Finset.card_sdiff_add_card_eq_card hsub)
            rw [hd2] at e4
            -- No sum overflows.
            have b1 : (sw32 sw (hibit m) (i.val : Nat).toUInt64).toNat < 2 ^ 32 := sw32_lt _ _ _
            have b2 : (sw32 sw (hibit m) (j.val : Nat).toUInt64).toNat < 2 ^ 32 := sw32_lt _ _ _
            have b3 : (sw32 sw (i.val : Nat).toUInt64 (j.val : Nat).toUInt64).toNat < 2 ^ 32 := sw32_lt _ _ _
            have b4 := UInt32.toNat_lt (get32 t ((r ^^^ bit (i.val : Nat).toUInt64) ^^^ bit (j.val : Nat).toUInt64).toNat)
            have hpw := pieceWeight_triple w hiF.symm hjF.symm hij
            simp only [hV, UInt64.toNat_add, UInt32.toNat_toUInt64]
            omega
          rw [Function.comp_apply, hv]
      _ = min (SENTINEL.toNat : WithTop ℕ) (((T.erase aF).powersetCard 2).inf fun bc =>
            ((pieceWeight w (insert aF bc) + bestTriplesRef w (T \ insert aF bc) : ℕ) : WithTop ℕ)) := by
          rw [inf_powersetCard_two]
      _ = min (SENTINEL.toNat : WithTop ℕ) (bestTriplesRef w T : WithTop ℕ) := by
          rw [bestTriplesRef_step hne h3, hmax]
      _ = (bestTriplesRef w T : WithTop ℕ) := by
          have hs : SENTINEL.toNat = 2 ^ 62 := by decide
          refine min_eq_right ?_
          rw [hs]
          exact_mod_cast (by omega : bestTriplesRef w T ≤ 2 ^ 62)
  exact_mod_cast key

end

end FernImpl
