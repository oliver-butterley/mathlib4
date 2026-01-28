/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function actually is a measure.

## Main definition

* `VectorMeasure.variation` is the definition of the total variation measure.

## Implementation notes

Variation is defined as an `ℝ≥0∞`-valued `VectorMeasure` rather than as a `Measure`, this is
somewhat natural since we start with `VectorMeasure`. The corresponding `Measure` is given by
`VectorMeasure.ennrealToMeasure`.

Variation is defined for signed measures in `MeasureTheory.SignedMeasure.totalVariation`. This
definition uses the Hahn–Jordan decomposition of a signed measure. However this construction doesn't
generalize to other vector-valued measures, in particular doesn't apply to the case of complex
measures.

The notion of defining a set function as the supremum over all choices of partition of the sum gives
a measure for any subadditive set function which assigns zero measure to the empty set. Consequently
the construction is first developed for any subadditive set function before specializing to the case
of `s ↦ ‖μ s‖ₑ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

open MeasureTheory BigOperators ENNReal Function

namespace MeasureTheory

/-!
## Variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all partitions `E i` of the sum of `∑ i, f (E i)`. If `f` is sub-additive then the function
defined is an `ℝ≥0∞`-valued measure.
-/

section

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

open Classical in
/-- If `s` is measurable then `preVariation s f` is the supremum over partitions `P` of `s` of the
quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def preVariation (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
    else 0

end

namespace preVariation

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

-- move to MeasurablyGenerated
@[simp]
lemma set_subtype_bot_eq {α : Type*} [MeasurableSpace α] :
  (⟨∅, .empty⟩ : Subtype (MeasurableSet (α := X))) = ⊥ := rfl
--

/-- `preVariation` of the empty set is equal to zero. -/
lemma empty : preVariation f ∅ = 0 := by simp [preVariation]

lemma sum_le {s : Set X} (hs : MeasurableSet s) (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet))
    : ∑ p ∈ P.parts, f p ≤ preVariation f s := by
  simp only [preVariation, hs, reduceDIte]
  exact le_iSup_iff.mpr fun b a ↦ a P

open Classical in
/-- If `P` is a partition of `s₁` and `s₁ ⊊ s₂` then `∑ p ∈ P.parts, f p ≤ preVariation f s₂`. -/
lemma sum_le_preVariation_of_subset_ne {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) (h_ne : s₁ ≠ s₂)
    (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariation f s₂ := by
  let b : Subtype MeasurableSet := ⟨s₂ \ s₁, hs₂.diff hs₁⟩
  have hb : b ≠ ⊥ := by
    by_contra hc
    suffices h : s₂ ⊆ s₁ by grind
    apply Set.diff_eq_empty.mp
    simp_all [b, ← set_subtype_bot_eq, Subtype.mk.injEq]
  have hab : Disjoint (⟨s₁, hs₁⟩ : Subtype MeasurableSet) b := by simp_all [b, disjoint_iff]
  have hc : (⟨s₁, hs₁⟩ : Subtype MeasurableSet) ⊔ b = ⟨s₂, hs₂⟩ := by simp_all [b]
  let Q := P.extend hb hab hc
  calc ∑ p ∈ P.parts, f p
    _ ≤ ∑ p ∈ Q.parts, f p := by
      apply Finset.sum_le_sum_of_subset
      intro _ hx
      simpa [Q] using Or.inr hx
    _ ≤ preVariation f s₂ := sum_le f hs₂ _

/-- `preVariation` is monotone in terms of the (measurable) set. -/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariation f s₁ ≤ preVariation f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · by_cases hne : s₁ = s₂
    · simp_all
    · have := sum_le_preVariation_of_subset_ne f hs₁ hs₂ h hne
      simp_all [preVariation]
  · simp [preVariation, hs₁]

lemma exists_isSubpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariation f s) : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p ∈ P.parts, f p := by
  simp_all [preVariation, lt_iSup_iff]

-- Move to Mathlib/Order/Partition/Finpartition.lean
instance _root_.Finpartition.instNonempty {α : Type*} [Lattice α] [OrderBot α] (a : α) :
    Nonempty (Finpartition a) := by
  by_cases h : a = ⊥
  · rw [h]; exact ⟨Finpartition.empty α⟩
  · exact ⟨Finpartition.indiscrete h⟩
---

lemma exists_isSubpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε : 0 < ε)
    (h : preVariation f s ≠ ⊤) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariation f s ≤ ∑ p ∈ P.parts, f p + ε := by
  let ε' := min ε (preVariation f s).toNNReal
  have hε1 : ε' ≤ preVariation f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariation f s ≠ 0 ∨ preVariation f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariation f s - ε'
    have ha : a < preVariation f s := by exact ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_isSubpartition_sum_gt f hs ha
    refine ⟨P, ?_⟩
    calc preVariation f s
      _ = a + ε' := (tsub_add_cancel_of_le hε1).symm
      _ ≤ ∑ p ∈ P.parts, f p + ε' := by
        apply (ENNReal.add_le_add_iff_right coe_ne_top).mpr
        grind
      _ ≤ ∑ p ∈ P.parts, f p + ε := by gcongr
  · simp [*]

-- TODO: move to Finpartition file
/-- Extend a partition of `a` to a partition of `b` when `a ≤ b`, by adding `b \ a` as a `part`. -/
noncomputable def _root_.Finpartition.extendSup {α : Type*} [GeneralizedBooleanAlgebra α] {a b : α}
    (P : Finpartition a) (hab : a ≤ b) : Finpartition b := by
  classical
  exact if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

lemma _root_.Finpartition.parts_subset_extendSup {α : Type*} [GeneralizedBooleanAlgebra α]
    {a b : α} (P : Finpartition a) (hab : a ≤ b) : P.parts ⊆ (P.extendSup hab).parts := by
  classical
  simp only [Finpartition.extendSup]
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _

-- TODO: move to Finpartition file
/-- Construct a `Finpartition` of `T.sup id` from a finset `T` of pairwise disjoint elements.
Any `⊥` elements in `T` are erased since they don't contribute to the supremum. -/
@[simps]
def _root_.Finpartition.ofPairwiseDisjoint {α : Type*} [DistribLattice α] [OrderBot α]
    [DecidableEq α] (T : Finset α) (hT : (T : Set α).PairwiseDisjoint id) :
    Finpartition (T.sup id) where
  parts := T.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun a ha b hb hab =>
    hT (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot T
  bot_notMem := Finset.notMem_erase _ _
---

lemma sum_le_preVariation_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariation f (⋃ i, s i) := by
  classical
  -- Step 1: Create the coarse partition Q' with parts {⟨s 0, hs 0⟩, ..., ⟨s (n-1), hs (n-1)⟩}
  let S : Finset (Subtype MeasurableSet) :=
    (Finset.range n).image fun i => ⟨s i, hs i⟩
  have hS_disjoint : Set.PairwiseDisjoint S.toSet id := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, rfl⟩ := hb
    have hne : i ≠ j := fun h => hab (by simp [h])
    simp only [Function.onFun, id_eq, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hne)
  let Q' := Finpartition.ofPairwiseDisjoint S hS_disjoint
  -- Step 2: S.sup id = ⟨⋃ i ∈ range n, s i, ...⟩
  have sup_eq : ∀ m, ↑((Finset.range m).sup fun i => (⟨s i, hs i⟩ : Subtype MeasurableSet)) =
      ⋃ i ∈ Finset.range m, s i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_add_one, Finset.sup_insert]
      change s k ∪ ↑((Finset.range k).sup fun i => (⟨s i, hs i⟩ : Subtype MeasurableSet)) =
        ⋃ i ∈ insert k (Finset.range k), s i
      rw [ih]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert, Finset.mem_range]
      constructor
      · intro hx
        cases hx with
        | inl h => exact ⟨k, Or.inl rfl, h⟩
        | inr h =>
          obtain ⟨i, hi, hxi⟩ := h
          exact ⟨i, Or.inr hi, hxi⟩
      · intro ⟨i, hi, hxi⟩
        cases hi with
        | inl h => exact Or.inl (h ▸ hxi)
        | inr h => exact Or.inr ⟨i, h, hxi⟩
  have hS_sup : S.sup id = ⟨⋃ i ∈ Finset.range n, s i,
      MeasurableSet.biUnion (Finset.range n).countable_toSet fun i _ => hs i⟩ := by
    apply Subtype.ext
    simp only [S, Finset.sup_image, Function.id_comp]
    exact sup_eq n
  -- Step 3: Use bind to refine Q' with the P i partitions
  -- For each p ∈ Q'.parts = S.erase ⊥, we have p ∈ S, so p = ⟨s i, hs i⟩ for some i
  have hS_mem : ∀ p ∈ Q'.parts, ∃ i ∈ Finset.range n, p = ⟨s i, hs i⟩ := fun p hp => by
    have : p ∈ S := Finset.erase_subset _ _ hp
    simp only [S, Finset.mem_image] at this
    obtain ⟨i, hi, rfl⟩ := this
    exact ⟨i, hi, rfl⟩
  let hbind_fn : ∀ p ∈ Q'.parts, Finpartition p := fun p hp =>
    (hS_mem p hp).choose_spec.2 ▸ P (hS_mem p hp).choose
  let Q := Q'.bind hbind_fn
  -- Step 4: Extend Q to a partition of ⋃ i, s i using extendSup
  have hQ_le : S.sup id ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [hS_sup]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendSup hQ_le
  -- Step 5: The calc proof
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
      ≤ ∑ p ∈ R.parts, f ↑p := by
        -- Each p ∈ (P i).parts is in R.parts

        sorry
    _ ≤ ∑ p ∈ R.parts, f ↑p := by
        -- R.parts ⊇ Q.parts by parts_subset_extendSup
        apply Finset.sum_le_sum_of_subset
        exact Q.parts_subset_extendSup hQ_le
    _ ≤ preVariation f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

lemma sum_le_preVariation_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariation f (s i) ≤ preVariation f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  wlog hn : n ≠ 0
  · simp [show n = 0 by omega]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariation f (s i) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt ?_ hsnetop
    exact mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a)
  -- For each set `s i` we choose a subpartition `P i` such that, for each `i`,
  -- `preVariation f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_isSubpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariation f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i).parts, f p + ε) := by
      gcongr with i _
      exact (hP i)
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]
      norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ preVariation f (⋃ i, s i) + ε' := by
      have := sum_le_preVariation_iUnion' f hs hs' P n
      gcongr

/-- A set function is subadditive if the value assigned to the union of disjoint sets is bounded
above by the sum of the values assigned to the individual sets. -/
def IsSubadditive (f : Set X → ℝ≥0∞) : Prop := ∀ (s : ℕ → Set X), (∀ i, MeasurableSet (s i)) →
  Pairwise (Disjoint on s) → f (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), f (s i)

-- /-- Given a subpartition `Q`, `∑ q ∈ Q, f q` is bounded by the sum of the `∑ q ∈ (P i), f q` where
-- the `P i` are the subpartitions formed by restricting to a disjoint set of sets `s i`. -/
-- lemma sum_part_le_tsum_sum_part (hf : IsSubadditive f) (hf' : f ∅ = 0) {s : ℕ → Set X}
--     (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)}
--     (hQ : IsSubpartition (⋃ i, s i) Q) :
--     ∑ q ∈ Q, f q ≤ ∑' i, ∑ p ∈ (IsSubpartition.restriction (s i) Q), f p := by
--   classical
--   let P (i : ℕ) := IsSubpartition.restriction (s i) Q
--   calc ∑ q ∈ Q, f q
--     _ = ∑ q ∈ Q, f (⋃ i, q ∩ s i) := ?_
--     _ ≤ ∑ q ∈ Q, ∑' i, f (q ∩ s i) := ?_
--     _ = ∑' i, ∑ q ∈ Q, f (q ∩ s i) := ?_
--     _ ≤ ∑' i, ∑ p ∈ (P i), f p := ?_
--   · -- Each `q` is equal to the union of `q ∩ s i`.
--     -- TO DO: This only needs one direction of the argument since subadditivity implies monotone.
--     suffices h : ∀ q ∈ Q, q = ⋃ i, q ∩ s i by
--       exact Finset.sum_congr rfl (fun q hq ↦ (by simp [← h q hq]))
--     intro q hq
--     ext x
--     refine ⟨fun hx ↦ ?_, by simp_all⟩
--     obtain ⟨_, hs⟩ := (hQ.1 q hq) hx
--     obtain ⟨i, _⟩ := Set.mem_range.mp hs.1
--     simp_all [Set.mem_iUnion_of_mem i]
--   · -- Subadditivity of `f` since the `s i` are pairwise disjoint.
--     suffices h : ∀ p ∈ Q, f (⋃ i, p ∩ s i) ≤ ∑' (i : ℕ), f (p ∩ s i) by exact Finset.sum_le_sum h
--     intro p hp
--     refine hf (fun (i : ℕ) ↦ p ∩ s i) (fun i ↦ ?_) ?_
--     · exact MeasurableSet.inter (hQ.measurableSet p hp) (hs i)
--     · refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
--       intro _ _ _
--       exact Disjoint.inter_left' p (Disjoint.inter_right' p (hs' (by omega)))
--   · -- Swapping the order of the sum.
--     refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
--   · -- By defintion of the restricted subpartition
--     refine ENNReal.tsum_le_tsum (fun i ↦ ?_)
--     calc ∑ q ∈ Q, f (q ∩ s i)
--       _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), f p := by
--         refine Eq.symm (Finset.sum_image_of_disjoint (by simp [hf']) ?_)
--         intro _ hp _ hq hpq
--         exact Disjoint.inter_left (s i) (Disjoint.inter_right (s i) (hQ.disjoint hp hq hpq))
--       _ ≤  ∑ p ∈ P i, f p := by
--         refine Finset.sum_le_sum_of_ne_zero (fun p hp hp' ↦ ?_)
--         obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
--         · simp [hc, hf'] at hp'
--         · simp only [P, IsSubpartition.restriction, Finset.mem_filter, Finset.mem_image]
--           obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hp
--           refine ⟨⟨q, hq, hq'⟩, ?_⟩
--           exact Set.nonempty_iff_ne_empty.mpr hc

lemma sum_le_tsum' {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ b < a, ∃ n, b < ∑ i ∈ Finset.range n, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := h b hb
  exact lt_of_lt_of_le hn (ENNReal.sum_le_tsum <| Finset.range n)

open Classical in
lemma iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    preVariation f (⋃ i, s i) ≤ ∑' i, preVariation f (s i) := by
  -- refine sum_le_tsum' fun b hb ↦ ?_
  -- simp  [preVariation, MeasurableSet.iUnion hs, reduceIte, lt_iSup_iff] at hb
  -- obtain ⟨Q, hQ⟩ := hb
  -- -- Take the subpartitions defined as intersection of `Q` and `s i`.
  -- let P (i : ℕ) := IsSubpartition.restriction (s i) Q
  -- have hP (i : ℕ) : IsSubpartition (s i) (P i) :=
  --   IsSubpartition.restriction_of_measurableSet hQ (hs i)
  -- have hP' := calc
  --   b < ∑ q ∈ Q, f q := hbQ
  --   _ ≤ ∑' i, ∑ p ∈ (P i), f p := by exact sum_part_le_tsum_sum_part f hf hf' hs hs' hQ
  -- have := tendsto_nat_tsum fun i ↦ ∑ p ∈ (P i), f p
  -- obtain ⟨n, hn, _⟩ := (((tendsto_order.mp this).1 b hP').and (Filter.Ici_mem_atTop 1)).exists
  -- use n
  -- calc
  --   b < ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p := hn
  --   _ ≤ ∑ i ∈ Finset.range n, preVariation f (s i) := by
  --     gcongr with i hi
  --     exact sum_le f (hs i) (hP i)
  sorry

/-- Additivity of `variation_aux` for disjoint measurable sets. -/
lemma iUnion (hf : IsSubadditive f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariation f (s i)) (preVariation f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (eq_of_le_of_ge ?_ ?_)
  · exact sum_le_preVariation_iUnion f hs hs'
  · exact iUnion_le f hs hs' hf hf'

end preVariation

/-!
## Definition of variation
-/

namespace VectorMeasure

open MeasureTheory.VectorMeasure preVariation

variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

lemma isSubadditive_enorm_vectorMeasure (μ : VectorMeasure X V) : IsSubadditive (‖μ ·‖ₑ) := by
  intro _ hs hs'
  simpa [VectorMeasure.of_disjoint_iUnion hs hs'] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariation (‖μ ·‖ₑ)
  empty' := preVariation.empty (‖μ ·‖ₑ)
  not_measurable' _ h := by simp [preVariation, h]
  m_iUnion' := iUnion (‖μ ·‖ₑ) (isSubadditive_enorm_vectorMeasure μ) (by simp)

/-- The variation of a `VectorMeasure` as a `Measure`. -/
noncomputable def variation (μ : VectorMeasure X V) : Measure X
  := (ennrealVariation μ).ennrealToMeasure

end VectorMeasure

end MeasureTheory
