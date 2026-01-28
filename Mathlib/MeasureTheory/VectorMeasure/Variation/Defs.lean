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

open Finpartition
-- TODO: move to Finpartition file
/-- Extend a partition of `a` to a partition of `b` when `a ≤ b`, by adding `b \ a` as a `part`. -/
def _root_.Finpartition.extendOfLE {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a ≤ b) : Finpartition b :=
  if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)

lemma _root_.Finpartition.parts_extendOfLE_of_eq {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a : α} (P : Finpartition a) :
    (P.extendOfLE (a := a) (b := a) (by rfl)).parts = P.parts := by simp [extendOfLE]

lemma _root_.Finpartition.parts_extendOfLE_of_lt {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a < b) :
    (P.extendOfLE (le_of_lt hab)).parts = insert (b \ a) P.parts := by
  simp [extendOfLE, Std.not_le_of_gt hab]

lemma _root_.Finpartition.parts_subset_extendOfLE {α : Type*} [GeneralizedBooleanAlgebra α]
    [DecidableEq α] {a b : α} (P : Finpartition a) (hab : a ≤ b) :
    P.parts ⊆ (P.extendOfLE hab).parts := by
  simp only [Finpartition.extendOfLE]
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _
---

-- TODO: move to Finpartition file
/-- Construct a `Finpartition` of `T.sup id` from a finset `T` of pairwise disjoint elements.
Any `⊥` elements in `T` are erased since they don't contribute to the supremum. -/
@[simps]
def _root_.Finpartition.ofPairwiseDisjoint {α : Type*} [DistribLattice α] [OrderBot α]
    [DecidableEq α] (T : Finset α) (hT : (T : Set α).PairwiseDisjoint id) :
    Finpartition (T.sup id) where
  parts := T.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hT (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot T
  bot_notMem := Finset.notMem_erase _ _
---

open Classical in
lemma sum_le_preVariation_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariation f (⋃ i, s i) := by
  -- Step 1: S.sup id = ⟨⋃ i ∈ range n, s i, ...⟩
  let S : Finset (Subtype MeasurableSet) :=
    (Finset.range n).image fun i => ⟨s i, hs i⟩
  have sup_eq (m : ℕ) : ((Finset.range m).sup fun i => (⟨s i, hs i⟩ : Subtype MeasurableSet)) =
      ⋃ i ∈ Finset.range m, s i := by
    induction m with
    | zero => simp
    | succ k ih => simp [Finset.range_add_one, Finset.sup_insert, ih]
  have hS_sup : S.sup id = ⟨⋃ i ∈ Finset.range n, s i,
      MeasurableSet.biUnion (Finset.range n).countable_toSet fun i _ => hs i⟩ := by
    apply Subtype.ext
    simp only [S, Finset.sup_image, Function.id_comp]
    exact sup_eq n
  -- Step 2: Direct union of all partition parts
  let Q_parts := (Finset.range n).biUnion (fun i => (P i).parts)
  -- Helper: s i and s j are disjoint as subtypes when i ≠ j
  have hs_disj : ∀ i j, i ≠ j → Disjoint (⟨s i, hs i⟩ : Subtype MeasurableSet) ⟨s j, hs j⟩ := by
    intro i j hij
    rw [disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  -- Parts from different P i are disjoint
  have hQ_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) (fun i => (P i).parts) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have hp_disj : Disjoint p p := (hs_disj i j hij).mono ((P i).le hpi) ((P j).le hpj)
    exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)
  -- Q_parts is pairwise disjoint (for ofPairwiseDisjoint)
  have hQ_parts_pwdisj : Set.PairwiseDisjoint (SetLike.coe Q_parts) id := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_biUnion] at ha hb
    obtain ⟨i, _, hai⟩ := ha
    obtain ⟨j, _, hbj⟩ := hb
    by_cases hij : i = j
    · subst hij
      exact (P i).disjoint hai hbj (fun h => hab (h ▸ rfl))
    · exact (hs_disj i j hij).mono ((P i).le hai) ((P j).le hbj)
  -- ⊥ is not in Q_parts (since each (P i).bot_notMem)
  have hbot_notMem : ⊥ ∉ Q_parts := by
    rw [Finset.mem_biUnion]
    push_neg
    exact fun i _ => (P i).bot_notMem
  -- Q_parts.sup id equals S.sup id
  have hQ_parts_sup : Q_parts.sup id = S.sup id := by
    simp only [Q_parts, S, Finset.sup_biUnion, Finset.sup_image, Function.id_comp]
    congr 1
    funext i
    exact (P i).sup_parts
  -- Create Q as a Finpartition of Q_parts.sup id
  let Q := Finpartition.ofPairwiseDisjoint Q_parts hQ_parts_pwdisj
  -- Q.parts = Q_parts (since ⊥ ∉ Q_parts)
  have hQ_parts_eq : Q.parts = Q_parts := Finset.erase_eq_self.mpr hbot_notMem
  -- Step 4: Extend Q to a partition of ⋃ i, s i
  have hQ_le : Q_parts.sup id ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [hQ_parts_sup, hS_sup]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
      _ = ∑ p ∈ Q_parts, f p := (Finset.sum_biUnion hQ_disj).symm
      _ = ∑ p ∈ Q.parts, f p := by rw [hQ_parts_eq]
      _ ≤ ∑ p ∈ R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
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

lemma sum_le_tsum' {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ b < a, ∃ n, b < ∑ i ∈ Finset.range n, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := h b hb
  exact lt_of_lt_of_le hn (ENNReal.sum_le_tsum <| Finset.range n)

open Classical in
lemma iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    preVariation f (⋃ i, s i) ≤ ∑' i, preVariation f (s i) := by
  refine sum_le_tsum' fun b hb ↦ ?_
  simp only [preVariation, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  -- Step 1: Define restriction partitions P_parts i
  -- P_parts i = { q ⊓ ⟨s i, hs i⟩ | q ∈ Q.parts } \ {⊥}
  let P_parts (i : ℕ) : Finset (Subtype MeasurableSet) :=
    (Q.parts.image (· ⊓ ⟨s i, hs i⟩)).erase ⊥
  have hP_disj (i : ℕ) : Set.PairwiseDisjoint {x | x ∈ P_parts i} id := by
    intro a ha b hb hab
    rw [Set.mem_setOf, Finset.mem_erase, Finset.mem_image] at ha hb
    obtain ⟨_, qa, hqa, rfl⟩ := ha
    obtain ⟨_, qb, hqb, rfl⟩ := hb
    have hdisj := Q.disjoint hqa hqb fun h => hab (by rw [h])
    exact hdisj.inf_left (c := ⟨s i, hs i⟩) |>.inf_right (c := ⟨s i, hs i⟩)
  have hP_sup (i : ℕ) : (P_parts i).sup id = ⟨s i, hs i⟩ := by
    have h1 : (P_parts i).sup id = (Q.parts.image (· ⊓ ⟨s i, hs i⟩)).sup id :=
      Finset.sup_erase_bot _
    have h2 : (Q.parts.image (· ⊓ ⟨s i, hs i⟩)).sup id = Q.parts.sup (· ⊓ ⟨s i, hs i⟩) :=
      Finset.sup_image ..
    have h3 : Q.parts.sup (· ⊓ ⟨s i, hs i⟩) = Q.parts.sup id ⊓ ⟨s i, hs i⟩ :=
      (Finset.sup_inf_distrib_right ..).symm
    rw [h1, h2, h3, Q.sup_parts, inf_eq_right]
    exact Set.subset_iUnion s i
  -- Step 2: Key splitting inequality using P_parts directly
  have hinj (i : ℕ) : ∀ a ∈ Q.parts, ∀ b ∈ Q.parts,
      a ⊓ ⟨s i, hs i⟩ ≠ ⊥ → b ⊓ ⟨s i, hs i⟩ ≠ ⊥ →
      a ⊓ ⟨s i, hs i⟩ = b ⊓ ⟨s i, hs i⟩ → a = b := by
    intro a ha b hb ha' hb' hab
    by_contra hne
    have hdisj : Disjoint a b := Q.disjoint ha hb hne
    have : a ⊓ ⟨s i, hs i⟩ ⊓ (b ⊓ ⟨s i, hs i⟩) = ⊥ :=
      disjoint_iff.mp (hdisj.mono inf_le_left inf_le_left)
    rw [hab, inf_idem] at this
    exact hb' this
  let si (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hP_parts_sum (i : ℕ) : ∑ p ∈ P_parts i, f p = ∑ q ∈ Q.parts, f (q ⊓ si i) := by
    have heq : P_parts i = (Q.parts.filter (· ⊓ si i ≠ ⊥)).image (· ⊓ si i) := by
      ext p
      simp only [P_parts, si, Finset.mem_erase, ne_eq, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hp, q, hq, rfl⟩; exact ⟨q, ⟨hq, hp⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hp⟩, rfl⟩; exact ⟨hp, q, hq, rfl⟩
    have hinj' : ∀ a ∈ Q.parts.filter (· ⊓ si i ≠ ⊥), ∀ b ∈ Q.parts.filter (· ⊓ si i ≠ ⊥),
        a ⊓ si i = b ⊓ si i → a = b := by
      intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb
      exact hinj i a ha.1 b hb.1 ha.2 hb.2 hab
    rw [heq, Finset.sum_image hinj']
    have hz : ∑ x ∈ Q.parts.filter (· ⊓ si i = ⊥), f (x ⊓ si i) = 0 := by
      apply Finset.sum_eq_zero
      simp only [Finset.mem_filter, and_imp]
      intro q _ hq
      change f (↑q ⊓ ↑(si i)) = 0
      have : (↑q ⊓ ↑(si i) : Set X) = ∅ := by
        rw [show (↑q ⊓ ↑(si i) : Set X) = ↑(q ⊓ si i) from rfl, hq]; rfl
      rw [this, hf']
    rw [← Finset.sum_filter_add_sum_filter_not Q.parts (· ⊓ si i ≠ ⊥)]
    simp only [ne_eq, Decidable.not_not, hz, add_zero]
    rfl
  have splitting : ∑ q ∈ Q.parts, f q ≤ ∑' i, ∑ p ∈ P_parts i, f p := by
    calc ∑ q ∈ Q.parts, f q
        ≤ ∑ q ∈ Q.parts, ∑' i, f (q ⊓ si i) := by
          apply Finset.sum_le_sum
          intro q hq
          have hq_subset : q.val ⊆ ⋃ i, s i := Q.le hq
          have hq_eq : q.val = ⋃ i, q.val ∩ s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr hq_subset).symm
          have hq_disj : Pairwise (Disjoint on fun i => q.val ∩ s i) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q = f q.val := rfl
            _ = f (⋃ i, q.val ∩ s i) := congrArg f hq_eq
            _ ≤ ∑' i, f (q.val ∩ s i) := hf _ (fun i => q.2.inter (hs i)) hq_disj
            _ = ∑' i, f (q ⊓ si i) := rfl
      _ = ∑' i, ∑ q ∈ Q.parts, f (q ⊓ si i) :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ = ∑' i, ∑ p ∈ P_parts i, f p := by simp only [hP_parts_sum]
  -- Step 3: Find finite n from convergence
  have hb' : b < ∑' i, ∑ p ∈ P_parts i, f p := lt_of_lt_of_le hQ splitting
  rw [ENNReal.tsum_eq_iSup_nat] at hb'
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hb'
  -- Step 4: Bound each P_parts sum by preVariation using sum_le
  have bound (i : ℕ) : ∑ p ∈ P_parts i, f p ≤ preVariation f (s i) := by
    have hbot : ⊥ ∉ P_parts i := Finset.notMem_erase ⊥ _
    let P' : Finpartition ((P_parts i).sup id) :=
      Finpartition.ofPairwiseDisjoint (P_parts i) (hP_disj i)
    have hP'_parts : P'.parts = P_parts i := by
      simp only [P', Finpartition.ofPairwiseDisjoint]
      exact Finset.erase_eq_of_notMem hbot
    have hP'_sup_eq : ((P_parts i).sup id : Subtype MeasurableSet).val = s i := by
      rw [hP_sup i]
    have hP'_meas : MeasurableSet ((P_parts i).sup id).val := by rw [hP'_sup_eq]; exact hs i
    calc ∑ p ∈ P_parts i, f p = ∑ p ∈ P'.parts, f p := by rw [hP'_parts]
      _ ≤ preVariation f ((P_parts i).sup id).val := sum_le f hP'_meas P'
      _ = preVariation f (s i) := by rw [hP'_sup_eq]
  -- Step 5: Conclude
  exact ⟨n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

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
