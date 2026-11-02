import CappedDeterminantReal

noncomputable section
open Finset MeasureTheory
namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def cappedVector (a : ℝ) (S R : Finset κ) : κ → ℝ :=
  fun i => if i ∈ S then a else if i ∈ R then 1 - (Nat.floor (1/a):ℝ)*a else 0

/-- The displayed paper vector: k full caps, and one remainder only when it
is nonzero. Disjoint finite sets specify its arbitrary coordinate ordering. -/
theorem cappedVector_spec {a : ℝ} (ha : 0 < a) (S R : Finset κ)
    (hSR : Disjoint S R) (hS : S.card = Nat.floor (1/a))
    (hR : R.card = if 1 - (Nat.floor (1/a):ℝ)*a = 0 then 0 else 1) :
    cappedVector a S R ∈ slice a 1 ∧ (interior a (cappedVector a S R)).card ≤ 1 := by
  have hrange := capped_remainder_range ha
  have hRc : R.card ≤ 1 := by rw [hR]; split_ifs <;> omega
  have hdis : ∀ i, i ∈ S → i ∉ R := fun i hi => Finset.disjoint_left.mp hSR hi
  have hcoord (i : κ) : cappedVector a S R i =
      (if i ∈ S then a else 0) +
      (if i ∈ R then 1 - (Nat.floor (1/a):ℝ)*a else 0) := by
    by_cases hi : i ∈ S
    · simp [cappedVector, hi, hdis i hi]
    · simp [cappedVector, hi]
  constructor
  · constructor
    · intro i
      unfold cappedVector
      split_ifs <;> constructor <;> linarith
    · simp_rw [hcoord]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hS]
      by_cases hr : 1 - (Nat.floor (1/a):ℝ)*a = 0
      · rw [hr, mul_zero, add_zero]
        linarith
      · rw [hR, if_neg hr]
        norm_num
  · apply (Finset.card_le_card (show interior a (cappedVector a S R) ⊆ R from ?_)).trans hRc
    intro i hi
    have h := mem_interior.mp hi
    by_contra hnot
    by_cases his : i ∈ S
    · simp [cappedVector, his] at h
    · simp [cappedVector, his, hnot] at h

/-- Literal capped-vector form of paper Lemma 5.1 with real s>0 and arbitrary
0<a<1 (indeed every positive feasible cap). The singular determinant convention
is extended-valued. No moment-existence assumption is used. -/
theorem extendedRealMoment_le_explicit_cappedVector
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) {w : κ → ℝ}
    (hw : w ∈ slice a 1) (S R : Finset κ) (hSR : Disjoint S R)
    (hS : S.card = Nat.floor (1/a))
    (hR : R.card = if 1 - (Nat.floor (1/a):ℝ)*a = 0 then 0 else 1) :
    extendedRealMoment (Measure.pi (fun _ : κ => μ)) s w ≤
      extendedRealMoment (Measure.pi (fun _ : κ => μ)) s (cappedVector a S R) := by
  have hspec := cappedVector_spec ha S R hSR hS hR
  exact extendedRealMoment_le_capped_vertex μ ha hs hw hspec.1 hspec.2
end GaussianEllipsoid.CappedSimplex
#print axioms GaussianEllipsoid.CappedSimplex.extendedRealMoment_le_explicit_cappedVector
