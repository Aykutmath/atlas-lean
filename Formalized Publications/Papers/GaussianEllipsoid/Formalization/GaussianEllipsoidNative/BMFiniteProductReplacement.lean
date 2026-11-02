import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BMFiniteProductReplacement

variable {X : Type*} [MeasurableSpace X]

/-- Fubini disintegration at any coordinate of the actual independent finite
product law. No conditional-expectation or replacement hypothesis is used. -/
theorem integral_pi_insertNth {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (i : Fin (n+1)) (f : (Fin (n+1) → X) → ℝ)
    (hf : Integrable f (Measure.pi fun _ : Fin (n+1) => μ)) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ u, ∫ x, f (i.insertNth x u) ∂μ ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) i
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
  have hi : Integrable (fun z : X × (Fin n → X) => f (i.insertNth z.1 z.2))
      (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    exact (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  calc
    _ = ∫ z : X × (Fin n → X), f (i.insertNth z.1 z.2)
        ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := (hp.integral_comp' f).symm
    _ = _ := integral_prod_symm _ hi

/-- A genuine finite-product telescoping inequality: a uniform comparison for
one row with all other rows fixed gives the sum of the row errors under the
full iid product law. The intermediate functions may be arbitrary integrable
hybrids and need not factor over coordinates. -/
theorem finite_product_telescoping {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℕ → (Fin (n+1) → X) → ℝ) (ε : ℝ)
    (hF : ∀ k ≤ n+1, Integrable (F k) (Measure.pi fun _ : Fin (n+1) => μ))
    (hrow : ∀ i : Fin (n+1), ∀ u : Fin n → X,
      |(∫ x, F (i.val+1) (i.insertNth x u) ∂μ) -
        ∫ x, F i.val (i.insertNth x u) ∂μ| ≤ ε) :
    |(∫ x, F (n+1) x ∂Measure.pi (fun _ : Fin (n+1) => μ)) -
      ∫ x, F 0 x ∂Measure.pi (fun _ : Fin (n+1) => μ)| ≤ (n+1 : ℕ)*ε := by
  let I : ℕ → ℝ := fun k => ∫ x, F k x ∂Measure.pi (fun _ : Fin (n+1) => μ)
  have hstep (k : ℕ) (hk : k < n+1) : |I (k+1)-I k| ≤ ε := by
    let i : Fin (n+1) := ⟨k,hk⟩
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) i
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    have hprev := (hp.integrable_comp (hF k (by omega)).aestronglyMeasurable).mpr (hF k (by omega))
    have hnext := (hp.integrable_comp (hF (k+1) (by omega)).aestronglyMeasurable).mpr (hF (k+1) (by omega))
    have hprev' : Integrable (fun z : X × (Fin n → X) => F k (i.insertNth z.1 z.2))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := hprev
    have hnext' : Integrable (fun z : X × (Fin n → X) => F (k+1) (i.insertNth z.1 z.2))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) := hnext
    dsimp only [I]
    rw [integral_pi_insertNth μ i _ (hF (k+1) (by omega)),
      integral_pi_insertNth μ i _ (hF k (by omega)),
      ← integral_sub hnext'.integral_prod_right hprev'.integral_prod_right]
    calc
      _ ≤ ∫ u, |(∫ x, F (k+1) (i.insertNth x u) ∂μ) -
            ∫ x, F k (i.insertNth x u) ∂μ| ∂Measure.pi (fun _ : Fin n => μ) :=
        by simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun u : Fin n → X =>
            (∫ x, F (k+1) (i.insertNth x u) ∂μ) - ∫ x, F k (i.insertNth x u) ∂μ))
      _ ≤ ∫ _u : Fin n → X, ε ∂Measure.pi (fun _ : Fin n => μ) :=
        integral_mono (hnext'.integral_prod_right.sub hprev'.integral_prod_right).norm
          (integrable_const ε) (fun u => hrow i u)
      _ = ε := by simp
  change |I (n+1)-I 0| ≤ _
  rw [← Finset.sum_range_sub I (n+1)]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), |I (k+1)-I k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1), ε :=
      Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)
    _ = _ := by simp

/-- Normalization used for finite-prior BM free energy. -/
theorem normalized_expectation_comparison {a b ε β v : ℝ}
    (hβ : 0 < β) (hv : 0 < v) (h : |a-b| ≤ ε) :
    |(-a/(β*v))-(-b/(β*v))| ≤ ε/(β*v) := by
  have hd : 0 < β*v := mul_pos hβ hv
  calc
    _ = |a-b|/(β*v) := by rw [← sub_div, show -a - -b = -(a-b) by ring, abs_div, abs_neg, abs_of_pos hd]
    _ ≤ _ := div_le_div_of_nonneg_right h hd.le

#print axioms finite_product_telescoping
#print axioms integral_pi_insertNth
#print axioms normalized_expectation_comparison
end BMFiniteProductReplacement
