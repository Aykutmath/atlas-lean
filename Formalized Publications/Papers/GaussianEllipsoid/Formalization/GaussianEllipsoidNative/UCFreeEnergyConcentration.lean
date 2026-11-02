import UCProductConcentration
import UCFreeEnergyBridge

/-! Exponential concentration for the actual normalized finite free energy.
This supplies the UC exp(-c n) probability rate directly, with no McDiarmid
or Gaussian-concentration assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition
open GaussianEllipsoid.UCProductConcentration
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCFreeEnergyConcentration
variable {κ X : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
  [MeasurableSpace X] [Nonempty X]

/-- The actual weighted free energy is a measurable function of all rows. -/
theorem measurable_freeEnergy (D : Data κ) {n : ℕ}
    (q : X → κ → ℝ) (hq : Measurable q) (c : Fin n → κ → ℝ) :
    Measurable (fun x : Fin n → X => UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i)) := by
  unfold UCActualFreeEnergy.freeEnergy
  apply Measurable.div_const
  apply Measurable.neg
  apply (fullLogPartition_continuous D n).measurable.comp
  exact measurable_pi_iff.mpr fun i =>
    (hq.comp (measurable_pi_apply i)).add_const _

/-- Each bounded normalized free energy has a lower-tail of exp(-n t²/2). -/
theorem freeEnergy_lower_tail (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (hweight : ∀ a, D.weight a = (Fintype.card κ:ℝ)⁻¹)
    (hβ : 0 < D.beta) {n : ℕ} (hn : 0 < n)
    (hloss : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (q : X → κ → ℝ) (hq : Measurable q) (c : Fin n → κ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    (productLaw μ n).real {x |
      UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i) <
        (∫ y, UCActualFreeEnergy.freeEnergy D (fun i => q (y i)+c i) ∂productLaw μ n)-t}
      ≤ Real.exp (-(n:ℝ)*t^2/2) := by
  apply normalized_product_lower_tail μ n hn _ (measurable_freeEnergy D q hq c) 1 _ _ t ht
  · intro x
    have h := UCFreeEnergyBridge.freeEnergy_mem_unit_interval D hweight hβ hn hloss
      (fun i => q (x i)+c i)
    rw [abs_of_nonneg h.1]
    exact h.2
  · intro x i z
    exact UCFreeEnergyBridge.freeEnergy_row_difference D hweight hβ hn hloss q c x i z

/-- A proved expectation floor moves the same exponential tail to a fixed
positive margin. -/
theorem freeEnergy_below_margin (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (hweight : ∀ a, D.weight a = (Fintype.card κ:ℝ)⁻¹)
    (hβ : 0 < D.beta) {n : ℕ} (hn : 0 < n)
    (hloss : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (q : X → κ → ℝ) (hq : Measurable q) (c : Fin n → κ → ℝ)
    (a t : ℝ) (ht : 0 ≤ t)
    (hmean : a+t ≤ ∫ y, UCActualFreeEnergy.freeEnergy D (fun i => q (y i)+c i) ∂productLaw μ n) :
    (productLaw μ n).real {x | UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i) < a}
      ≤ Real.exp (-(n:ℝ)*t^2/2) := by
  apply le_trans (measureReal_mono (μ := productLaw μ n) ?_)
    (freeEnergy_lower_tail μ D hweight hβ hn hloss q hq c t ht)
  intro x hx
  change UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i) < _
  change UCActualFreeEnergy.freeEnergy D (fun i => q (x i)+c i) < a at hx
  linarith

/-- The actual UC finite-net free energy has an exponential lower-tail once
its Gaussian comparison has the robust expectation floor. -/
theorem quadratic_freeEnergy_margin {d : ℕ}
    (D : Data2 κ) (hweight : ∀ a, D.weight a = (Fintype.card κ:ℝ)⁻¹)
    (hβ : 0 < D.beta) (hloss : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (A : κ → Square d) (hAsym : ∀ a, (A a).transpose = A a) (hd : 0 < d)
    (τ : ℝ) (hτ : 0 ≤ τ) (hOp : ∀ a, matrixOpNorm (A a) ≤ τ)
    (hF : ∀ a, frobeniusNorm (A a) ≤ 1)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hsmall : (UCActualFreeEnergy.comparisonConstant D/D.beta)*τ ≤ θ/16)
    (hGaussian : 15*θ/16 ≤ ∫ z : Fin (n+1) → (Fin (d*d) → ℝ),
      UCActualFreeEnergy.freeEnergy D.toData (fun i => UCActualFreeEnergy.linearRow A (z i)+c i)
        ∂Measure.pi (fun _ : Fin (n+1) => GaussianTensorMoments.gaussianProductLaw (Fin (d*d)))) :
    (gaussianSampleLaw d (n+1)).real {x |
      UCActualFreeEnergy.freeEnergy D.toData
        (fun i => UCActualFreeEnergy.quadraticRow A (x i)+c i) < 3*θ/4}
      ≤ Real.exp (-((n+1:ℕ):ℝ)*θ^2/128) := by
  have hcomp := UCActualFreeEnergy.actual_freeEnergy_comparison D hβ A hAsym hd τ hτ hOp hF n c
  have hmean : 3*θ/4+θ/8 ≤ ∫ y,
      UCActualFreeEnergy.freeEnergy D.toData
        (fun i => UCActualFreeEnergy.quadraticRow A (y i)+c i) ∂gaussianSampleLaw d (n+1) := by
    have hc := (abs_le.mp (hcomp.trans hsmall)).1
    linarith
  have h := freeEnergy_below_margin (gaussianVectorLaw d) D.toData hweight hβ
    (Nat.succ_pos n) hloss _ (UCActualFreeEnergy.quadraticRow_continuous A hd).measurable c
    (3*θ/4) (θ/8) (by positivity) hmean
  exact h.trans_eq (by congr 1; ring)

#print axioms freeEnergy_lower_tail
#print axioms quadratic_freeEnergy_margin
end GaussianEllipsoid.UCFreeEnergyConcentration
