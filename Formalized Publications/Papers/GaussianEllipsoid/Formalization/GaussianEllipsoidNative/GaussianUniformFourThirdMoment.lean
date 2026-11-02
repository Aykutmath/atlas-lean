import FourThirdOperatorNet
import GaussianUniformFractionalMoment

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory Real Set GaussianMixedNormHelpers BMQuadraticSpectral BMUniformMoment
open scoped ENNReal BigOperators
namespace BMFourThirdMoment

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) := Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) := Submodule.normedSpace (symmetricOperators d)

/-- Finite-dimensional uniform fractional-moment bound, with its entropy factor
and threshold dependence explicit. The event is genuinely measurable. -/
theorem exists_uniform_fractional_event {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (A t : ℝ) (hA : 1 ≤ A) (ht : 0 < t) (hwindow : (n:ℝ) ≤ A*(d:ℝ)^2) :
    ∃ E : Set (Fin n → BMQuadraticSpectral.Euclid d), MeasurableSet E ∧
      (∀ x ∈ E, ∀ T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d,
        T.toLinearMap.IsSymmetric → ‖T‖ ≤ 1 →
        (∑ i, |normalizedQuadratic T (x i)|^((4:ℝ)/3)) ≤ 4*t*n) ∧
      (gaussianSampleLaw d n).real Eᶜ ≤
        (5:ℝ)^(d*d)*(8*exp 1*(32+2304*A)/t)^n := by
  classical
  obtain ⟨s, hs, hcard, hnet⟩ := exists_symmetric_operator_half_net d
  let F : SymOp d → (Fin n → BMQuadraticSpectral.Euclid d) → ℝ :=
    fun T x => ∑ i, |normalizedQuadratic T.val (x i)|^((4:ℝ)/3)
  let E : Set (Fin n → BMQuadraticSpectral.Euclid d) := {x | ∀ T ∈ s, F T x ≤ t*n}
  have hm (T : SymOp d) : Measurable (F T) :=
    Finset.measurable_sum _ (fun i _ =>
      (((continuous_normalizedQuadratic T.val).measurable.comp (measurable_pi_apply i)).abs.pow_const _))
  have hE : MeasurableSet E := measurableSet_finset_forall_le s F (t*n) hm
  refine ⟨E, hE, ?_, ?_⟩
  · intro x hx T hT hN
    let U : SymOp d := ⟨T, hT⟩
    have h := empirical_quadratic_sum_le_of_half_net x s hnet (t*n) (by positivity) hx U hN
    simpa only [U, mul_assoc] using h
  · have hc : Eᶜ = ⋃ T ∈ s,
        {x | t*n < ∑ i, |normalizedQuadratic T.val (x i)|^((4:ℝ)/3)} := by
      ext x
      simp [E, F]
    rw [hc]
    calc
      _ ≤ ∑ T ∈ s, (gaussianSampleLaw d n).real
          {x | t*n < ∑ i, |normalizedQuadratic T.val (x i)|^((4:ℝ)/3)} :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _T ∈ s, (8*exp 1*(32+2304*A)/t)^n := by
        apply Finset.sum_le_sum
        intro T hT
        exact normalizedQuadratic_empirical_tail hd hn T.val T.property (hs T hT).le A t hA ht hwindow
      _ = (s.card:ℝ)*(8*exp 1*(32+2304*A)/t)^n := by simp
      _ ≤ (5:ℝ)^(d*d)*(8*exp 1*(32+2304*A)/t)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Uniform 4/3 empirical integrability, with exponentially small exceptional
probability throughout the proportional d² sample window. This is the BM
uniform-integrability dependency under the actual Gaussian law. -/
theorem exists_uniform_fractional_constant (a A : ℝ) (ha : 0 < a) (hA : 1 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ d n : ℕ, 0 < d → 0 < n →
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∃ E : Set (Fin n → BMQuadraticSpectral.Euclid d), MeasurableSet E ∧
        (∀ x ∈ E, ∀ T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d,
          T.toLinearMap.IsSymmetric → ‖T‖ ≤ 1 →
          (∑ i, |normalizedQuadratic T (x i)|^((4:ℝ)/3)) ≤ K*n) ∧
        (gaussianSampleLaw d n).real Eᶜ ≤ exp (-(n:ℝ)) := by
  let C : ℝ := 8*exp 1*(32+2304*A)
  let c : ℝ := 1+log 5/a
  let t : ℝ := C*exp c
  have hC : 0 < C := by dsimp [C]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨4*t, by positivity, ?_⟩
  intro d n hd hn hlow hhigh
  obtain ⟨E, hE, hgood, hbad⟩ := exists_uniform_fractional_event hd hn A t hA ht hhigh
  refine ⟨E, hE, hgood, hbad.trans ?_⟩
  have hratio : 8*exp 1*(32+2304*A)/t = exp (-c) := by
    dsimp [t, C]
    rw [Real.exp_neg]
    field_simp
  rw [hratio]
  have hfive : (5:ℝ)^(d*d) = exp ((d:ℝ)^2*log 5) := by
    rw [show (d:ℝ)^2 = (d*d:ℕ) by push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hfive, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ log 5 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlow (div_nonneg hlog ha.le)
  dsimp [c]
  have hcancel : (log 5/a)*(a*(d:ℝ)^2) = log 5*(d:ℝ)^2 := by field_simp
  rw [hcancel] at hh
  nlinarith

#print axioms exists_uniform_fractional_event
#print axioms exists_uniform_fractional_constant
end BMFourThirdMoment
