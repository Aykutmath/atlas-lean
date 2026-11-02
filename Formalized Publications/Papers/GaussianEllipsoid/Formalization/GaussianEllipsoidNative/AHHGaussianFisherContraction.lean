import AHHGaussianSemigroup
import AHHGaussianEnergyJensen
import AHHGaussianLogTest

/-! Rotation identities and the exact Fisher-information contraction. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open AHHGaussianSemigroup AHHGaussianEnergyJensen
open scoped BigOperators BoundedContinuousFunction Topology

namespace AHHGaussianFisherContraction
variable {d : ℕ}

theorem first_preserving (t : ℝ) : MeasurePreserving (first (d := d) t) (γ₂ d) (γ d) :=
  (measurePreserving_fst (μ := γ d) (ν := γ d)).comp (rotate_preserving t)

theorem integral_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ x, f (T x) ∂μ) = ∫ y, f y ∂ν := by
  have h := integral_map hT.measurable.aemeasurable (f := f) (by rwa [hT.map_eq])
  rw [hT.map_eq] at h
  exact h.symm

theorem integral_average (f : Raw d →ᵇ ℝ) (t : ℝ) :
    (∫ x, average f t x ∂γ d) = ∫ x, f x ∂γ d := by
  have hi := (first_preserving (d := d) t).integrable_comp_of_integrable (integrable_bounded f)
  unfold AHHGaussianSemigroup.average
  change (∫ x, ∫ y, (f ∘ first t) (x,y) ∂γ d ∂γ d) = _
  rw [← integral_prod _ hi]
  exact integral_preserving (first_preserving t) f.continuous.aestronglyMeasurable

theorem first_neg_rotate (t : ℝ) (z : Raw d × Raw d) :
    first (-t) (rotate t z) = z.1 := by
  simpa only [neg_neg] using first_rotate_neg (-t) z

theorem expected_pathVelocity_unrotated (F G : SmoothTest (Fin d)) (t : ℝ) :
    (∫ z, pathVelocity F G t z ∂γ₂ d) =
      -Real.sin t * ∫ z, ∑ i, F.gradient i z.1 * G.gradient i (first t z) ∂γ₂ d := by
  rw [expected_pathVelocity]
  congr 1
  let b : (Raw d × Raw d) →ᵇ ℝ := ∑ i,
    ((F.gradient i).compContinuous (firstMap (-t))) * ((G.gradient i).compContinuous fstMap)
  have h := integral_preserving (rotate_preserving (d := d) t) b.continuous.aestronglyMeasurable
  simp only [b, BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.compContinuous_apply, firstMap, fstMap,
    ContinuousMap.coe_mk] at h
  simp_rw [first_neg_rotate] at h
  exact h.symm

theorem integrable_energy_first (f g : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) (t : ℝ) (x : Raw d) :
    Integrable (fun y => (g (first t (x,y)))^2 / f (first t (x,y))) (γ d) := by
  let m : C(Raw d, Raw d) := ⟨fun y => first t (x,y), by unfold first; fun_prop⟩
  exact boundedContinuous_integrable_energy (γ d) (f.compContinuous m) (g.compContinuous m)
    hc (fun y => hf _)

theorem average_energy_pointwise (f g : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) (t : ℝ) (x : Raw d) :
    (average g t x)^2 / average f t x ≤
      ∫ y, (g (first t (x,y)))^2 / f (first t (x,y)) ∂γ d := by
  exact integral_sq_div_le (γ d) _ _ (ae_of_all _ fun y => hc.trans_le (hf _))
    (integrable_first f t x) (integrable_first g t x)
    (integrable_energy_first f g hc hf t x) (hc.trans_le (average_lower f hf t x))

theorem average_energy_integral_le (f g : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ f x) (t : ℝ) :
    (∫ x, (average g t x)^2 / average f t x ∂γ d) ≤
      ∫ x, (g x)^2 / f x ∂γ d := by
  have he := boundedContinuous_integrable_energy (γ d) f g hc hf
  have he' := (first_preserving (d := d) t).integrable_comp_of_integrable he
  have ha := boundedContinuous_integrable_energy (γ d) (averageBounded f t)
    (averageBounded g t) hc (average_lower f hf t)
  have hi := integral_mono ha he'.integral_prod_left (average_energy_pointwise f g hc hf t)
  rw [← integral_prod _ he'] at hi
  exact hi.trans_eq (integral_preserving (first_preserving t) he.aestronglyMeasurable)

theorem average_fisher_integral_le (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ F.value x) (t : ℝ) :
    (∫ x, (∑ i, (average (F.gradient i) t x)^2) / average F.value t x ∂γ d) ≤
      ∫ x, (∑ i, (F.gradient i x)^2) / F.value x ∂γ d := by
  simp_rw [Finset.sum_div]
  have ha (i : Fin d) : Integrable (fun x => (average (F.gradient i) t x)^2 /
      average F.value t x) (γ d) :=
    boundedContinuous_integrable_energy (γ d) (averageBounded F.value t)
      (averageBounded (F.gradient i) t) hc (average_lower F.value hf t)
  have he (i : Fin d) : Integrable (fun x => (F.gradient i x)^2 / F.value x) (γ d) :=
    boundedContinuous_integrable_energy (γ d) F.value (F.gradient i) hc hf
  rw [integral_finsetSum _ (fun i _ => ha i), integral_finsetSum _ (fun i _ => he i)]
  exact Finset.sum_le_sum fun i _ => average_energy_integral_le F.value (F.gradient i) hc hf t

theorem entropy_velocity_eq (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ F.value x) (t : ℝ) :
    (∫ z, pathVelocity (AHHGaussianLogTest.logOneTest (averageTest F t) hc
      (average_lower F.value hf t)) F t z ∂γ₂ d) =
      -Real.sin t * Real.cos t *
        ∫ x, (∑ i, (average (F.gradient i) t x)^2) / average F.value t x ∂γ d := by
  let G := AHHGaussianLogTest.logOneTest (averageTest F t) hc (average_lower F.value hf t)
  rw [expected_pathVelocity_unrotated]
  have hi : Integrable (fun z : Raw d × Raw d =>
      ∑ i, G.gradient i z.1 * F.gradient i (first t z)) (γ₂ d) := by
    let b : (Raw d × Raw d) →ᵇ ℝ := ∑ i,
      ((G.gradient i).compContinuous fstMap) * ((F.gradient i).compContinuous (firstMap t))
    convert! BMRowInterpolation.integrable_bounded b using 1
    funext z
    simp [b, fstMap, firstMap]
  have hpoint (x : Raw d) : (∫ y, ∑ i, G.gradient i x * F.gradient i (first t (x,y)) ∂γ d) =
      Real.cos t * ((∑ i, (average (F.gradient i) t x)^2) / average F.value t x) := by
    rw [integral_finsetSum _ (fun i _ => (integrable_first (F.gradient i) t x).const_mul
      (G.gradient i x))]
    simp only [integral_const_mul]
    simp only [G, AHHGaussianLogTest.logOneTest_gradient, averageTest,
      BoundedContinuousFunction.smul_apply, averageBounded_apply, smul_eq_mul]
    change (∑ i, (Real.cos t * average (F.gradient i) t x / average F.value t x) *
      average (F.gradient i) t x) = _
    simp only [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change -Real.sin t * (∫ z, ∑ i, G.gradient i z.1 * F.gradient i (first t z) ∂γ₂ d) = _
  rw [integral_prod _ hi]
  simp_rw [hpoint]
  rw [integral_const_mul]
  ring

#print axioms entropy_velocity_eq
#print axioms expected_pathVelocity_unrotated
#print axioms average_fisher_integral_le
end AHHGaussianFisherContraction
