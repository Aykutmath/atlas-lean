import AHHRadialMean
import Mathlib.MeasureTheory.Integral.Pi

/-! Jensen bridge for the actual normalized complex radial factors.
The radii are the explicit measures obtained from polar Haar decomposition,
not abstract random variables whose means or independence are assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace AHHRadial

abbrev ComplexSpace (h : ℕ) := EuclideanSpace ℂ (Fin h)

def radiusPairLaw (h : ℕ) : Measure (Radius × Radius) :=
  (radiusLaw (volume : Measure (ComplexSpace h)) h).prod
    (radiusLaw (volume : Measure (ComplexSpace h)) h)

def radiiLaw (n h : ℕ) : Measure (Fin n → Radius × Radius) :=
  Measure.pi (fun _ => radiusPairLaw h)

def radialWeight {n : ℕ} (r : Fin n → Radius × Radius) (i : Fin n) : ℝ :=
  ((r i).1 : ℝ)^2 * ((r i).2 : ℝ)^2

theorem radiusPairLaw_probability (h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (radiusPairLaw h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := radiusLaw_probability (volume : Measure (ComplexSpace h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  unfold radiusPairLaw
  infer_instance

theorem radiiLaw_probability (n h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (radiiLaw n h) := by
  letI := radiusPairLaw_probability h hh
  unfold radiiLaw
  infer_instance

theorem radialWeight_integrable (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    Integrable (fun r => radialWeight r i) (radiiLaw n h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := radiusPairLaw_probability h hh
  have hi := radiusLaw_integrable_sq (volume : Measure (ComplexSpace h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  exact integrable_comp_eval (μ := fun _ : Fin n => radiusPairLaw h) (i := i)
    (hi.mul_prod hi)

theorem radialWeight_mean (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    (∫ r, radialWeight r i ∂radiiLaw n h) = 1 := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := radiusPairLaw_probability h hh
  simp only [radiiLaw, radialWeight]
  rw [integral_comp_eval (μ := fun _ : Fin n => radiusPairLaw h) (i := i) (f := fun z : Radius × Radius => (z.1 : ℝ)^2 * (z.2 : ℝ)^2)
      (by fun_prop), radiusPairLaw,
    integral_prod_mul (fun r : Radius => (r : ℝ)^2) (fun r : Radius => (r : ℝ)^2), complex_radius_mean_sq h hh, one_mul]

/-- Conditional Jensen for a finite sum of arbitrary Banach-space operators.
In applications A i is the rank-one projector of the i-th unit product state. -/
theorem conditional_jensen {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] (n h : ℕ) (hh : 0 < h) (A : Fin n → B) :
    ‖∑ i, A i‖ ≤ ∫ r, ‖∑ i, radialWeight r i • A i‖ ∂radiiLaw n h := by
  have hi (i : Fin n) : Integrable (fun r => radialWeight r i • A i) (radiiLaw n h) :=
    (radialWeight_integrable n h hh i).smul_const (A i)
  have he : (∫ r, ∑ i, radialWeight r i • A i ∂radiiLaw n h) = ∑ i, A i := by
    rw [integral_finset_sum _ (fun i _ => hi i)]
    simp_rw [integral_smul_const, radialWeight_mean n h hh, one_smul]
  rw [← he]
  exact norm_integral_le_integral_norm _

/-- Integral Jensen after averaging the unit directions.  Integrability is
an ordinary analytic hypothesis on the deterministic direction function;
all radial moments and independence have already been discharged. -/
theorem integrated_jensen {B D : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace D] (ν : Measure D) [SFinite ν]
    (n h : ℕ) (hh : 0 < h) (A : D → Fin n → B)
    (hA : ∀ i, Integrable (fun d => A d i) ν) :
    (∫ d, ‖∑ i, A d i‖ ∂ν) ≤
      ∫ p, ‖∑ i, radialWeight p.1 i • A p.2 i‖ ∂(radiiLaw n h).prod ν := by
  letI := radiiLaw_probability n h hh
  have hi : Integrable (fun p : (Fin n → Radius × Radius) × D =>
      ∑ i, radialWeight p.1 i • A p.2 i) ((radiiLaw n h).prod ν) :=
    integrable_finset_sum _ (fun i _ => (radialWeight_integrable n h hh i).smul_prod (hA i))
  rw [integral_prod_symm _ hi.norm]
  apply integral_mono (integrable_finset_sum _ (fun i _ => hA i)).norm
    hi.norm.integral_prod_right
  intro d
  exact conditional_jensen n h hh (A d)

#print axioms radialWeight_mean
#print axioms conditional_jensen
#print axioms integrated_jensen
end AHHRadial
