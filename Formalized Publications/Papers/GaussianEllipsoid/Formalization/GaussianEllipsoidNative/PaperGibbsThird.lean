import BMFiniteGibbsHessian
set_option maxHeartbeats 2000000
noncomputable section
open BMFiniteGibbsTest BMFiniteGibbsHessian BMGaussianSmoothStein
open scoped BigOperators BoundedContinuousFunction
namespace PaperGibbsThird
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A bounded C³ loss with the literal analytic derivatives. Zero prior weights
are permitted by the inherited finite probability-law interface. -/
structure Data3 (κ : Type*) [Fintype κ] extends Data2 κ where
  potentialThird : ℝ →ᵇ ℝ
  hasDeriv_third : ∀ t, HasDerivAt potentialSecond (potentialThird t) t

def probabilityPartial (D : Data κ) (a c : κ) (y : κ → ℝ) : ℝ :=
  -D.beta * probability D y a * D.potentialDeriv (y a) * (if c = a then 1 else 0) +
    D.beta * probability D y a * (probability D y c * D.potentialDeriv (y c))

theorem hasDerivAt_probability_coordinate (D : Data κ) (a c : κ) (y : κ → ℝ) :
    HasDerivAt (fun t => probability D (Function.update y c t) a)
      (probabilityPartial D a c y) (y c) := by
  have hp : HasDerivAt (fun t => Function.update y c t)
      (fun b => if c = b then 1 else 0) (y c) :=
    hasDerivAt_pi.mpr fun b => by
      by_cases h : c = b
      · subst b
        simpa using! hasDerivAt_id (y c)
      · simpa [Function.update_of_ne (Ne.symm h), h] using hasDerivAt_const (y c) (y b)
  have h := (hasFDerivAt_probability D a y).comp_hasDerivAt_of_eq (y c) hp
    (by simp)
  simpa [probabilityPartial, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp_def] using! h

/-- Exact ordered coordinate third derivative of log Z. This sparse form keeps
all coincident-index terms, including the diagonal contribution of ℓ'''. -/
def third (D : Data3 κ) (a b c : κ) (y : κ → ℝ) : ℝ :=
  (if a = b then
    probabilityPartial D.toData a c y *
      (D.beta^2 * (D.potentialDeriv (y a))^2 - D.beta * D.potentialSecond (y a)) +
    probability D.toData y a *
      (2 * D.beta^2 * D.potentialDeriv (y a) * D.potentialSecond (y a) -
        D.beta * D.potentialThird (y a)) * (if c = a then 1 else 0)
    else 0) - D.beta^2 *
    ((probabilityPartial D.toData a c y * probability D.toData y b +
      probability D.toData y a * probabilityPartial D.toData b c y) *
        D.potentialDeriv (y a) * D.potentialDeriv (y b) +
      probability D.toData y a * probability D.toData y b *
        (D.potentialSecond (y a) * (if c = a then 1 else 0) * D.potentialDeriv (y b) +
          D.potentialDeriv (y a) * D.potentialSecond (y b) * (if c = b then 1 else 0)))

theorem hasDerivAt_hessian_coordinate (D : Data3 κ) (a b c : κ) (y : κ → ℝ) :
    HasDerivAt (fun t => hessian D.toData2 a b (Function.update y c t))
      (third D a b c y) (y c) := by
  have hu (j : κ) : HasDerivAt (fun t => Function.update y c t j)
      (if c = j then 1 else 0) (y c) := by
    by_cases h : c = j
    · subst j; simpa using! hasDerivAt_id (y c)
    · simpa [Function.update_of_ne (Ne.symm h), h] using hasDerivAt_const (y c) (y j)
  have hl (j : κ) := (D.hasDeriv_second (y j)).comp_of_eq (y c) (hu j) (by simp)
  have hs (j : κ) := (D.hasDeriv_third (y j)).comp_of_eq (y c) (hu j) (by simp)
  have hp (j : κ) := hasDerivAt_probability_coordinate D.toData j c y
  have hfirst := (hp a).mul (((hl a).pow 2).const_mul (D.beta^2) |>.sub ((hs a).const_mul D.beta))
  have hsecond := ((((hp a).mul (hp b)).const_mul (D.beta^2)).mul (hl a)).mul (hl b)
  by_cases hab : a = b
  · have hh := hfirst.sub hsecond
    convert! hh using 1 <;> (try funext t) <;>
      simp [hessian, third, hab, Function.comp_def, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] <;>
      (try split_ifs) <;> ring <;> simp
  · have hh := (hasDerivAt_const (y c) (0 : ℝ)).sub hsecond
    convert! hh using 1 <;> (try funext t) <;>
      simp [hessian, third, hab, Function.comp_def, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] <;>
      (try split_ifs) <;> ring <;> simp

/-- Coordinate derivatives identify the full derivative once differentiability
is proved independently. No differentiability is inferred from partials alone. -/
theorem hasFDerivAt_of_coordinate_derivatives (f : (κ → ℝ) → ℝ)
    (y : κ → ℝ) (g : κ → ℝ) (hf : DifferentiableAt ℝ f y)
    (hg : ∀ c, HasDerivAt (fun t => f (Function.update y c t)) (g c) (y c)) :
    HasFDerivAt f (∑ c, (g c) •
      (ContinuousLinearMap.proj c : (κ → ℝ) →L[ℝ] ℝ)) y := by
  have hv (c : κ) : HasDerivAt (fun t => Function.update y c t)
      (Pi.single c 1) (y c) := by
    apply hasDerivAt_pi.mpr
    intro b
    by_cases h : c = b
    · subst b
      simpa using! hasDerivAt_id (y c)
    · simpa [Function.update_of_ne (Ne.symm h), Pi.single_apply, h, Ne.symm h] using!
        hasDerivAt_const (y c) (y b)
  have he (c : κ) : (fderiv ℝ f y) (Pi.single c 1) = g c := by
    have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq (y c) (hv c) (by simp)
    exact hh.unique (hg c)
  have hl : fderiv ℝ f y = ∑ c, (g c) •
      (ContinuousLinearMap.proj c : (κ → ℝ) →L[ℝ] ℝ) := by
    ext z
    have hz : z = ∑ c, (z c) • Pi.single c (1 : ℝ) := by
      ext b
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    conv_lhs => rw [hz]
    simp [map_sum, map_smul, he, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, mul_comm]
  rw [← hl]
  exact hf.hasFDerivAt

/-- The actual bounded C³ finite Gibbs family has the full Frechet third
coordinate tensor. Only ordinary scalar loss derivatives are input data. -/
theorem hasFDerivAt_hessian (D : Data3 κ) (a b : κ) (y : κ → ℝ) :
    HasFDerivAt (hessian D.toData2 a b)
      (∑ c, third D a b c y •
        (ContinuousLinearMap.proj c : (κ → ℝ) →L[ℝ] ℝ)) y := by
  apply hasFDerivAt_of_coordinate_derivatives
  · have hp (j : κ) := (hasFDerivAt_probability D.toData j y).differentiableAt
    have hl (j : κ) : DifferentiableAt ℝ (fun z : κ → ℝ => D.potentialDeriv (z j)) y :=
      (D.hasDeriv_second (y j)).differentiableAt.comp y
        (hasFDerivAt_apply (𝕜 := ℝ) j y).differentiableAt
    have hs (j : κ) : DifferentiableAt ℝ (fun z : κ → ℝ => D.potentialSecond (z j)) y :=
      (D.hasDeriv_third (y j)).differentiableAt.comp y
        (hasFDerivAt_apply (𝕜 := ℝ) j y).differentiableAt
    unfold hessian
    split_ifs <;> fun_prop
  · exact fun c => hasDerivAt_hessian_coordinate D a b c y

/-- Full replica expansion, retaining each of the three covariance terms
and the five cumulant terms. The coefficient mass is 1,6,6 after division
by −βn to obtain the paper's normalized cavity free energy. -/
def replicaThird (D : Data3 κ) (a b c : κ) (y : κ → ℝ) : ℝ :=
  -D.beta * (if a = b ∧ a = c then probability D.toData y a * D.potentialThird (y a) else 0) +
  D.beta^2 * (
    (if a = b ∧ a = c then 3 * probability D.toData y a * D.potentialSecond (y a) * D.potentialDeriv (y a) else 0) -
    (if a = b then probability D.toData y a * probability D.toData y c * D.potentialSecond (y a) * D.potentialDeriv (y c) else 0) -
    (if a = c then probability D.toData y a * probability D.toData y b * D.potentialSecond (y a) * D.potentialDeriv (y b) else 0) -
    (if b = c then probability D.toData y a * probability D.toData y b * D.potentialDeriv (y a) * D.potentialSecond (y b) else 0)) -
  D.beta^3 * (
    (if a = b ∧ a = c then probability D.toData y a * (D.potentialDeriv (y a))^3 else 0) -
    (if a = b then probability D.toData y a * probability D.toData y c * (D.potentialDeriv (y a))^2 * D.potentialDeriv (y c) else 0) -
    (if a = c then probability D.toData y a * probability D.toData y b * (D.potentialDeriv (y a))^2 * D.potentialDeriv (y b) else 0) -
    (if b = c then probability D.toData y a * probability D.toData y b * D.potentialDeriv (y a) * (D.potentialDeriv (y b))^2 else 0) +
    2 * probability D.toData y a * probability D.toData y b * probability D.toData y c *
      D.potentialDeriv (y a) * D.potentialDeriv (y b) * D.potentialDeriv (y c))

theorem third_eq_replicaThird (D : Data3 κ) (a b c : κ) (y : κ → ℝ) :
    third D a b c y = replicaThird D a b c y := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [third, replicaThird, probabilityPartial]
      ring
    · simp [third, replicaThird, probabilityPartial, hac, Ne.symm hac]
      ring
  · by_cases hac : a = c
    · subst c
      simp [third, replicaThird, probabilityPartial, hab, Ne.symm hab]
      ring
    · by_cases hbc : b = c
      · subst c
        simp [third, replicaThird, probabilityPartial, hab, Ne.symm hab]
        ring
      · simp [third, replicaThird, probabilityPartial, hab, hac, hbc,
          Ne.symm hab, Ne.symm hac, Ne.symm hbc]
        ring

#print axioms hasDerivAt_probability_coordinate
#print axioms hasDerivAt_hessian_coordinate
end PaperGibbsThird
