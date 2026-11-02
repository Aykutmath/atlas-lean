import BMSmoothSteinBounds

/-! Finite Gibbs log-partitions form a concrete nonpolynomial test class for the
actual Gaussian quadratic Stein identity. All positivity, boundedness, and
calculus obligations are proved from a finite probability vector and a bounded
C¹ scalar potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMSmoothSteinBounds
open scoped BigOperators BoundedContinuousFunction

namespace BMFiniteGibbsTest
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Literal finite-prior Gibbs data; no probabilistic comparison is assumed. -/
structure Data (κ : Type*) [Fintype κ] where
  weight : κ → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  potential : ℝ →ᵇ ℝ
  potentialDeriv : ℝ →ᵇ ℝ
  hasDeriv : ∀ t, HasDerivAt potential (potentialDeriv t) t
  beta : ℝ
  beta_nonneg : 0 ≤ beta

def partition (D : Data κ) (y : κ → ℝ) : ℝ :=
  ∑ a, D.weight a * Real.exp (-D.beta * D.potential (y a))

def probability (D : Data κ) (y : κ → ℝ) (a : κ) : ℝ :=
  (D.weight a * Real.exp (-D.beta * D.potential (y a))) / partition D y

theorem partition_lower (D : Data κ) (y : κ → ℝ) :
    Real.exp (-D.beta * ‖D.potential‖) ≤ partition D y := by
  calc
    _ = ∑ a, D.weight a * Real.exp (-D.beta * ‖D.potential‖) := by
      rw [← Finset.sum_mul, D.weight_sum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have h := (D.potential.norm_coe_le_norm (y a))
        rw [Real.norm_eq_abs] at h
        have hb := D.beta_nonneg
        nlinarith [(abs_le.mp h).2])) (D.weight_nonneg a)

theorem partition_upper (D : Data κ) (y : κ → ℝ) :
    partition D y ≤ Real.exp (D.beta * ‖D.potential‖) := by
  calc
    _ ≤ ∑ a, D.weight a * Real.exp (D.beta * ‖D.potential‖) :=
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have h := (D.potential.norm_coe_le_norm (y a))
          rw [Real.norm_eq_abs] at h
          have hb := D.beta_nonneg
          nlinarith [(abs_le.mp h).1])) (D.weight_nonneg a)
    _ = _ := by rw [← Finset.sum_mul, D.weight_sum, one_mul]

theorem partition_pos (D : Data κ) (y : κ → ℝ) : 0 < partition D y :=
  (Real.exp_pos _).trans_le (partition_lower D y)

theorem probability_nonneg (D : Data κ) (y : κ → ℝ) (a : κ) :
    0 ≤ probability D y a :=
  div_nonneg (mul_nonneg (D.weight_nonneg a) (Real.exp_pos _).le) (partition_pos D y).le

theorem probability_le_one (D : Data κ) (y : κ → ℝ) (a : κ) :
    probability D y a ≤ 1 := by
  apply (div_le_one (partition_pos D y)).mpr
  unfold partition
  exact Finset.single_le_sum (fun b _ => mul_nonneg (D.weight_nonneg b) (Real.exp_pos (-D.beta * D.potential (y b))).le)
    (Finset.mem_univ a)

theorem probability_sum (D : Data κ) (y : κ → ℝ) :
    ∑ a, probability D y a = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos D y))

theorem exp_potential_continuous (D : Data κ) (a : κ) :
    Continuous (fun y : κ → ℝ => Real.exp (-D.beta * D.potential (y a))) :=
  Real.continuous_exp.comp (continuous_const.mul (D.potential.continuous.comp (continuous_apply a)))

theorem partition_continuous (D : Data κ) : Continuous (partition D) := by
  apply continuous_finset_sum
  intro a ha
  exact continuous_const.mul (exp_potential_continuous D a)

def logPartition (D : Data κ) (y : κ → ℝ) : ℝ := Real.log (partition D y)

def gradient (D : Data κ) (a : κ) (y : κ → ℝ) : ℝ :=
  -D.beta * probability D y a * D.potentialDeriv (y a)

theorem logPartition_continuous (D : Data κ) : Continuous (logPartition D) :=
  (partition_continuous D).log (fun y => ne_of_gt (partition_pos D y))

theorem logPartition_norm_le (D : Data κ) (y : κ → ℝ) :
    ‖logPartition D y‖ ≤ D.beta * ‖D.potential‖ := by
  have hlo := Real.log_le_log (Real.exp_pos _) (partition_lower D y)
  have hhi := Real.log_le_log (partition_pos D y) (partition_upper D y)
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by simpa [logPartition] using hlo, hhi⟩

theorem gradient_continuous (D : Data κ) (a : κ) : Continuous (gradient D a) := by
  unfold gradient probability
  exact (continuous_const.mul
    ((continuous_const.mul (exp_potential_continuous D a)).div
      (partition_continuous D) (fun y => ne_of_gt (partition_pos D y)))).mul
    (D.potentialDeriv.continuous.comp (continuous_apply a))

theorem gradient_norm_le (D : Data κ) (a : κ) (y : κ → ℝ) :
    ‖gradient D a y‖ ≤ D.beta * ‖D.potentialDeriv‖ := by
  calc
    _ = D.beta * probability D y a * ‖D.potentialDeriv (y a)‖ := by
      simp only [gradient, norm_mul, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg D.beta_nonneg, abs_of_nonneg (probability_nonneg D y a)]
    _ ≤ D.beta * 1 * ‖D.potentialDeriv‖ :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (probability_le_one D y a) D.beta_nonneg)
        (D.potentialDeriv.norm_coe_le_norm _) (norm_nonneg _) (by simpa using D.beta_nonneg)
    _ = _ := by ring

/-- The finite Gibbs log-partition is uniformly bounded. -/
def boundedLogPartition (D : Data κ) : (κ → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (logPartition D)
    (logPartition_continuous D) (D.beta * ‖D.potential‖) (logPartition_norm_le D)

def boundedGradient (D : Data κ) (a : κ) : (κ → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gradient D a)
    (gradient_continuous D a) (D.beta * ‖D.potentialDeriv‖) (gradient_norm_le D a)

theorem boundedGradient_norm_le (D : Data κ) (a : κ) :
    ‖boundedGradient D a‖ ≤ D.beta * ‖D.potentialDeriv‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg D.beta_nonneg (norm_nonneg _)) _

/-- Exact Frechet derivative of the finite Gibbs partition function. -/
theorem hasFDerivAt_partition (D : Data κ) (y : κ → ℝ) :
    HasFDerivAt (partition D)
      (∑ a, (D.weight a * Real.exp (-D.beta * D.potential (y a)) *
        (-D.beta) * D.potentialDeriv (y a)) •
          (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
  apply HasFDerivAt.fun_sum
  intro a ha
  have hp : HasFDerivAt (fun z : κ → ℝ => D.potential (z a))
      (D.potentialDeriv (y a) • (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
    simpa using! (D.hasDeriv (y a)).comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) a y)
  have he := ((hp.const_mul (-D.beta)).exp).const_mul (D.weight a)
  convert! he using 1
  ext z
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Exact Gibbs gradient, including the normalization denominator. -/
theorem hasFDerivAt_logPartition (D : Data κ) (y : κ → ℝ) :
    HasFDerivAt (logPartition D)
      (∑ a, gradient D a y • (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
  have h := (hasFDerivAt_partition D y).log (ne_of_gt (partition_pos D y))
  convert! h using 1
  ext z
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum, gradient, probability]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A concrete Gibbs log-partition is an admissible smooth nonpolynomial test. -/
def smoothTest (D : Data κ) : SmoothTest κ where
  value := boundedLogPartition D
  gradient := boundedGradient D
  hasFDeriv := hasFDerivAt_logPartition D

/-- A finite Gibbs log-partition has a genuine d⁻¹/² quadratic Stein error.
The displayed square bound is explicit in the finite support size, spectral
bound, inverse temperature, and scalar derivative bound. -/
theorem finiteGibbs_stein_discrepancy_sq_le
    (D : Data κ) (d : ℕ) (hd : 0 < d)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a)
    (a : κ) (K : ℝ) (hAnorm : ∀ b, spectralNorm (A b) ≤ K) :
    (boundedExpectation (composedTest (smoothTest D) (fun b => normalizedQuadratic d (A b)))
        (normalizedQuadratic d (A a)) -
      ∑ b, (2 / (d : ℝ) * Matrix.trace (A a*A b)) *
        boundedExpectation (composedGradient (smoothTest D)
          (fun b => normalizedQuadratic d (A b)) b) 1)^2 ≤
      8 * (Fintype.card κ : ℝ)^2 * K^4 * (D.beta * ‖D.potentialDeriv‖)^2 / d := by
  have hnorm (b : κ) : spectralNorm (A b)^2 ≤ K^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hAnorm b) 2
  have hg (b : κ) : ‖(smoothTest D).gradient b‖^2 ≤ (D.beta * ‖D.potentialDeriv‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (boundedGradient_norm_le D b) 2
  calc
    _ ≤ (Fintype.card κ : ℝ) * ∑ b,
        (8 / (d : ℝ) * spectralNorm (A a)^2 * spectralNorm (A b)^2) *
          ‖(smoothTest D).gradient b‖^2 :=
      smooth_normalized_vector_discrepancy_sq_le d hd (smoothTest D) A hA a
    _ ≤ (Fintype.card κ : ℝ) * ∑ _b : κ,
        (8 / (d : ℝ) * K^2 * K^2) * (D.beta * ‖D.potentialDeriv‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul _ (hg b) (sq_nonneg _) (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hnorm a) (by positivity))
        (hnorm b) (sq_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

#print axioms finiteGibbs_stein_discrepancy_sq_le
#print axioms smoothTest
#print axioms hasFDerivAt_logPartition
end BMFiniteGibbsTest
