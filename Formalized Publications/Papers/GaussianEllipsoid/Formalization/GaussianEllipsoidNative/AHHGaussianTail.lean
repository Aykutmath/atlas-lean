import AHHGaussianModelBridge
import AHHGaussianTailArithmetic
import AHHComplexCovarianceBounds
import GaussianTensorCovarianceTail

/-! A fully independent proof of the constant operator-norm tail at manuscript
line 2750.  This proof uses the previously verified real Gaussian tensor moments
and four exact real marginals; it does not use AHH equation (11), a Haar law,
or an assumed sharp edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianTensorTrace
open AHHAlgebraBridges
open scoped BigOperators
namespace AHHGaussian

def actualComplexCovariance (n h : ℕ) (s t : Bool) (x : FourEntries n h) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ :=
  complexCov n h (fun i j => x.1.1 (i,j)) (fun i j => x.1.2 (i,j))
    (fun i j => x.2.1 (i,j)) (fun i j => x.2.2 (i,j)) s t

/-- Identification of the norm-tail matrix with the sum of projectors of the
actual iid normalized complex Gaussian product states. -/
theorem actualComplexCovariance_eq_sum_projectors (n h : ℕ) (s t : Bool)
    (x : FourEntries n h) :
    actualComplexCovariance n h s t x =
      ∑ i : Fin n, AHHAlgebraBridges.projector
        (fun p => actualProductStates n h s t x i p) := by
  unfold actualComplexCovariance complexCov
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext p
  exact (actualProductStates_eq_productState n h s t x i p).symm

def realCovarianceNorm (n h : ℕ) (b c : Bool) (x : FourEntries n h) : ℝ :=
  ‖matrixCLM (tensorGaussianCovariance n h (selectCopy b x.1, selectCopy c x.2))‖

theorem tensor_covariance_norm_continuous (n h : ℕ) :
    Continuous (fun z => ‖matrixCLM (tensorGaussianCovariance n h z)‖) := by
  have hcov : Continuous (tensorGaussianCovariance n h) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    simp only [tensorGaussianCovariance, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]
    fun_prop
  have hclm : Continuous (matrixCLM (α := Fin h × Fin h) (β := Fin h × Fin h)) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin h × Fin h) (n := Fin h × Fin h)).trans
      LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional
  exact (hclm.comp hcov).norm

/-- Each of the four covariance tails is transported through a proved equality
of actual measures. No independence between the four events is needed. -/
theorem realCovarianceNorm_tail (n q h : ℕ) (hq : 1 ≤ q) (hh : 0 < h)
    (hn : n ≤ q^2) (b c : Bool) :
    (fourGaussianLaw n h).real
      {x | 2048 * (h+q : ℕ)^2 < realCovarianceNorm n h b c x} ≤
      (h : ℝ)^2 / (2 : ℝ)^h := by
  have hmeas : MeasurableSet {z | 2048 * (h+q : ℕ)^2 <
      ‖matrixCLM (tensorGaussianCovariance n h z)‖} :=
    (isOpen_lt continuous_const (tensor_covariance_norm_continuous n h)).measurableSet
  have he := map_measureReal_apply
    (μ := fourGaussianLaw n h)
    ((measurable_selectCopy n h b).comp measurable_fst |>.prodMk
      ((measurable_selectCopy n h c).comp measurable_snd)) hmeas
  simp only [Function.comp_apply] at he
  rw [fourGaussianLaw_map_select] at he
  change (tensorGaussianLaw n h).real {z | 2048 * (h+q : ℕ)^2 <
      ‖matrixCLM (tensorGaussianCovariance n h z)‖} = _ at he
  rw [show (fourGaussianLaw n h).real {x | 2048 * (h+q : ℕ)^2 <
      realCovarianceNorm n h b c x} = _ from he.symm]
  exact tensorGaussianCovariance_norm_tail n q h hq hh hn

theorem actualComplexCovariance_norm_le_four_real (n h : ℕ) (hh : 0 < h)
    (s t : Bool) (x : FourEntries n h) :
    ‖cMatrixCLM (actualComplexCovariance n h s t x)‖ ≤
      (realCovarianceNorm n h false false x + realCovarianceNorm n h false true x +
       realCovarianceNorm n h true false x + realCovarianceNorm n h true true x) /
        (h : ℝ)^2 := by
  have he := complexCov_norm_le_four_realCov_norm n h hh
    (fun i j => x.1.1 (i,j)) (fun i j => x.1.2 (i,j))
    (fun i j => x.2.1 (i,j)) (fun i j => x.2.2 (i,j)) s t
  have hnorm (A : Matrix (Fin h × Fin h) (Fin h × Fin h) ℝ) :
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) A‖ = ‖matrixCLM A‖ :=
    (Matrix.l2_opNorm_toEuclideanCLM A).trans (matrix_l2_norm_eq A)
  simp only [hnorm] at he
  simpa only [actualComplexCovariance, realCovarianceNorm, selectCopy,
    Bool.false_eq_true, ↓reduceIte, tensorGaussianCovariance, realCov,
    div_eq_mul_inv, mul_comm] using he

/-- A simultaneous bound for all four sign ensembles. The four real covariance
bad events cover every sign, so only one union over four events is used. -/
theorem all_sign_complexCovariance_norm_tail (n K h : ℕ)
    (hK : 1 ≤ K) (hh : 0 < h) (hn : n ≤ (K*h)^2) :
    (fourGaussianLaw n h).real
      {x | ∃ s t : Bool, 8192 * (1 + (K : ℝ))^2 <
        ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ≤
      4 * (h : ℝ)^2 / (2 : ℝ)^h := by
  let T : ℝ := 2048 * (h + K*h : ℕ)^2
  let E : Bool × Bool → Set (FourEntries n h) := fun b =>
    {x | T < realCovarianceNorm n h b.1 b.2 x}
  have hsub : {x | ∃ s t : Bool, 8192 * (1 + (K : ℝ))^2 <
        ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ⊆ ⋃ b, E b := by
    intro x hx
    by_contra hnot
    have hgood (b c : Bool) : realCovarianceNorm n h b c x ≤ T := by
      by_contra hnle
      apply hnot
      exact Set.mem_iUnion.mpr ⟨(b,c), lt_of_not_ge hnle⟩
    obtain ⟨s,t,hst⟩ := hx
    have hs := actualComplexCovariance_norm_le_four_real n h hh s t x
    have hsum : realCovarianceNorm n h false false x + realCovarianceNorm n h false true x +
        realCovarianceNorm n h true false x + realCovarianceNorm n h true true x ≤ 4*T := by
      linarith [hgood false false, hgood false true, hgood true false, hgood true true]
    have hbound := hs.trans (div_le_div_of_nonneg_right hsum (sq_nonneg (h : ℝ)))
    have hT : 4*T / (h : ℝ)^2 = 8192 * (1 + (K : ℝ))^2 := by
      simpa only [T, mul_assoc] using normalized_four_tail_threshold h K hh
    rw [hT] at hbound
    exact (not_lt_of_ge hbound) hst
  have hq : 1 ≤ K*h := by nlinarith
  calc
    _ ≤ (fourGaussianLaw n h).real (⋃ b, E b) := measureReal_mono hsub
    _ ≤ ∑ b : Bool × Bool, (fourGaussianLaw n h).real (E b) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _b : Bool × Bool, (h : ℝ)^2 / (2 : ℝ)^h := by
      apply Finset.sum_le_sum
      intro b hb
      exact realCovarianceNorm_tail n (K*h) h hq hh hn b.1 b.2
    _ = _ := by simp; ring

/-- The literal fixed-sign constant complex covariance tail, proved without
AHH equation (11) or any concentration hypothesis. -/
theorem actualComplexCovariance_norm_tail (n K h : ℕ)
    (hK : 1 ≤ K) (hh : 0 < h) (hn : n ≤ (K*h)^2) (s t : Bool) :
    (fourGaussianLaw n h).real
      {x | 8192 * (1 + (K : ℝ))^2 <
        ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ≤
      4 * (h : ℝ)^2 / (2 : ℝ)^h := by
  apply (measureReal_mono (show {x | 8192 * (1 + (K : ℝ))^2 <
    ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ⊆
      {x | ∃ s t : Bool, 8192 * (1 + (K : ℝ))^2 <
        ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} from
    fun x hx => ⟨s,t,hx⟩)).trans
  exact all_sign_complexCovariance_norm_tail n K h hK hh hn

/-- Arbitrary bounded aspect, with the constant selected before n,h and signs.
The bound is simultaneous in all four dependent sign ensembles. -/
theorem arbitrary_aspect_complexCovariance_exponential_tail (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n h : ℕ, 2 ≤ h → (n : ℝ) ≤ A * (h : ℝ)^2 →
      (fourGaussianLaw n h).real
        {x | ∃ s t : Bool, C < ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} ≤
          Real.exp (-Real.log 2 * h + 4 * Real.log h) := by
  obtain ⟨K,hK,hcover⟩ := aspect_integer_cover A
  refine ⟨8192 * (1 + (K : ℝ))^2, by positivity, ?_⟩
  intro n h hh hn
  exact (all_sign_complexCovariance_norm_tail n K h hK (by omega) (hcover n h hn)).trans
    (four_gaussian_error_le_exp h hh)

/-- Same covariance formula with literal real-valued source signs. -/
def paperComplexCovariance (n h : ℕ) (s t : ℝ) (x : FourEntries n h) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ :=
  ∑ i : Fin n, AHHAlgebraBridges.projector (fun p : Fin h × Fin h =>
    (((x.1.1 (i,p.1) : ℂ) + Complex.I * (s : ℂ) * (x.1.2 (i,p.1) : ℂ)) *
      ((x.2.1 (i,p.2) : ℂ) + Complex.I * (t : ℂ) * (x.2.2 (i,p.2) : ℂ))) /
        (2 * (h : ℂ)))

theorem paperComplexCovariance_eq_actual (n h : ℕ) (s t : Bool) (x : FourEntries n h) :
    paperComplexCovariance n h (sign s) (sign t) x = actualComplexCovariance n h s t x := rfl

/-- Literal paper-facing fixed-(s,t) endpoint. For each positive aspect A the
constant is chosen before the sample size, dimension, and the real signs ±1. -/
theorem paper_fixed_sign_complex_covariance_tail (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n h : ℕ, 2 ≤ h → (n : ℝ) ≤ A * (h : ℝ)^2 →
      ∀ s t : ℝ, (s = -1 ∨ s = 1) → (t = -1 ∨ t = 1) →
        (fourGaussianLaw n h).real
          {x | C < ‖cMatrixCLM (paperComplexCovariance n h s t x)‖} ≤
            Real.exp (-Real.log 2 * h + 4 * Real.log h) := by
  obtain ⟨C,hC,hbound⟩ := arbitrary_aspect_complexCovariance_exponential_tail A
  refine ⟨C,hC,?_⟩
  intro n h hh hn s t hs ht
  obtain ⟨b,rfl⟩ := exists_bool_sign s hs
  obtain ⟨c,rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact (measureReal_mono (show {x | C < ‖cMatrixCLM (actualComplexCovariance n h b c x)‖} ⊆
      {x | ∃ s t : Bool, C < ‖cMatrixCLM (actualComplexCovariance n h s t x)‖} from
        fun x hx => ⟨b,c,hx⟩)).trans (hbound n h hh hn)

/-- The same source-facing endpoint with h=floor(d/2) and an arbitrary bounded
n/d² aspect. It is uniform in every real sign pair, with explicit positive
exponential rate log(2)/2. -/
theorem paper_half_dimension_fixed_sign_tail (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 4 ≤ d → (n : ℝ) ≤ A * (d : ℝ)^2 →
      ∀ s t : ℝ, (s = -1 ∨ s = 1) → (t = -1 ∨ t = 1) →
        (fourGaussianLaw n (d/2)).real
          {x | C < ‖cMatrixCLM (paperComplexCovariance n (d/2) s t x)‖} ≤
            Real.exp (-(Real.log 2 / 2) * d + 4 * Real.log d + Real.log 2) := by
  obtain ⟨K,hK,hcover⟩ := aspect_integer_cover (9*A)
  refine ⟨8192 * (1 + (K : ℝ))^2, by positivity, ?_⟩
  intro n d hd hn s t hs ht
  obtain ⟨b,rfl⟩ := exists_bool_sign s hs
  obtain ⟨c,rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  have hdim : (d : ℝ) ≤ 3 * ((d/2 : ℕ) : ℝ) := by
    exact_mod_cast (show d ≤ 3 * (d/2) by omega)
  have hsq : (d : ℝ)^2 ≤ 9 * ((d/2 : ℕ) : ℝ)^2 := by nlinarith
  have hn' : (n : ℝ) ≤ 9*A*((d/2 : ℕ) : ℝ)^2 :=
    hn.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq hA.le])
  exact (actualComplexCovariance_norm_tail n K (d/2) hK (by omega)
    (hcover n (d/2) hn') b c).trans (half_dimension_error_le_exp d hd)

#print axioms paper_fixed_sign_complex_covariance_tail
#print axioms paper_half_dimension_fixed_sign_tail

#print axioms realCovarianceNorm_tail
#print axioms all_sign_complexCovariance_norm_tail
#print axioms actualComplexCovariance_norm_tail
#print axioms arbitrary_aspect_complexCovariance_exponential_tail
end AHHGaussian
