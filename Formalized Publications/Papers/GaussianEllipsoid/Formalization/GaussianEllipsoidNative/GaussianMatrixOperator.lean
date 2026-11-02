import GaussianProductLinearForms
import OperatorTwoSphereNet
import ShiftedExponentialMoments
import VolumetricNets
import Mathlib.Tactic

/-! Genuine rectangular Euclidean Gaussian operator norm. The input sample law
is the explicit iid product law on the h*q real matrix entries. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTensorMoments

/-- Currying the independent entry coordinates into a rectangular matrix. -/
def entryMatrix (h q : ℕ) : ((Fin h × Fin q) → ℝ) →ₗ[ℝ] Matrix (Fin h) (Fin q) ℝ where
  toFun x := fun i j => x (i,j)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- Explicit linear map into Euclidean continuous linear maps. Its norm is
therefore the spectral norm, not the default entrywise Matrix norm. -/
def gaussianMatrixCLM (h q : ℕ) : ((Fin h × Fin q) → ℝ) →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin h)) :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin h) (n := Fin q)).trans LinearMap.toContinuousLinearMap).toLinearMap.comp
    (entryMatrix h q)

theorem gaussianMatrixCLM_continuous (h q : ℕ) : Continuous (gaussianMatrixCLM h q) :=
  (gaussianMatrixCLM h q).continuous_of_finiteDimensional

/-- The bilinear form has the expected finite sum of independent entries. -/
theorem gaussianMatrixCLM_inner (h q : ℕ) (x : (Fin h × Fin q) → ℝ)
    (u : EuclideanSpace ℝ (Fin h)) (v : EuclideanSpace ℝ (Fin q)) :
    ⟪u,gaussianMatrixCLM h q x v⟫_ℝ =
      ∑ p : Fin h × Fin q, (u p.1 * v p.2) * x p := by
  simp [gaussianMatrixCLM, entryMatrix, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change x (i, j) * v j * u i = u i * v j * x (i, j)
  ring

/-- Unit vectors supply a unit squared coefficient sum for the bilinear Gaussian. -/
theorem bilinear_coefficients_norm (h q : ℕ)
    (u : EuclideanSpace ℝ (Fin h)) (v : EuclideanSpace ℝ (Fin q))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∑ p : Fin h × Fin q, (u p.1 * v p.2)^2 = 1 := by
  have hu₂ : ∑ i, (u i)^2 = 1 := by
    simpa [hu, Real.norm_eq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin h => ℝ) u).symm
  have hv₂ : ∑ j, (v j)^2 = 1 := by
    simpa [hv, Real.norm_eq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => ℝ) v).symm
  simp_rw [Fintype.sum_prod_type, mul_pow]
  rw [← Finset.sum_mul_sum, hu₂, hv₂, one_mul]

/-- Actual bilinear Gaussian tails for fixed real Euclidean unit vectors. -/
theorem gaussianMatrixCLM_pair_tail (h q : ℕ)
    (u : EuclideanSpace ℝ (Fin h)) (v : EuclideanSpace ℝ (Fin q))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianProductLaw (Fin h × Fin q)).real
      {x | t ≤ |⟪u,gaussianMatrixCLM h q x v⟫_ℝ|} ≤ 2*exp (-(t^2)/2) := by
  simp_rw [gaussianMatrixCLM_inner]
  exact gaussianProductLaw_linear_abs_tail _ (bilinear_coefficients_norm h q u v hu hv) ht

/-- Union bound on two concrete finite sphere nets; no independence between
net pairings is assumed or needed. -/
theorem gaussianMatrixCLM_tail_of_nets (h q : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin h)))
    (t : Finset (EuclideanSpace ℝ (Fin q)))
    (hsnorm : ∀ u ∈ s, ‖u‖ = 1) (htnorm : ∀ v ∈ t, ‖v‖ = 1)
    (hsnet : ∀ u, ‖u‖ = 1 → ∃ u₀ ∈ s, ‖u-u₀‖ ≤ 1/4)
    (htnet : ∀ v, ‖v‖ = 1 → ∃ v₀ ∈ t, ‖v-v₀‖ ≤ 1/4)
    {r : ℝ} (hr : 0 ≤ r) :
    (gaussianProductLaw (Fin h × Fin q)).real
      {x | 2*r < ‖gaussianMatrixCLM h q x‖} ≤
      2*(s.card*t.card : ℕ)*exp (-(r^2)/2) := by
  classical
  let μ := gaussianProductLaw (Fin h × Fin q)
  let ev (u : EuclideanSpace ℝ (Fin h)) (v : EuclideanSpace ℝ (Fin q)) :=
    {x : (Fin h × Fin q) → ℝ | r ≤ |⟪u,gaussianMatrixCLM h q x v⟫_ℝ|}
  have hsub : {x | 2*r < ‖gaussianMatrixCLM h q x‖} ⊆
      ⋃ u ∈ s, ⋃ v ∈ t, ev u v := by
    intro x hx
    by_contra hbad
    simp only [Set.mem_iUnion, exists_prop] at hbad
    have hp : ∀ u ∈ s, ∀ v ∈ t, |⟪u,gaussianMatrixCLM h q x v⟫_ℝ| ≤ r := by
      intro u hu v hv
      exact le_of_lt (lt_of_not_ge (fun hh => hbad ⟨u, hu, v, hv, hh⟩))
    have hh := opNorm_le_two_of_sphere_nets (gaussianMatrixCLM h q x)
      s t hsnorm htnorm hsnet htnet hr hp
    exact not_lt_of_ge hh hx
  calc
    μ.real {x | 2*r < ‖gaussianMatrixCLM h q x‖}
      ≤ μ.real (⋃ u ∈ s, ⋃ v ∈ t, ev u v) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ u ∈ s, μ.real (⋃ v ∈ t, ev u v) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ s, ∑ v ∈ t, 2*exp (-(r^2)/2) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (measureReal_biUnion_finset_le t (ev u)).trans
        (Finset.sum_le_sum (fun v hv => gaussianMatrixCLM_pair_tail h q u v
          (hsnorm u hu) (htnorm v hv) hr))
    _ = _ := by simp; ring

/-- Unconditional rectangular spectral-norm tail, using the constructed
Euclidean quarter-nets of cardinality at most 9^h and 9^q. -/
theorem gaussianMatrixCLM_net_tail (h q : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianProductLaw (Fin h × Fin q)).real
      {x | 2*r < ‖gaussianMatrixCLM h q x‖} ≤
      2*(9:ℝ)^(h+q)*exp (-(r^2)/2) := by
  obtain ⟨s, hsn, hsc, hsnets⟩ := GaussianEllipsoid.exists_sphere_quarter_net h
  obtain ⟨t, htn, htc, htnets⟩ := GaussianEllipsoid.exists_sphere_quarter_net q
  have hsnet : ∀ u, ‖u‖ = 1 → ∃ u₀ ∈ s, ‖u-u₀‖ ≤ 1/4 := by
    intro u hu
    obtain ⟨u₀, hmem, hdist⟩ := hsnets u hu
    exact ⟨u₀, hmem, hdist.le⟩
  have htnet : ∀ v, ‖v‖ = 1 → ∃ v₀ ∈ t, ‖v-v₀‖ ≤ 1/4 := by
    intro v hv
    obtain ⟨v₀, hmem, hdist⟩ := htnets v hv
    exact ⟨v₀, hmem, hdist.le⟩
  have hc : (s.card*t.card : ℝ) ≤ (9:ℝ)^(h+q) := by
    exact_mod_cast (show s.card*t.card ≤ (9:ℕ)^(h+q) by
      rw [pow_add]
      exact Nat.mul_le_mul hsc htc)
  exact (gaussianMatrixCLM_tail_of_nets h q s t hsn htn hsnet htnet hr).trans (by
    push_cast
    gcongr)

/-- The exact entropy shift appearing in the elementary Gaussian moment bound. -/
def gaussianNetShift (h q : ℕ) : ℝ := (h+q : ℕ)*log 9 + log 2

theorem gaussianNetShift_nonneg (h q : ℕ) : 0 ≤ gaussianNetShift h q := by
  unfold gaussianNetShift
  positivity

theorem exp_gaussianNetShift (h q : ℕ) :
    exp (gaussianNetShift h q) = 2*(9:ℝ)^(h+q) := by
  rw [gaussianNetShift, exp_add, exp_nat_mul, exp_log (by norm_num : (0:ℝ)<9),
    exp_log (by norm_num : (0:ℝ)<2)]
  ring

/-- The squared Euclidean operator norm, divided by eight, has a shifted
unit exponential tail under the actual iid Gaussian matrix law. -/
theorem gaussianMatrixCLM_squared_shifted_tail (h q : ℕ) {a : ℝ} (ha : 0 < a) :
    (gaussianProductLaw (Fin h × Fin q))
      {x | gaussianNetShift h q+a < ‖gaussianMatrixCLM h q x‖^2/8} ≤
      ENNReal.ofReal (exp (-a)) := by
  let D := gaussianNetShift h q
  have hD : 0 ≤ D := gaussianNetShift_nonneg h q
  let r := sqrt (2*(D+a))
  have hr : 0 ≤ r := sqrt_nonneg _
  have hrsq : r^2 = 2*(D+a) := sq_sqrt (by positivity)
  have hsub : {x | D+a < ‖gaussianMatrixCLM h q x‖^2/8} ⊆
      {x | 2*r < ‖gaussianMatrixCLM h q x‖} := by
    intro x hx
    change 2*r < ‖gaussianMatrixCLM h q x‖
    have hn := norm_nonneg (gaussianMatrixCLM h q x)
    change D + a < ‖gaussianMatrixCLM h q x‖ ^ 2 / 8 at hx
    nlinarith
  have hb := (measureReal_mono hsub).trans (gaussianMatrixCLM_net_tail h q hr)
  have he : 2*(9:ℝ)^(h+q)*exp (-(r^2)/2) = exp (-a) := by
    rw [hrsq, show -(2*(D+a))/2 = -D-a by ring, exp_sub, exp_neg,
      exp_gaussianNetShift]
    rw [exp_neg]
    field_simp
  rw [he] at hb
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  simpa [Measure.real, D, ENNReal.toReal_ofReal (le_of_lt (exp_pos _))] using hb

/-- Every even operator-norm moment is integrable under the iid matrix law. -/
theorem gaussianMatrixCLM_integrable_even_moment (h q m : ℕ) :
    Integrable (fun x => ‖gaussianMatrixCLM h q x‖^(2*m))
      (gaussianProductLaw (Fin h × Fin q)) := by
  let X : ((Fin h × Fin q) → ℝ) → ℝ :=
    fun x => ‖gaussianMatrixCLM h q x‖^2/8
  have hXn : 0 ≤ᵐ[gaussianProductLaw (Fin h × Fin q)] X :=
    ae_of_all _ (fun x => by dsimp [X]; positivity)
  have hXm : AEMeasurable X (gaussianProductLaw (Fin h × Fin q)) :=
    ((((gaussianMatrixCLM_continuous h q).norm.pow 2).div_const 8).measurable).aemeasurable
  have hi := shifted_exp_tail_integrable_pow hXn hXm (gaussianNetShift_nonneg h q)
    (fun t ht => gaussianMatrixCLM_squared_shifted_tail h q ht) m
  have heq (x : (Fin h × Fin q) → ℝ) :
      ‖gaussianMatrixCLM h q x‖^(2*m) = (8:ℝ)^m * X x^m := by
    dsimp [X]
    rw [pow_mul, div_pow]
    field_simp
  simpa only [heq] using hi.const_mul ((8:ℝ)^m)

/-- Exact finite-dimensional ordinary Gaussian operator moment used in the
Wick tensor comparison. Everything here is under the concrete product law. -/
theorem gaussianMatrixCLM_even_moment_le (h q m : ℕ) :
    (∫ x, ‖gaussianMatrixCLM h q x‖^(2*m)
      ∂gaussianProductLaw (Fin h × Fin q)) ≤
      (8*(gaussianNetShift h q+m))^m := by
  let X : ((Fin h × Fin q) → ℝ) → ℝ :=
    fun x => ‖gaussianMatrixCLM h q x‖^2/8
  have hXn : 0 ≤ᵐ[gaussianProductLaw (Fin h × Fin q)] X :=
    ae_of_all _ (fun x => by dsimp [X]; positivity)
  have hXm : AEMeasurable X (gaussianProductLaw (Fin h × Fin q)) :=
    ((((gaussianMatrixCLM_continuous h q).norm.pow 2).div_const 8).measurable).aemeasurable
  have hm := shifted_exp_tail_integral_pow_le hXn hXm (gaussianNetShift_nonneg h q)
    (fun t ht => gaussianMatrixCLM_squared_shifted_tail h q ht) m
  have heq (x : (Fin h × Fin q) → ℝ) :
      ‖gaussianMatrixCLM h q x‖^(2*m) = (8:ℝ)^m * X x^m := by
    dsimp [X]
    rw [pow_mul, div_pow]
    field_simp
  simp_rw [heq]
  rw [integral_const_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

#print axioms gaussianMatrixCLM_even_moment_le
#print axioms gaussianMatrixCLM_net_tail
#print axioms gaussianMatrixCLM_squared_shifted_tail
#print axioms gaussianMatrixCLM_pair_tail

end GaussianTensorMoments
