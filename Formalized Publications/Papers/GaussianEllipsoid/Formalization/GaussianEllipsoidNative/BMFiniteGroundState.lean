import BMActualFiniteReplacement
import BMFiniteSoftMin
import Mathlib.Topology.Order.Lattice

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition BMFiniteGibbsReplacement BMGibbsRowReplacement BMActualFiniteReplacement
open scoped BigOperators BoundedContinuousFunction

namespace BMFiniteGroundState
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Replace an arbitrary finite prior with the uniform prior on the same states.
All scalar potential and temperature data are unchanged. -/
def uniformData2 (D : Data2 κ) : Data2 κ :=
  { D with
    weight := fun _ => (Fintype.card κ : ℝ)⁻¹
    weight_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
    weight_sum := by simp [ne_of_gt (Fintype.card_pos (α := κ))] }

def energy (D : Data κ) (v : ℝ) {n : ℕ} (y : Fin n → κ → ℝ) (a : κ) : ℝ :=
  rowSum D y a / v

def ground (D : Data κ) (v : ℝ) {n : ℕ} (y : Fin n → κ → ℝ) : ℝ :=
  BMFiniteSoftMin.ground (energy D v y)

def free (D : Data κ) (v : ℝ) {n : ℕ} (y : Fin n → κ → ℝ) : ℝ :=
  -fullLogPartition D y/(D.beta*v)

theorem uniform_free_eq_softMin (D : Data2 κ) (v : ℝ) (hv : v ≠ 0)
    {n : ℕ} (y : Fin n → κ → ℝ) :
    free (uniformData2 D).toData v y = BMFiniteSoftMin.freeEnergy D.beta v (energy D.toData v y) := by
  unfold free fullLogPartition fullPartition BMFiniteSoftMin.freeEnergy uniformData2 energy
  congr 2
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only
  have hs : rowSum D.toData y a = rowSum (uniformData2 D).toData y a := rfl
  have he : -D.beta*v*(rowSum D.toData y a/v) = -D.beta*rowSum D.toData y a := by field_simp [hv]
  rw [he]
  simp only [rowSum,div_eq_mul_inv,mul_comm]

theorem uniform_ground_eq (D : Data2 κ) (v : ℝ) {n : ℕ} (y : Fin n → κ → ℝ) :
    ground (uniformData2 D).toData v y = ground D.toData v y := rfl

theorem uniform_free_sub_ground_le (D : Data2 κ) (hβ : 0 < D.beta) (v : ℝ) (hv : 0 < v)
    {n : ℕ} (y : Fin n → κ → ℝ) :
    |free (uniformData2 D).toData v y-ground D.toData v y| ≤
      Real.log (Fintype.card κ : ℝ)/(D.beta*v) := by
  rw [uniform_free_eq_softMin D v (ne_of_gt hv)]
  exact BMFiniteSoftMin.abs_freeEnergy_sub_ground_le D.beta v hβ hv _

theorem energy_continuous (D : Data κ) (v : ℝ) (n : ℕ) (a : κ) :
    Continuous (fun y : Fin n → κ → ℝ => energy D v y a) := by
  apply Continuous.div_const
  apply continuous_finset_sum
  intro i hi
  exact D.potential.continuous.comp ((continuous_apply a).comp (continuous_apply i))

theorem ground_continuous (D : Data κ) (v : ℝ) (n : ℕ) :
    Continuous (ground D v (n := n)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun a _ => energy_continuous D v n a)

theorem ground_abs_le (D : Data κ) (v : ℝ) {n : ℕ} (y : Fin n → κ → ℝ) :
    |ground D v y| ≤ (n*‖D.potential‖)/|v| := by
  obtain ⟨a,ha⟩ := BMFiniteSoftMin.ground_attained (energy D v y)
  change |BMFiniteSoftMin.ground (energy D v y)| ≤ _
  rw [ha,energy,abs_div]
  exact div_le_div_of_nonneg_right (rowSum_abs_le D y a) (abs_nonneg v)

theorem ground_integrable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (v : ℝ) {n : ℕ} (y : X → Fin n → κ → ℝ) (hy : Continuous y) :
    Integrable (fun x => ground D v (y x)) μ := by
  apply (integrable_const ((n*‖D.potential‖)/|v|)).mono'
  · exact ((ground_continuous D v n).comp hy).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => ground_abs_le D v _

theorem free_integrable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (v : ℝ) {n : ℕ} (y : X → Fin n → κ → ℝ) (hy : Continuous y) :
    Integrable (fun x => free D v (y x)) μ := by
  have hi : Integrable (fun x => fullLogPartition D (y x)) μ := by
    apply (integrable_const (D.beta*(n*‖D.potential‖))).mono'
    · exact ((fullLogPartition_continuous D n).comp hy).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => fullLogPartition_abs_le D _
  exact hi.neg.div_const _

/-- Soft-min error after expectation under any probability source law. -/
theorem expected_uniform_free_sub_ground_le {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data2 κ) (hβ : 0 < D.beta) (v : ℝ) (hv : 0 < v)
    {n : ℕ} (y : X → Fin n → κ → ℝ) (hy : Continuous y) :
    |(∫ x, free (uniformData2 D).toData v (y x) ∂μ) -
        ∫ x, ground D.toData v (y x) ∂μ| ≤ Real.log (Fintype.card κ : ℝ)/(D.beta*v) := by
  rw [← integral_sub (free_integrable μ (uniformData2 D).toData v y hy) (ground_integrable μ D.toData v y hy)]
  calc
    _ ≤ ∫ x, |free (uniformData2 D).toData v (y x)-ground D.toData v (y x)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => free (uniformData2 D).toData v (y x)-ground D.toData v (y x))
    _ ≤ ∫ _x, Real.log (Fintype.card κ : ℝ)/(D.beta*v) ∂μ :=
      integral_mono ((free_integrable μ (uniformData2 D).toData v y hy).sub
        (ground_integrable μ D.toData v y hy)).norm (integrable_const _)
        (fun x => uniform_free_sub_ground_le D hβ v hv _)
    _ = _ := by simp

/-- The normalized full-product free-energy error, with the BM d² volume. -/
theorem actual_finite_free_replacement {d m : ℕ}
    (D : Data2 κ) (hβ : 0 < D.beta) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hAsym : ∀ a, (A a).transpose = A a) (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2/(d:ℝ)*Matrix.trace (A a*A b))
    (hd : 0 < d) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K)
    (n : ℕ) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), free D.toData ((d:ℝ)^2)
        (fun i => polynomialFamily (fun a => normalizedQuadratic d (A a)) (x i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d))) -
      ∫ z : Fin (n+1) → (Fin m → ℝ), free D.toData ((d:ℝ)^2)
        (fun i => polynomialFamily (fun a => linearPolynomial (B a)) (z i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤
      ((n+1 : ℕ)*replacementError D K d)/(D.beta*(d:ℝ)^2) := by
  have h := actual_finite_logPartition_replacement D A hAsym B hCov hd hK hA n
  unfold free
  simp_rw [integral_div,integral_neg]
  exact BMFiniteProductReplacement.normalized_expectation_comparison hβ
    (sq_pos_of_pos (by exact_mod_cast hd)) h

@[simp] theorem replacementError_uniformData2 (D : Data2 κ) (K : ℝ) (d : ℕ) :
    replacementError (uniformData2 D) K d = replacementError D K d := rfl

/-- Actual finite-state ground-energy comparison obtained by calling the
quadratic Stein replacement and the sharp finite soft-min bound. The only
state-count dependence is the displayed logarithmic entropy penalty. -/
theorem actual_finite_ground_replacement {d m : ℕ}
    (D : Data2 κ) (hβ : 0 < D.beta) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hAsym : ∀ a, (A a).transpose = A a) (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2/(d:ℝ)*Matrix.trace (A a*A b))
    (hd : 0 < d) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K)
    (n : ℕ) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), ground D.toData ((d:ℝ)^2)
        (fun i => polynomialFamily (fun a => normalizedQuadratic d (A a)) (x i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d))) -
      ∫ z : Fin (n+1) → (Fin m → ℝ), ground D.toData ((d:ℝ)^2)
        (fun i => polynomialFamily (fun a => linearPolynomial (B a)) (z i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤
      ((n+1 : ℕ)*replacementError D K d)/(D.beta*(d:ℝ)^2) +
        2*(Real.log (Fintype.card κ : ℝ)/(D.beta*(d:ℝ)^2)) := by
  let q := polynomialFamily (fun a => normalizedQuadratic d (A a))
  let g := polynomialFamily (fun a => linearPolynomial (B a))
  have hq : Continuous (fun x : Fin (n+1) → (Fin d → ℝ) => fun i => q (x i)) :=
    continuous_pi fun i => q.continuous.comp (continuous_apply i)
  have hg : Continuous (fun x : Fin (n+1) → (Fin m → ℝ) => fun i => g (x i)) :=
    continuous_pi fun i => g.continuous.comp (continuous_apply i)
  have hv : 0 < (d:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hd)
  letI : ∀ _i : Fin (n+1), IsProbabilityMeasure (gaussianProductLaw (Fin d)) := fun _ => gaussianProductLaw_probability
  letI : ∀ _i : Fin (n+1), IsProbabilityMeasure (gaussianProductLaw (Fin m)) := fun _ => gaussianProductLaw_probability
  letI : ∀ _i : Fin (n+1), SigmaFinite (gaussianProductLaw (Fin d)) := fun _ => inferInstance
  letI : ∀ _i : Fin (n+1), SigmaFinite (gaussianProductLaw (Fin m)) := fun _ => inferInstance
  have hW := expected_uniform_free_sub_ground_le (n := n+1)
    (Measure.pi fun _ : Fin (n+1) => gaussianProductLaw (Fin d)) D hβ ((d:ℝ)^2) hv _ hq
  have hG := expected_uniform_free_sub_ground_le (n := n+1)
    (Measure.pi fun _ : Fin (n+1) => gaussianProductLaw (Fin m)) D hβ ((d:ℝ)^2) hv _ hg
  have hF := actual_finite_free_replacement (uniformData2 D) hβ A hAsym B hCov hd hK hA n
  rw [replacementError_uniformData2] at hF
  rw [abs_sub_comm] at hW hG
  exact BMFiniteSoftMin.ground_comparison_of_freeEnergy hW hG hF

#print axioms actual_finite_ground_replacement
#print axioms actual_finite_free_replacement
#print axioms expected_uniform_free_sub_ground_le
#print axioms uniform_free_eq_softMin
end BMFiniteGroundState
