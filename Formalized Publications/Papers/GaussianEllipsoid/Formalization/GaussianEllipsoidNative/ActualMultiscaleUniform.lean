import ActualFixedVectorTail
import ActualUniformProbability

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.SparseSupport GaussianMixedNormHelpers
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate

/-- A concrete retention width valid uniformly in the coefficient vector. -/
def multiscaleWidth (K : ℝ) : ℕ := 40+4*⌈max K 1⌉₊

/-- A numerical fixed-vector exponential rate; its small size affects only
the starting dimension, not the stated uniform nuclear lower constant. -/
def multiscaleTailRate (K : ℝ) : ℝ := 1/((2:ℝ)^67*multiscaleWidth K)

theorem multiscaleWidth_pos (K : ℝ) : 0 < multiscaleWidth K := by
  unfold multiscaleWidth
  omega

theorem multiscaleTailRate_pos (K : ℝ) : 0 < multiscaleTailRate K := by
  have hT : (0:ℝ) < multiscaleWidth K := by exact_mod_cast multiscaleWidth_pos K
  unfold multiscaleTailRate
  positivity

theorem multiscaleFixedConstant_max_one (K : ℝ) :
    multiscaleFixedConstant (max K 1) = multiscaleFixedConstant K := by
  unfold multiscaleFixedConstant
  rw [max_eq_left (le_max_right K 1)]

/-- All finite-dimensional cutoff obligations are discharged eventually.
This is the actual Gaussian fixed-vector bound, uniform over all n and all
unit-l1 vectors with at most Kd nonzero coefficients. -/
theorem eventually_actual_fixed_vector_tail (K : ℝ) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, ∀ u : Fin n → ℝ,
      coefficientMass u = 1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
        (n+1:ℝ)*Real.exp (-multiscaleTailRate K*(d:ℝ)^2/Real.log (d:ℝ)) := by
  have hlog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_natural_cutoff_thresholds (multiscaleWidth K) (multiscaleWidth_pos K),
    hlog, eventually_ge_atTop 24] with d hcut hlogd hd
  intro n u hu hs
  have hs' : ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ max K 1*d :=
    hs.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Nat.cast_nonneg d))
  have hh := actual_fixed_vector_tail (max K 1) (le_max_right K 1) hd hlogd
    hcut.2.2.1 hcut.2.2.2.1 hcut.2.2.2.2.1 hcut.2.2.2.2.2 u hu hs'
  rw [multiscaleFixedConstant_max_one] at hh
  convert hh using 1
  unfold multiscaleTailRate multiscaleWidth
  congr 2
  ring

/-- Section 7's actual uniform multiscale nuclear lower bound: the full
failure probability tends to zero. The result is simultaneous over arbitrary
sample-dependent supports, signs and magnitudes and requires no analytic
hypothesis beyond the actual iid standard Gaussian pair law. -/
theorem actual_multiscale_uniform_failure_tendsto_zero (A K : ℝ)
    (hA : 0 < A) (hK : 0 ≤ K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (2*(d/4)) (2*(d/4))).real
      (actualMultiscaleBad d (n d) K)) atTop (nhds 0) := by
  apply actual_multiscale_tendsto_zero_of_fixed_vector A K 1 (multiscaleTailRate K) 1
    hA hK (by norm_num) (multiscaleTailRate_pos K) _ n hn
  filter_upwards [eventually_actual_fixed_vector_tail K] with d hd
  intro n hn u hu hs
  simpa only [one_mul, pow_one] using hd n u hu hs

/-- Exact good event appearing in the paper's uniform nuclear theorem. -/
def actualMultiscaleGood (d n : ℕ) (K : ℝ) :
    Set (Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4))) :=
  {X | ∀ u : Fin n → ℝ,
    ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
    ((1/2:ℝ)^30/(Real.sqrt (max K 1)*(1+Real.log (max K 1))))*Real.sqrt d*(∑ i, |u i|) ≤
      spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))}

theorem actualMultiscaleGood_eq_compl (d n : ℕ) (K : ℝ) :
    actualMultiscaleGood d n K = (actualMultiscaleBad d n K)ᶜ := by
  ext X
  simp only [actualMultiscaleGood, actualMultiscaleBad, Set.mem_setOf_eq, Set.mem_compl_iff,
    not_exists, not_and, not_lt, scaledBilinearNuclear, multiscaleConstant, coefficientMass]

theorem measurableSet_actualMultiscaleGood (d n : ℕ) (K : ℝ) :
    MeasurableSet (actualMultiscaleGood d n K) := by
  letI : SecondCountableTopology (Euclid (2*(d/4))) :=
    (EuclideanSpace.equiv (Fin (2*(d/4))) ℝ).toHomeomorph.secondCountableTopology
  rw [actualMultiscaleGood_eq_compl]
  exact (actualMultiscaleBad_isOpen d n K).measurableSet.compl

/-- Probability tends to one in precisely the actual iid Gaussian pair model,
with the literal μ(K)=2⁻³⁰/[√max(K,1)(1+log max(K,1))] and even-half dimensions. -/
theorem actual_multiscale_uniform_good_tendsto_one (A K : ℝ)
    (hA : 0 < A) (hK : 0 ≤ K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (2*(d/4)) (2*(d/4))).real
      (actualMultiscaleGood d (n d) K)) atTop (nhds 1) := by
  have hbad := actual_multiscale_uniform_failure_tendsto_zero A K hA hK n hn
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hbad
  simp only [sub_zero] at hh
  convert hh using 1
  funext d
  letI : SecondCountableTopology (Euclid (2*(d/4))) :=
    (EuclideanSpace.equiv (Fin (2*(d/4))) ℝ).toHomeomorph.secondCountableTopology
  rw [actualMultiscaleGood_eq_compl,
    measureReal_compl (actualMultiscaleBad_isOpen d (n d) K).measurableSet]
  simp

end GaussianEllipsoidCandidate
