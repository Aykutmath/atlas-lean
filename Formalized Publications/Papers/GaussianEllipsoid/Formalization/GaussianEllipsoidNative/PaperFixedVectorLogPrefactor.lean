import PaperFixedVectorLogDepth
import PaperPrefactorAbsorption

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.SparseSupport GaussianMixedNormHelpers
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

/-- Source logarithmic depth and logarithmic prefactor, with every numerical
starting-dimension condition discharged and uniformity over sample count and vector. -/
theorem paper_fixed_vector_logarithmic_tail (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  let T := depth (max K 1)
  have hT : 0<T := depth_pos _ (le_max_right K 1)
  let C : ℝ := (2:ℝ)^67*T
  have hC : 0<C := by dsimp [C]; exact mul_pos (by positivity) (Nat.cast_pos.mpr hT)
  let c : ℝ := 1/(2*C)
  have hc : 0<c := by dsimp [c]; positivity
  have hlog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ d : ℕ in atTop, 48*C^3*(A+1) ≤ (d:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hall : ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
    filter_upwards [eventually_natural_cutoff_thresholds T hT,hlog,hlarge,eventually_ge_atTop 24]
      with d hcut hlogd hlargeD hd
    intro n hn u hu hs
    have hs' := hs.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Nat.cast_nonneg d))
    have htail := actual_fixed_vector_tail_logarithmic_depth (max K 1) (le_max_right K 1)
      hd hlogd hcut.2.2.1 hcut.2.2.2.1 hcut.2.2.2.2.1 hcut.2.2.2.2.2 u hu hs'
    have hconst : multiscaleFixedConstant (max K 1)=multiscaleFixedConstant K := by
      unfold multiscaleFixedConstant
      rw [max_eq_left (le_max_right K 1)]
    rw [hconst] at htail
    have hp := paper_logarithmic_prefactor hA.le hC
      (show (1:ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega)) hlogd hn hlargeD
    have hh := htail.trans hp
    apply hh.trans_eq
    congr 2
    dsimp [c]
    ring
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp hall
  exact ⟨c,hc,d₀,hd₀⟩
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_fixed_vector_logarithmic_tail
