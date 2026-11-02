import PaperMultiscaleHalfDimension
import Mathlib.Data.EReal.Operations

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate

def paperMultiscaleRatioInf (d n h : ℕ) (K : ℝ)
    (X : Fin n → Euclid h × Euclid h) : EReal :=
  sInf {v : EReal | ∃ u : Fin n → ℝ, u ≠ 0 ∧
    ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d ∧
    v = ((scaledBilinearNuclear d u X / (Real.sqrt d * coefficientMass u) : ℝ) : EReal)}

theorem coefficientMass_pos_of_ne_zero {n : ℕ} (u : Fin n → ℝ) (hu : u ≠ 0) :
    0 < coefficientMass u := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  exact Finset.sum_pos' (fun j _ => abs_nonneg (u j))
    ⟨i,Finset.mem_univ _,abs_pos.mpr hi⟩

/-- The paper's infimum is an extended-real infimum, so an empty coefficient
class has value +infinity rather than Lean's real sInf default0. For d>0 this
is exactly the already proved undivided uniform event. -/
theorem paperMultiscaleRatioInf_ge_iff (d n h : ℕ) (hd : 0 < d) (K : ℝ)
    (X : Fin n → Euclid h × Euclid h) :
    (multiscaleConstant K : EReal) ≤ paperMultiscaleRatioInf d n h K X ↔
      X ∈ multiscaleGoodDimension d n h K := by
  have hsqrt : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  constructor
  · intro hInf u hu
    by_cases hu0 : u = 0
    · subst u
      simp [scaledBilinearNuclear,coefficientMass,bilinearSynthesis]
    have hden := mul_pos hsqrt (coefficientMass_pos_of_ne_zero u hu0)
    have hq : (multiscaleConstant K : EReal) ≤
        ((scaledBilinearNuclear d u X/(Real.sqrt d*coefficientMass u):ℝ):EReal) :=
      (le_sInf_iff.mp hInf) _ ⟨u,hu0,hu,rfl⟩
    have hreal : multiscaleConstant K ≤ scaledBilinearNuclear d u X/(Real.sqrt d*coefficientMass u) := by
      exact_mod_cast hq
    simpa only [mul_assoc] using (le_div_iff₀ hden).mp hreal
  · intro hGood
    apply le_sInf
    rintro v ⟨u,hu0,hu,rfl⟩
    have hden := mul_pos hsqrt (coefficientMass_pos_of_ne_zero u hu0)
    have hreal : multiscaleConstant K ≤ scaledBilinearNuclear d u X/(Real.sqrt d*coefficientMass u) := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_assoc] using hGood u hu
    exact_mod_cast hreal

/-- Literal infimum-ratio probability form of paper Theorem7.1, preserving
empty-class semantics and the exact half dimension. -/
theorem paper_multiscale_infimum_tendsto_one (A K : ℝ)
    (hA : 0 < A) (hK : 0 < K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
      {X | (multiscaleConstant K:EReal) ≤ paperMultiscaleRatioInf d (n d) (d/2) K X})
      atTop (𝓝 1) := by
  apply (paper_multiscale_uniform_good_tendsto_one A K hA hK n hn).congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  congr 1
  ext X
  exact (paperMultiscaleRatioInf_ge_iff d (n d) (d/2) (by omega) K X).symm
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_multiscale_infimum_tendsto_one
