import ActualAtomEvent
import ActualUniformExtension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Filter GaussianEllipsoid
namespace GaussianEllipsoidCandidate

/-- Explicit aspect-uniform failure envelope for the actual atom event. -/
def atomFailureBound (A : ℝ) (d : ℕ) : ℝ :=
  2*A*(d:ℝ)^2*Real.exp (-(d:ℝ)/768)

theorem canonical_atom_event (A : ℝ) (hA : 0 < A) (d n : ℕ) (hd : 24 ≤ d)
    (hn : (n:ℝ) ≤ A*(d:ℝ)^2) :
    MeasurableSet (atomRowsGood d n (2*(d/4))) ∧
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      (atomRowsGood d n (2*(d/4)))ᶜ ≤ atomFailureBound A d ∧
    ∀ X ∈ atomRowsGood d n (2*(d/4)), ∀ u : Fin n → ℝ,
      spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) ≤
          2*Real.sqrt d*coefficientMass u := by
  have hhlo : (d:ℝ) ≤ 3*((2*(d/4):ℕ):ℝ) := by exact_mod_cast (show d ≤ 3*(2*(d/4)) by omega)
  have hhup : (5/4:ℝ)*((2*(d/4):ℕ):ℝ) ≤ d := by
    have hh : 4*(d/4) ≤ d := Nat.mul_div_le d 4
    have hhR : 4*(d/4:ℕ) ≤ (d:ℝ) := by exact_mod_cast hh
    push_cast
    linarith [Nat.cast_nonneg (d/4) (α:=ℝ)]
  refine ⟨atomRowsGood_measurable _ _ _, ?_, ?_⟩
  · apply (atomRowsGood_failure_le d n (2*(d/4)) hhup).trans
    unfold atomFailureBound
    apply mul_le_mul
    · linarith
    · exact Real.exp_le_exp.mpr (by linarith)
    · positivity
    · positivity
  · intro X hX u
    have hh := scaledBilinearNuclear_le_mass hX u
    exact hh.trans (by nlinarith [Real.sqrt_nonneg (d:ℝ), coefficientMass_nonneg u])

/-- The genuine Gaussian atom error vanishes uniformly for every fixed aspect A. -/
theorem atomFailureBound_tendsto_zero (A : ℝ) :
    Tendsto (atomFailureBound A) atTop (nhds 0) := by
  have ht : Tendsto (fun d : ℕ => (d:ℝ)/768) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).const_mul_atTop
        (by norm_num : (0:ℝ)<(768:ℝ)⁻¹)
  have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp ht
  have hf := hh.const_mul (2*A*768^2)
  convert hf using 1
  · ext d
    dsimp [atomFailureBound]
    simp only [Function.comp_apply, neg_div]
    ring
  · ring

end GaussianEllipsoidCandidate
