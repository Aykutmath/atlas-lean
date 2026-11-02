import PaperProjectedEscapeConcentration
import PaperExactEscapeMean

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open BMGeometry BMSaddle BMGordon UCEscape
open scoped InnerProductSpace
namespace GaussianEllipsoid.PaperGaussianEscape
open PaperPSDSphereWidth PaperExactEscapeMean

/-- Exact paper Gaussian escape inequality, retaining the Gaussian norm expectation,
the true PSD-unit-sphere width, and the sharp exp(−t²/2) failure probability.
The sample is the canonical full-entry realization of independent symmetric-isonormal rows. -/
theorem gaussian_escape {n d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (U : Euclid r →ₗᵢ[ℝ] Euclid n) (t : ℝ) (ht : 0 < t) :
    (sampleLaw n d).real {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t} ≤
      Real.exp (-t^2/2) := by
  have hm := paper_projectedEscape_mean_exact_lower hd hr U
  have hsub : {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t} ⊆
    {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ Y, projectedEscape (d := d) (fun _ : PUnit.{1} => U) Y ∂sampleLaw n d)-t} := by
    intro X hX
    exact lt_of_lt_of_le hX (sub_le_sub_right hm t)
  exact (measureReal_mono hsub).trans
    (projectedEscape_sharp_lower_tail hd hr (fun _ : PUnit.{1} => U) t ht.le)

#print axioms gaussian_escape
end GaussianEllipsoid.PaperGaussianEscape
