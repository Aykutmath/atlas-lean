/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending. Uses the true PSD sphere, not a ball-width replacement. -/
import PaperPSDSphereWidth
import UCEscapeExpectation
import GaussianCoisometry

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open BMGeometry BMSaddle BMGordon UCEscape
open scoped InnerProductSpace
namespace GaussianEllipsoid.PaperExactEscapeMean
open PaperPSDSphereWidth

theorem paper_projectedEscape_mean_exact_lower {n d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (U : Euclid r →ₗᵢ[ℝ] Euclid n) :
    (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r)) - paperGaussianSphereWidth d ≤
      ∫ X, projectedEscape (d := d) (fun _ : PUnit.{1} => U) X ∂sampleLaw n d := by
  have h := projected_escape_comparison hd hr (fun _ : PUnit.{1} => U)
  rw [primary_escape_mean hd hr, auxiliary_escape_mean hd hr] at h
  have hsingle : projectedNormMinimum n r (fun _ : PUnit.{1} => U) =
      fun g => ‖U.toContinuousLinearMap.adjoint g‖ := by
    funext g
    simp [projectedNormMinimum]
  have hp : MeasurePreserving U.toContinuousLinearMap.adjoint
      (euclideanGaussianLaw (Fin n)) (euclideanGaussianLaw (Fin r)) := by
    refine ⟨U.toContinuousLinearMap.adjoint.continuous.measurable,
      GaussianEllipsoid.SmallBall.euclideanGaussianLaw_map_coisometry _ ?_⟩
    simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.one_def] using U.adjoint_comp_self
  have hn : (∫ g, projectedNormMinimum n r (fun _ : PUnit.{1} => U) g
      ∂euclideanGaussianLaw (Fin n)) = ∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r) := by
    rw [hsingle]
    exact integral_comp_preserving hp continuous_norm.aestronglyMeasurable
  have hneg := gaussianProductLaw_neg_preserving (Fin d × Fin d)
  have hmin : (∫ z, psdMinimumRaw d z ∂gaussianProductLaw (Fin d × Fin d)) =
      -paperGaussianSphereWidth d := by
    have hs : paperGaussianSphereWidth d = sphereWidth d := by
      simp only [paperGaussianSphereWidth, paper_sphere_support_eq, sphereWidth]
    rw [hs, sphereWidth]
    simp_rw [sphereSupport_eq_neg_min hd]
    rw [integral_neg, neg_neg]
    exact (integral_comp_preserving hneg (psdMinimumRaw_integrable hd).aestronglyMeasurable).symm
  rw [hn, hmin] at h
  simpa only [sub_eq_add_neg] using h

end GaussianEllipsoid.PaperExactEscapeMean
