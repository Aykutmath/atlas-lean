import PaperGaussianEscape
import PaperSphereWidthAsymptotic

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open BMGeometry BMSaddle BMGordon UCEscape
open scoped InnerProductSpace
namespace GaussianEllipsoid.PaperGaussianEscape
open PaperPSDSphereWidth PaperExactEscapeMean

lemma paperGaussianSphereWidth_nonneg {d : ℕ} (hd : 0 < d) :
    0 ≤ paperGaussianSphereWidth d := by
  simpa only [paperGaussianSphereWidth,paper_sphere_support_eq,sphereWidth] using sphereWidth_nonneg hd

/-- The zero-output-dimensional case has an empty exceptional event. -/
theorem gaussian_escape_zero {n d : ℕ} (hd : 0 < d)
    (U : Euclid 0 →ₗᵢ[ℝ] Euclid n) (t : ℝ) (ht : 0 < t) :
    (sampleLaw n d).real {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ g : Euclid 0, ‖g‖ ∂euclideanGaussianLaw (Fin 0))-paperGaussianSphereWidth d-t} ≤
      Real.exp (-t^2/2) := by
  letI : Nonempty ↥(psdUnit d) := (psdUnit_nonempty hd).to_subtype
  have hzero (X : BMSaddle.Sample n d) : projectedEscape (d := d) (fun _ : PUnit.{1} => U) X=0 := by
    unfold projectedEscape
    have he (p : PUnit.{1} × ↥(psdUnit d)) :
        U.toContinuousLinearMap.adjoint (measurement X p.2)=0 := Subsingleton.elim _ _
    simp only [he,norm_zero,Set.range_const,csInf_singleton]
  have hempty : {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ g : Euclid 0, ‖g‖ ∂euclideanGaussianLaw (Fin 0))-paperGaussianSphereWidth d-t} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    change projectedEscape (d := d) (fun _ : PUnit.{1} => U) X < _ at hX
    have hg (g : Euclid 0) : ‖g‖=0 := by rw [Subsingleton.elim g 0,norm_zero]
    simp only [hzero,hg,integral_zero,zero_sub] at hX
    linarith [paperGaussianSphereWidth_nonneg hd]
  rw [hempty,measureReal_empty]
  exact Real.exp_nonneg _

/-- Exact source threshold and tail for every output dimension, including zero. -/
theorem gaussian_escape_all_output_dimensions {n d r : ℕ} (hd : 0 < d)
    (U : Euclid r →ₗᵢ[ℝ] Euclid n) (t : ℝ) (ht : 0 < t) :
    (sampleLaw n d).real {X | projectedEscape (d := d) (fun _ : PUnit.{1} => U) X <
      (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t} ≤
      Real.exp (-t^2/2) := by
  by_cases hr : r=0
  · subst r
    exact gaussian_escape_zero hd U t ht
  · exact gaussian_escape hd (Nat.pos_of_ne_zero hr) U t ht

#print axioms gaussian_escape_all_output_dimensions
end GaussianEllipsoid.PaperGaussianEscape
