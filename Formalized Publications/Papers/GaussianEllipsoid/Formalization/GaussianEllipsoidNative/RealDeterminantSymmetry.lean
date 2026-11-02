import RealDeterminantExpectation
import RegularizedExpectationSymmetry
import CappedSimplexRemainder
noncomputable section
open MeasureTheory Matrix Finset Set
namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
/-- An iid product measure makes the actual regularized moment permutation invariant. -/
theorem regularizedRealMoment_perm (μ : Measure (ι → ℝ)) [SigmaFinite μ]
    (ε : ℝ) (s : ℝ) (w : κ → ℝ) (e : Equiv.Perm κ) :
    regularizedRealMoment (Measure.pi (fun _ : κ => μ)) ε s (w ∘ e) =
      regularizedRealMoment (Measure.pi (fun _ : κ => μ)) ε s w := by
  let T := MeasurableEquiv.piCongrLeft (fun _ : κ => ι → ℝ) e.symm
  have hT := measurePreserving_piCongrLeft (fun _ : κ => μ) e.symm
  have h := hT.integral_comp T.measurableEmbedding
    (fun g => (regularizedGram ε g (w ∘ e)).det ^ (-s))
  have hfun : (fun g : κ → ι → ℝ =>
      (regularizedGram ε (T g) (w ∘ e)).det ^ (-s)) =
      (fun g => (regularizedGram ε g w).det ^ (-s)) := by
    funext g
    have hg : T g = g ∘ e := by
      funext k
      simpa [T] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ι → ℝ) e.symm g (e k)
    rw [hg, regularizedGram_reindex]
  change (∫ g, (regularizedGram ε g (w ∘ e)).det ^ (-s)
    ∂Measure.pi (fun _ : κ => μ)) = _
  rw [← h]
  rw [hfun]
  rfl


end GaussianEllipsoid.CappedSimplex
