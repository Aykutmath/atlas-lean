import AHHPathwiseBilinear
import GaussianBilinearContinuity

noncomputable section
open scoped BigOperators
open GaussianTensorTrace GaussianTensorMoments GaussianEllipsoid
namespace AHHAlgebraBridges

/-- Display 2759 on the already formalized Gaussian bilinear operator, with
independent copies left as arbitrary pathwise inputs. -/
theorem gaussianBilinearOperator_four_complex_bound (n h d : ℕ) (hh : 0 < h) (hd : 0 < d)
    (z z' : GaussianEntries n h × GaussianEntries n h) :
    ‖gaussianBilinearOperator n h d z‖ ^ 2 ≤ (h : ℝ) ^ 2 / d *
      ∑ s : Bool, ∑ t : Bool,
        ‖cMatrixCLM (complexCov n h
          (fun i j => z.1 (i,j)) (fun i j => z'.1 (i,j))
          (fun i j => z.2 (i,j)) (fun i j => z'.2 (i,j)) s t)‖ := by
  exact pathwise_real_bilinear_to_complex n h hh (d : ℝ) (Nat.cast_pos.mpr hd) _ _ _ _

/-- Exact all-dimension high-event conclusion for the existing real operator. -/
theorem gaussianBilinearOperator_four_sign_bound_all_d (n d : ℕ)
    (z z' : GaussianEntries n (d / 2) × GaussianEntries n (d / 2))
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hC : ∀ s t : Bool,
      ‖cMatrixCLM (complexCov n (d / 2)
        (fun i j => z.1 (i,j)) (fun i j => z'.1 (i,j))
        (fun i j => z.2 (i,j)) (fun i j => z'.2 (i,j)) s t)‖ ≤ C₀) :
    ‖gaussianBilinearOperator n (d / 2) d z‖ ≤ 2 * Real.sqrt C₀ * Real.sqrt d := by
  exact paper_half_dimension_bound_all_d n d _ _ _ _ C₀ hC₀ hC

end AHHAlgebraBridges
