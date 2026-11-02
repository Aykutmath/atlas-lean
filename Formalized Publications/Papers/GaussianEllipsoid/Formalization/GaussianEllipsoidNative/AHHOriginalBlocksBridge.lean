import AHHGaussianBilinearBridge
import PaperBilinearOriginalBlocks

noncomputable section
open scoped BigOperators
open GaussianTensorTrace GaussianTensorMoments GaussianEllipsoid
open GaussianEllipsoid.ProjectedClusters
namespace AHHAlgebraBridges

/-- Display 2759 on the literal original first/last floor(d/2) coordinate
blocks of the manuscript, with the exact existing Frobenius operator. -/
theorem paperBilinearOperator_four_complex_bound (n d : ℕ) (hd : 2 ≤ d)
    (x x' : Fin n → Euclid d) :
    ‖paperBilinearOperator d n x‖ ^ 2 ≤ ((d / 2 : ℕ) : ℝ) ^ 2 / d *
      ∑ s : Bool, ∑ t : Bool,
        ‖cMatrixCLM (complexCov n (d / 2)
          (fun i j => x i (paperBlockLeft d j)) (fun i j => x' i (paperBlockLeft d j))
          (fun i j => x i (paperBlockRight d j)) (fun i j => x' i (paperBlockRight d j)) s t)‖ := by
  exact gaussianBilinearOperator_four_complex_bound n (d / 2) d (by omega) (by omega)
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x)
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x')

/-- All original dimensions, including d=0 and d=1, with explicit norm constant. -/
theorem paperBilinearOperator_four_sign_bound_all_d (n d : ℕ)
    (x x' : Fin n → Euclid d) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hC : ∀ s t : Bool,
      ‖cMatrixCLM (complexCov n (d / 2)
        (fun i j => x i (paperBlockLeft d j)) (fun i j => x' i (paperBlockLeft d j))
        (fun i j => x i (paperBlockRight d j)) (fun i j => x' i (paperBlockRight d j)) s t)‖ ≤ C₀) :
    ‖paperBilinearOperator d n x‖ ≤ 2 * Real.sqrt C₀ * Real.sqrt d := by
  exact gaussianBilinearOperator_four_sign_bound_all_d n d
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x)
    (splitCoordinateRows n (paperBlockLeft d) (paperBlockRight d) x') C₀ hC₀ hC

end AHHAlgebraBridges
