/-
Unconditional Gaussian rotation invariance: discharge of the three
`GaussRotation` premises (P1: `RotDensity`, P2: `RotVolume`,
P3: `RotDensity`) plus the right-inverse identity (`RotVolume`).
-/
import GaussianEllipsoid.GaussRotation
import GaussianEllipsoid.RotDensity
import GaussianEllipsoid.RotVolume

namespace GaussianEllipsoid

open Matrix

theorem piVolume_orthogonal_invariant_true : piVolume_orthogonal_invariant :=
  fun d Q hQ => rotP2_piVolume d Q hQ

theorem gaussianVectorLaw_rotation_uncond (d : ℕ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) :
    (gaussianVectorLaw d).map (fun x => Q *ᵥ x) = gaussianVectorLaw d :=
  gaussianVectorLaw_rotation d Q hQ (rotP2_mul_transpose Q hQ)
    gaussianVectorLaw_density_true piVolume_orthogonal_invariant_true
    measure_eq_of_lintegral_eq_true

end GaussianEllipsoid
