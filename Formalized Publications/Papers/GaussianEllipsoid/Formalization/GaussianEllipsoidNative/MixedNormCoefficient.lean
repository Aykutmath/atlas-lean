import FlatBilinearAssembly

noncomputable section
open GaussianEllipsoidFinalPassage
namespace GaussianEllipsoidStandalone

theorem reciprocal_eta_max : max (1/numericalEta^2) 1 = 1/numericalEta^2 := by
  apply max_eq_left
  have hη := numerical_eta_range
  norm_num [numericalEta]

theorem reciprocal_eta_sqrt : Real.sqrt (1/numericalEta^2) = 1/numericalEta := by
  have he : 1/numericalEta^2 = (1/numericalEta)^2 := by ring
  rw [he, Real.sqrt_sq (div_nonneg (by norm_num) numerical_eta_range.1.le)]

theorem reciprocal_eta_log : Real.log (1/numericalEta^2) = 2*Real.log (1/numericalEta) := by
  have he : 1/numericalEta^2 = (1/numericalEta)^2 := by ring
  rw [he, Real.log_pow]
  norm_num

/-- Exact rescaling of the actual multiscale coefficient at K=η⁻². -/
theorem fixed_sparse_coefficient_eq :
    fixedSparseCoefficient = (1/2:ℝ)^30 /
      (Real.sqrt (max (1/numericalEta^2) 1) * (1+Real.log (max (1/numericalEta^2) 1))) := by
  rw [reciprocal_eta_max, reciprocal_eta_sqrt, reciprocal_eta_log]
  unfold fixedSparseCoefficient fixedHeadCoefficient numericalDlog
  field_simp

end GaussianEllipsoidStandalone
