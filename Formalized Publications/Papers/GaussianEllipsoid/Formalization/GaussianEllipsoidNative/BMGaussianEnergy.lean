import BMIsotropicGaussian

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

variable {ι : Type*} [Fintype ι]

theorem gaussian_coordinate_integrable_pow (i : ι) (n : ℕ) :
    Integrable (fun x : ι → ℝ => (x i)^n) (gaussianProductLaw ι) := by
  have h := standardGaussian_integrable_pow n
  rw [← gaussianProductLaw_coordinate i] at h
  exact (integrable_map_measure ((continuous_pow n).aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable).mp h

theorem gaussian_coordinate_moment (i : ι) (n : ℕ) :
    (∫ x : ι → ℝ, (x i)^n ∂gaussianProductLaw ι) =
      ∫ z : ℝ, z^n ∂gaussianReal 0 1 := by
  rw [← gaussianProductLaw_coordinate i]
  exact (integral_map (φ := fun x : ι → ℝ => x i)
    (f := fun z : ℝ => z^n) (measurable_pi_apply i).aemeasurable
    (continuous_pow n).aestronglyMeasurable).symm

theorem gaussian_coordinate_mean (i : ι) :
    (∫ x : ι → ℝ, x i ∂gaussianProductLaw ι) = 0 := by
  simpa only [pow_one, standardGaussian_moment_one] using gaussian_coordinate_moment i 1

theorem gaussian_coordinate_second (i : ι) :
    (∫ x : ι → ℝ, (x i)^2 ∂gaussianProductLaw ι) = 1 := by
  rw [gaussian_coordinate_moment]
  simpa using standardGaussian_moment_even 1

theorem gaussian_coordinate_mul_integrable (i j : ι) :
    Integrable (fun x : ι → ℝ => x i * x j) (gaussianProductLaw ι) := by
  have h := gaussianProductLaw_integrable_endpoints (fun k : Fin 2 => ![i,j] k)
  simpa [Fin.prod_univ_two] using h

theorem gaussian_coordinate_covariance [DecidableEq ι] (i j : ι) :
    (∫ x : ι → ℝ, x i * x j ∂gaussianProductLaw ι) = if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j
    simpa [pow_two] using gaussian_coordinate_second i
  · have hi := (gaussianProductLaw_iIndepFun (ι := ι)).indepFun h
    have hh := hi.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
    simpa [h, gaussian_coordinate_mean] using hh

theorem gaussian_coordinate_average_sq_integrable (i j : ι) :
    Integrable (fun x : ι → ℝ => ((x i + x j)/2)^2) (gaussianProductLaw ι) := by
  have h := ((gaussian_coordinate_integrable_pow i 2).add
    ((gaussian_coordinate_mul_integrable i j).const_mul 2)).add
    (gaussian_coordinate_integrable_pow j 2)
  convert h.div_const 4 using 1
  funext x
  change ((x i+x j)/2)^2 = ((x i)^2 + 2*(x i*x j) + (x j)^2)/4
  ring

theorem gaussian_coordinate_average_sq_mean [DecidableEq ι] (i j : ι) :
    (∫ x : ι → ℝ, ((x i + x j)/2)^2 ∂gaussianProductLaw ι) =
      (1/2 : ℝ) + if i=j then 1/2 else 0 := by
  have heq : (fun x : ι → ℝ => ((x i + x j)/2)^2) =
      fun x => ((x i)^2 + 2*(x i*x j) + (x j)^2)/4 := by funext x; ring
  rw [heq]
  simp_rw [div_eq_mul_inv]
  have hi : Integrable (fun x : ι → ℝ => (x i)^2 + 2*(x i*x j)) (gaussianProductLaw ι) :=
    (gaussian_coordinate_integrable_pow i 2).add ((gaussian_coordinate_mul_integrable i j).const_mul 2)
  rw [integral_mul_const, integral_add hi (gaussian_coordinate_integrable_pow j 2),
    integral_add (gaussian_coordinate_integrable_pow i 2)
      ((gaussian_coordinate_mul_integrable i j).const_mul 2), integral_const_mul,
    gaussian_coordinate_second, gaussian_coordinate_second, gaussian_coordinate_covariance]
  split_ifs <;> norm_num

def gaussianSymmetricEnergy (d : ℕ) (x : (Fin d × Fin d) → ℝ) : ℝ :=
  ‖operatorFrobenius (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x))‖^2

theorem gaussianSymmetricEnergy_entries (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    gaussianSymmetricEnergy d x = ∑ j : Fin d, ∑ i : Fin d, ((x (i,j)+x (j,i))/2)^2 := by
  rw [gaussianSymmetricEnergy, isotropicSymmetricOp_frobenius, frobenius_norm_sq]
  simp only [frobeniusToMatrix, symmetricFrob_apply]
  rfl

theorem gaussianSymmetricEnergy_integrable (d : ℕ) :
    Integrable (gaussianSymmetricEnergy d) (gaussianProductLaw (Fin d × Fin d)) := by
  change Integrable (fun x => gaussianSymmetricEnergy d x) _
  simp_rw [gaussianSymmetricEnergy_entries]
  exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ =>
    gaussian_coordinate_average_sq_integrable (i,j) (j,i)

/-- The exact symmetric-space dimension arises from the actual iid Gaussian entry law. -/
theorem gaussianSymmetricEnergy_mean (d : ℕ) :
    (∫ x, gaussianSymmetricEnergy d x ∂gaussianProductLaw (Fin d × Fin d)) =
      (d : ℝ) * (d+1)/2 := by
  simp only [gaussianSymmetricEnergy_entries]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun i _ =>
    gaussian_coordinate_average_sq_integrable (i,j) (j,i))]
  simp_rw [integral_finset_sum _ (fun i _ => gaussian_coordinate_average_sq_integrable _ _),
    gaussian_coordinate_average_sq_mean]
  have hpair (i j : Fin d) : ((i,j)=(j,i)) ↔ i=j := by simp [Prod.ext_iff]; tauto
  simp_rw [hpair, Finset.sum_add_distrib]
  simp
  ring

theorem gaussianProductLaw_neg_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (fun x : ι → ℝ => -x) (gaussianProductLaw ι) (gaussianProductLaw ι) := by
  have hscalar : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    refine ⟨measurable_neg, ?_⟩
    simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) (-1)
  exact measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1) (fun _ => hscalar)

def gaussianPSDSupportRaw (d : ℕ) (x : (Fin d × Fin d) → ℝ) : ℝ :=
  gaussianPSDSupport d ((WithLp.equiv 2 _).symm x)

theorem gaussianPSDSupportRaw_continuous (d : ℕ) : Continuous (gaussianPSDSupportRaw d) :=
  (gaussianPSDSupport_continuous d).comp (PiLp.continuous_toLp _ _)

theorem gaussianPSDSupportRaw_sign_energy (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    (gaussianPSDSupportRaw d x)^2 + (gaussianPSDSupportRaw d (-x))^2 = gaussianSymmetricEnergy d x := by
  exact gaussianPSDSupport_sign_energy d ((WithLp.equiv 2 _).symm x)

theorem gaussianPSDSupportRaw_sq_integrable (d : ℕ) :
    Integrable (fun x => (gaussianPSDSupportRaw d x)^2) (gaussianProductLaw (Fin d × Fin d)) := by
  apply (gaussianSymmetricEnergy_integrable d).mono' ((gaussianPSDSupportRaw_continuous d).pow 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (gaussianPSDSupportRaw d x)^2 ≤ gaussianSymmetricEnergy d x
    have h := gaussianPSDSupportRaw_sign_energy d x
    nlinarith [sq_nonneg (gaussianPSDSupportRaw d (-x))]

/-- Exact PSD statistical dimension, proved by sign symmetry and spectral Pythagoras. -/
theorem gaussianPSDSupportRaw_second_moment (d : ℕ) :
    (∫ x, (gaussianPSDSupportRaw d x)^2 ∂gaussianProductLaw (Fin d × Fin d)) =
      (d : ℝ) * (d+1)/4 := by
  let μ := gaussianProductLaw (Fin d × Fin d)
  have hneg : (∫ x, (gaussianPSDSupportRaw d (-x))^2 ∂μ) =
      ∫ x, (gaussianPSDSupportRaw d x)^2 ∂μ :=
    (gaussianProductLaw_neg_preserving (Fin d × Fin d)).integral_comp measurableEmbedding_neg
      (fun x => (gaussianPSDSupportRaw d x)^2)
  have hineg : Integrable (fun x => (gaussianPSDSupportRaw d (-x))^2) μ :=
    ((gaussianProductLaw_neg_preserving _).integrable_comp
      ((gaussianPSDSupportRaw_continuous d).pow 2).aestronglyMeasurable).mpr
      (gaussianPSDSupportRaw_sq_integrable d)
  have hsplit : (∫ x, (gaussianPSDSupportRaw d x)^2 + (gaussianPSDSupportRaw d (-x))^2 ∂μ) =
      (d : ℝ)*(d+1)/2 := by
    simp_rw [gaussianPSDSupportRaw_sign_energy]
    exact gaussianSymmetricEnergy_mean d
  rw [integral_add (gaussianPSDSupportRaw_sq_integrable d) hineg, hneg] at hsplit
  linarith

end BMGeometry
