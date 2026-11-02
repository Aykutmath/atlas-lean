import AHHLipschitzCounterexample

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open WithLp

namespace AHHLipschitzCounterexample

/-- Euclidean norm multiplicativity for the coordinate pure tensor. -/
theorem pureTensor_norm_sq (u v : LocalSpace) :
    ‖pureTensor u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, pureTensor, Fintype.sum_prod_type,
    PiLp.toLp_apply, norm_mul, mul_pow, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem pureTensor_unit (u v : LocalSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖pureTensor u v‖ = 1 := by
  have h := pureTensor_norm_sq u v
  rw [hu, hv] at h
  nlinarith [norm_nonneg (pureTensor u v)]

/-- With one sample, the scalar AHH function is constant on unit configurations. -/
theorem function_one_sample {ι : Type*} [Fintype ι] [Unique ι]
    (X : Configuration ι) (hX : UnitConfiguration X) : ahhFunction X = 1 := by
  unfold ahhFunction
  rw [ahhMatrix_eq_sum_projectors]
  simp only [Fintype.sum_unique, projector_toEuclideanCLM, InnerProductSpace.norm_rankOne,
    pureTensor_unit _ _ (hX 0 default) (hX 1 default), one_mul]

/-- Rational unit vectors (4/5,3/5) and (3/5,4/5) in the actual complex local space. -/
def rationalVector (s : Fin 2) : LocalSpace :=
  toLp 2 (fun j => if j = s then (4 / 5 : ℂ) else 3 / 5)

theorem rationalVector_norm (s : Fin 2) : ‖rationalVector s‖ = 1 := by
  have hs : ‖rationalVector s‖ ^ 2 = 1 := by
    fin_cases s <;>
      norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, rationalVector, norm_div]
  nlinarith [norm_nonneg (rationalVector s)]

theorem basis_rational_sub_sq (s : Fin 2) :
    ‖basisVector s - rationalVector s‖ ^ 2 = 2 / 5 := by
  fin_cases s <;>
    norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, rationalVector,
      basisVector_apply, norm_div]

/-- The perturbed configuration with exactly p=2 samples. -/
def rationalConfig : Configuration (Fin 2 × Fin 1) :=
  fun a s => if a = 0 then rationalVector s.1 else basisVector 0

theorem rationalConfig_unit : UnitConfiguration rationalConfig := by
  intro a s
  dsimp [rationalConfig]
  split_ifs
  · exact rationalVector_norm _
  · exact basisVector_norm _

theorem rational_distance :
    ahhDistance (configA 1) rationalConfig = Real.sqrt (4 / 5) := by
  norm_num [ahhDistance, configA, rationalConfig, Fin.sum_univ_two,
    Fintype.sum_prod_type, basis_rational_sub_sq]

/-- A nonzero eigenvector supported on the two active tensor coordinates. -/
def eigenWitness : TensorSpace :=
  toLp 2 (fun i => if i.2 = 0 then 1 else 0)

theorem eigenWitness_ne_zero : eigenWitness ≠ 0 := by
  intro h
  have h' := congrArg (fun v : TensorSpace => v (0, 0)) h
  norm_num [eigenWitness] at h'

theorem rational_eigenvector :
    (Matrix.toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)) (ahhMatrix rationalConfig) eigenWitness =
      (49 / 25 : ℂ) • eigenWitness := by
  simp only [eigenWitness, Matrix.toEuclideanCLM_toLp]
  ext ⟨i₁, i₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;>
    norm_num [Matrix.mulVec, dotProduct, Matrix.sum_apply, ahhMatrix, rationalConfig, rationalVector,
      projector, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat]

/-- Lower bound in the genuine Euclidean operator norm, using the explicit eigenvector. -/
theorem rational_function_lower : 49 / 25 ≤ ahhFunction rationalConfig := by
  have h := ((Matrix.toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)) (ahhMatrix rationalConfig)).le_opNorm eigenWitness
  rw [rational_eigenvector, norm_smul] at h
  have hw : 0 < ‖eigenWitness‖ := norm_pos_iff.mpr eigenWitness_ne_zero
  apply (mul_le_mul_iff_right₀ hw).mp
  simpa [ahhFunction, norm_div, mul_comm] using h

/-- The selfadjoint swap on the active two-coordinate block, zero on its complement. -/
def activeSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if i.2 = 0 ∧ j.2 = 0 ∧ i.1 ≠ j.1 then 1 else 0

theorem activeSwap_star_mul : star activeSwap * activeSwap = ahhMatrix (configA 1) := by
  rw [matrixA]
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [activeSwap, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem activeSwap_norm : ‖activeSwap‖ = 1 := by
  have h := CStarRing.norm_star_mul_self (x := activeSwap)
  rw [activeSwap_star_mul, ← ahhFunction_eq_l2_matrix_norm, functionA] at h
  norm_num at h
  nlinarith [norm_nonneg activeSwap]

theorem rational_matrix_decomposition :
    ahhMatrix rationalConfig = ahhMatrix (configA 1) + (24 / 25 : ℂ) • activeSwap := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [Matrix.sum_apply, ahhMatrix, rationalConfig, rationalVector, configA, activeSwap,
      projector, Matrix.kronecker_apply, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat]

/-- The exact value, established by the eigenvector lower bound and a norm upper bound. -/
theorem rational_function : ahhFunction rationalConfig = 49 / 25 := by
  apply le_antisymm _ rational_function_lower
  rw [ahhFunction_eq_l2_matrix_norm, rational_matrix_decomposition]
  calc
    _ ≤ ‖ahhMatrix (configA 1)‖ + ‖(24 / 25 : ℂ) • activeSwap‖ := norm_add_le _ _
    _ = 49 / 25 := by
      rw [← ahhFunction_eq_l2_matrix_norm, functionA, norm_smul, activeSwap_norm]
      norm_num [norm_div]

/-- A minimal-sample counterexample: k=d=p=2, with exact values and metric. -/
theorem counterexample_p2 :
    UnitConfiguration (configA 1) ∧ UnitConfiguration rationalConfig ∧
    Fintype.card (Fin 2 × Fin 1) = 2 ∧
    ahhFunction (configA 1) = 1 ∧ ahhFunction rationalConfig = 49 / 25 ∧
    ahhDistance (configA 1) rationalConfig = Real.sqrt (4 / 5) ∧
    ahhDistance (configA 1) rationalConfig <
      |ahhFunction (configA 1) - ahhFunction rationalConfig| := by
  refine ⟨configA_unit 1, rationalConfig_unit, by simp, (by simpa using functionA 1),
    rational_function, rational_distance, ?_⟩
  rw [functionA, rational_function, rational_distance]
  have hs : Real.sqrt (4 / 5 : ℝ) < 24 / 25 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  simpa only [Nat.cast_one, show |(1 : ℝ) - 49 / 25| = 24 / 25 by norm_num] using hs

theorem not_one_lipschitz_p2 :
    ¬ (∀ X Y : Configuration (Fin 2 × Fin 1),
      UnitConfiguration X → UnitConfiguration Y →
      |ahhFunction X - ahhFunction Y| ≤ ahhDistance X Y) := by
  intro h
  exact (not_le_of_gt counterexample_p2.2.2.2.2.2.2)
    (h _ _ (configA_unit 1) rationalConfig_unit)

end AHHLipschitzCounterexample
