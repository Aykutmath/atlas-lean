import UCNormalizedRows
import BMMatrixQuadraticSpectral
import BMSpectralPositive
import GaussianLinearAbsMoment

/-! Uniform exponential integrability for actual Frobenius-unit quadratic
rows, the analytic input to the empirical Frobenius-to-l1 continuity event. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open GaussianEllipsoidCandidate
open scoped BigOperators BoundedContinuousFunction InnerProductSpace

namespace GaussianEllipsoid.UCQuadraticMGF

/-- Euclidean operator columns have exactly the matrix Frobenius energy. -/
theorem matrix_operator_frobenius_sq {d : ℕ} (A : Square d) :
    ‖operatorFrobenius (Matrix.toEuclideanCLM (𝕜 := ℝ) A)‖^2 = frobeniusSq A := by
  rw [frobenius_norm_sq, frobeniusSq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.basisFun (Fin d) ℝ i)) j = A j i
  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

/-- Spectral weights retain exact Frobenius energy, without a dimension loss. -/
theorem eigenWeight_energy {d : ℕ} (A : Square d) (hA : A.transpose = A) :
    (∑ i, (BMQuadraticSpectral.eigenWeight (BMQuadraticSpectral.matrixSymmetric hA) i)^2) =
      frobeniusSq A/(d:ℝ) := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let hT := BMQuadraticSpectral.matrixSymmetric hA
  have h := BMGeometry.spectralOp_frobenius_sq
    (hT.eigenvectorBasis finrank_euclideanSpace_fin) (hT.eigenvalues finrank_euclideanSpace_fin)
  rw [BMGeometry.spectral_reconstruction, matrix_operator_frobenius_sq] at h
  simp only [BMQuadraticSpectral.eigenWeight, div_pow, ← Finset.sum_div,
    Real.sq_sqrt (Nat.cast_nonneg d), ← h]

 theorem scaled_eigenWeight_energy {d : ℕ} (hd : 0 < d) (A : Square d) (hA : A.transpose = A) :
    (∑ i, (BMQuadraticSpectral.eigenWeight
      (BMQuadraticSpectral.matrixSymmetric (UCNormalizedRows.scaled_transpose A hA)) i)^2) =
      frobeniusNorm A^2/2 := by
  rw [eigenWeight_energy _ (UCNormalizedRows.scaled_transpose A hA),
    UCNormalizedRows.scaled_frobeniusSq]
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  field_simp

/-- A centered diagonal quadratic with unit coefficient energy has an
absolute exponential moment at a fixed universal scale. -/
theorem diagonal_exp_abs {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : (∑ i, (w i)^2) ≤ 1) :
    Integrable (fun z => Real.exp (|centeredDiagonal w z|/8)) (gaussianProductLaw ι) ∧
      (∫ z, Real.exp (|centeredDiagonal w z|/8) ∂gaussianProductLaw ι) ≤ 2*Real.exp 1 := by
  have hab (i : ι) : |w i| ≤ 1 := by
    have hs := (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)).trans hw
    nlinarith [sq_abs (w i), abs_nonneg (w i)]
  have hp := centeredDiagonal_exp_integrable (fun i => -w i) (b := 4) (t := 1/8)
    (by norm_num) (fun i => by simpa using hab i) (by norm_num) (by norm_num)
  have hn := centeredDiagonal_exp_integrable w (b := 4) (t := 1/8)
    (by norm_num) (fun i => by simpa using hab i) (by norm_num) (by norm_num)
  have he (z : ι → ℝ) : centeredDiagonal (fun i => -w i) z = -centeredDiagonal w z := by
    simp [centeredDiagonal, Finset.sum_neg_distrib]
  simp only [he, neg_mul_neg] at hp
  have hp' : Integrable (fun z => Real.exp (centeredDiagonal w z/8)) (gaussianProductLaw ι) := by
    convert hp using 1 <;> ext z <;> congr 1 <;> ring
  have hn' : Integrable (fun z => Real.exp (-(centeredDiagonal w z/8))) (gaussianProductLaw ι) := by
    convert hn using 1 <;> ext z <;> congr 1 <;> ring
  have hm : Measurable (centeredDiagonal w) := by unfold centeredDiagonal; fun_prop
  have hpoint (z : ι → ℝ) : Real.exp (|centeredDiagonal w z|/8) ≤
      Real.exp (centeredDiagonal w z/8)+Real.exp (-(centeredDiagonal w z/8)) := by
    have h := BMGOEUniform.exp_abs_le_exp_add_exp_neg (centeredDiagonal w z/8)
    simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<8)] using h
  have hi : Integrable (fun z => Real.exp (|centeredDiagonal w z|/8)) (gaussianProductLaw ι) := by
    apply (hp'.add hn').mono' (hm.abs.div_const 8).exp.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint z
  have hpos := centeredDiagonal_mgf_le (fun i => -w i) (b := 4) (t := 1/8)
    (by norm_num) (fun i => by simpa using hab i) (by simpa using hw) (by norm_num) (by norm_num)
  have hneg := centeredDiagonal_mgf_le w (b := 4) (t := 1/8)
    (by norm_num) (fun i => by simpa using hab i) hw (by norm_num) (by norm_num)
  have hIp : (∫ z, Real.exp (centeredDiagonal w z/8) ∂gaussianProductLaw ι) ≤ Real.exp 1 := by
    have hh : (∫ z, Real.exp (centeredDiagonal w z/8) ∂gaussianProductLaw ι) ≤ Real.exp ((1/8:ℝ)^2*4) := by
      convert hpos using 1 <;> simp only [mgf, he] <;> congr 1 <;> funext z <;> congr 1 <;> ring
    exact hh.trans (Real.exp_le_exp.mpr (by norm_num))
  have hIn : (∫ z, Real.exp (-(centeredDiagonal w z/8)) ∂gaussianProductLaw ι) ≤ Real.exp 1 := by
    have hh : (∫ z, Real.exp (-(centeredDiagonal w z/8)) ∂gaussianProductLaw ι) ≤ Real.exp ((1/8:ℝ)^2*4) := by
      convert hneg using 1 <;> simp only [mgf] <;> congr 1 <;> funext z <;> congr 1 <;> ring
    exact hh.trans (Real.exp_le_exp.mpr (by norm_num))
  refine ⟨hi, ?_⟩
  have h := integral_mono hi (hp'.add hn') hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hp' hn'] at h
  linarith

/-- The actual project row Q(A) has a universal exponential absolute moment
for every symmetric Frobenius-unit-or-smaller test matrix. -/
theorem quadratic_exp_abs {d : ℕ} (hd : 0 < d) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A ≤ 1) :
    Integrable (fun x => Real.exp (|(quadratic A x-Matrix.trace A)/Real.sqrt 2|/8))
      (gaussianVectorLaw d) ∧
    (∫ x, Real.exp (|(quadratic A x-Matrix.trace A)/Real.sqrt 2|/8)
      ∂gaussianVectorLaw d) ≤ 2*Real.exp 1 := by
  let w := BMQuadraticSpectral.eigenWeight
    (BMQuadraticSpectral.matrixSymmetric (UCNormalizedRows.scaled_transpose A hA))
  have hw : (∑ i, (w i)^2) ≤ 1 := by
    rw [show (∑ i, (w i)^2)=frobeniusNorm A^2/2 from scaled_eigenWeight_energy hd A hA]
    have hsq : frobeniusNorm A^2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (frobeniusNorm_nonneg A) hF 2
    linarith
  have hid := BMQuadraticSpectral.eval_normalizedQuadratic_identDistrib
    (UCNormalizedRows.scaled_transpose A hA)
  have hid' : IdentDistrib (fun x => (quadratic A x-Matrix.trace A)/Real.sqrt 2)
      (centeredDiagonal w) (gaussianVectorLaw d) (gaussianProductLaw (Fin d)) := by
    simpa only [UCNormalizedRows.eval_scaled hd, gaussianVectorLaw, gaussianProductLaw] using hid
  have hexp := hid'.comp (by fun_prop : Measurable (fun t : ℝ => Real.exp (|t|/8)))
  have hi := diagonal_exp_abs w hw
  exact ⟨hexp.integrable_iff.mpr hi.1, hexp.integral_eq.trans_le hi.2⟩

#print axioms quadratic_exp_abs
end GaussianEllipsoid.UCQuadraticMGF
