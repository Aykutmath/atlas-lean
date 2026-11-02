import BilinearSynthesis
import CoordinateBlockPinching

open scoped InnerProductSpace
open GaussianEllipsoid
namespace GaussianEllipsoidCandidate

/-- Compression of a genuine rank-one operator, with adjoints on the domain. -/
theorem compress_bilinearRowOperator {d r q : ℕ}
    (P : Euclid d →L[ℝ] Euclid r) (Q : Euclid q →L[ℝ] Euclid d)
    (x : Euclid d) :
    P ∘L bilinearRowOperator (x,x) ∘L Q =
      bilinearRowOperator (ContinuousLinearMap.adjoint Q x, P x) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, bilinearRowOperator_apply, map_smul]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Centered quadratic synthesis before a deterministic normalization. -/
noncomputable def centeredRankOneSynthesis {n d : ℕ} (y : Fin n → ℝ)
    (X : Fin n → Euclid d) : Euclid d →L[ℝ] Euclid d :=
  (∑ i, y i • bilinearRowOperator (X i,X i)) -
    (∑ i, y i) • ContinuousLinearMap.id ℝ (Euclid d)

/-- Every scalar identity centering vanishes in orthogonal rectangular
compression, including sample-dependent trace centerings. -/
theorem compress_quadratic_minus_scalar {n d r q : ℕ}
    (P : Euclid d →L[ℝ] Euclid r) (Q : Euclid q →L[ℝ] Euclid d)
    (hPQ : P ∘L Q = 0) (y : Fin n → ℝ) (X : Fin n → Euclid d) (c : ℝ) :
    P ∘L ((∑ i, y i • bilinearRowOperator (X i,X i)) -
      c • ContinuousLinearMap.id ℝ (Euclid d)) ∘L Q =
      bilinearSynthesis y (fun i => (ContinuousLinearMap.adjoint Q (X i), P (X i))) := by
  apply ContinuousLinearMap.ext
  intro v
  have hpq : P (Q v) = 0 := by
    have hv := congrArg (fun T : Euclid q →L[ℝ] Euclid r => T v) hPQ
    simpa using hv
  simp only [bilinearSynthesis,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_sum, map_smul, hpq, smul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun T : Euclid q →L[ℝ] Euclid r => T v)
    (compress_bilinearRowOperator P Q (X i))

/-- Centering vanishes in any orthogonal rectangular compression. -/
theorem compress_centeredRankOneSynthesis {n d r q : ℕ}
    (P : Euclid d →L[ℝ] Euclid r) (Q : Euclid q →L[ℝ] Euclid d)
    (hPQ : P ∘L Q = 0) (y : Fin n → ℝ) (X : Fin n → Euclid d) :
    P ∘L centeredRankOneSynthesis y X ∘L Q =
      bilinearSynthesis y (fun i => (ContinuousLinearMap.adjoint Q (X i), P (X i))) := by
  exact compress_quadratic_minus_scalar P Q hPQ y X (∑ i, y i)

/-- The rectangular bilinear lower bound transfers to the centered full
quadratic synthesis without a zero-sum coefficient restriction. -/
theorem bilinear_nuclear_le_centered {n d r q : ℕ}
    (P : Euclid d →L[ℝ] Euclid r) (Q : Euclid q →L[ℝ] Euclid d)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hPQ : P ∘L Q = 0)
    (y : Fin n → ℝ) (X : Fin n → Euclid d) (a : ℝ) :
    spectralNuclearNorm (operatorFrobenius (a •
      bilinearSynthesis y (fun i => (ContinuousLinearMap.adjoint Q (X i), P (X i))))) ≤
    spectralNuclearNorm (operatorFrobenius (a • centeredRankOneSynthesis y X)) := by
  have h := spectralNuclear_compression_le P (a • centeredRankOneSynthesis y X) Q hP hQ
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    compress_centeredRankOneSynthesis P Q hPQ] using h

/-- Disjoint coordinate insertions have zero cross-adjoint. -/
theorem disjoint_coordinate_cross_zero {d r q : ℕ}
    (eL : Fin r ↪ Fin d) (eR : Fin q ↪ Fin d)
    (hdis : ∀ i j, eL i ≠ eR j) :
    ContinuousLinearMap.adjoint (coordinateEmbedding eL) ∘L coordinateEmbedding eR = 0 := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, coordinateEmbedding_adjoint_apply,
    ContinuousLinearMap.zero_apply, PiLp.zero_apply, coordinateEmbedding_apply,
    euclid_sum_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp [hdis i j, Ne.symm (hdis i j)]

/-- Literal full-sample coordinate extraction, before any Gaussian assumption. -/
noncomputable def extractedRows {n d r q : ℕ}
    (eL : Fin r ↪ Fin d) (eR : Fin q ↪ Fin d) (X : Fin n → Euclid d) :
    Fin n → Euclid q × Euclid r := fun i =>
      (ContinuousLinearMap.adjoint (coordinateEmbedding eR) (X i),
        ContinuousLinearMap.adjoint (coordinateEmbedding eL) (X i))

theorem extractedRows_fst {n d r q : ℕ}
    (eL : Fin r ↪ Fin d) (eR : Fin q ↪ Fin d) (X : Fin n → Euclid d)
    (i : Fin n) (j : Fin q) : (extractedRows eL eR X i).1 j = X i (eR j) := by
  exact coordinateEmbedding_adjoint_apply eR (X i) j

theorem extractedRows_snd {n d r q : ℕ}
    (eL : Fin r ↪ Fin d) (eR : Fin q ↪ Fin d) (X : Fin n → Euclid d)
    (i : Fin n) (j : Fin r) : (extractedRows eL eR X i).2 j = X i (eL j) := by
  exact coordinateEmbedding_adjoint_apply eL (X i) j

/-- Direct norm transfer from the independent rectangular block to centered
quadratic measurements. Any normalization, including d^(-1/2), is permitted. -/
theorem extracted_bilinear_nuclear_le_centered {n d r q : ℕ}
    (eL : Fin r ↪ Fin d) (eR : Fin q ↪ Fin d)
    (hdis : ∀ i j, eL i ≠ eR j) (y : Fin n → ℝ) (X : Fin n → Euclid d) (a : ℝ) :
    spectralNuclearNorm (operatorFrobenius (a • bilinearSynthesis y (extractedRows eL eR X))) ≤
    spectralNuclearNorm (operatorFrobenius (a • centeredRankOneSynthesis y X)) := by
  apply bilinear_nuclear_le_centered
    (ContinuousLinearMap.adjoint (coordinateEmbedding eL)) (coordinateEmbedding eR)
  · simpa using coordinateEmbedding_norm_le_one eL
  · exact coordinateEmbedding_norm_le_one eR
  · exact disjoint_coordinate_cross_zero eL eR hdis

#print axioms compress_quadratic_minus_scalar
#print axioms compress_bilinearRowOperator
#print axioms compress_centeredRankOneSynthesis
#print axioms bilinear_nuclear_le_centered
#print axioms disjoint_coordinate_cross_zero
#print axioms extractedRows_fst
#print axioms extractedRows_snd
#print axioms extracted_bilinear_nuclear_le_centered
end GaussianEllipsoidCandidate
