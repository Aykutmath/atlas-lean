import ProjectedDisjointCluster
import PrefixBlockInterfaces
import CanonicalMultiscaleLaw

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

def intervalCoefficients {n : ℕ} (u : Fin n → ℝ) (K L : ℕ) : Fin n → ℝ :=
  fun i => if K ≤ i.val ∧ i.val < L then u i else 0

def intervalEmbedding {n K L : ℕ} (hKL : K ≤ L) (hL : L ≤ n) : Fin (L-K) ↪ Fin n :=
  ⟨fun i => ⟨K+i.val, by omega⟩, fun i j hij => Fin.ext (by have := congrArg Fin.val hij; dsimp at this; omega)⟩

theorem intervalCoefficients_support {n K L : ℕ} (hKL : K ≤ L) (hL : L ≤ n)
    (u : Fin n → ℝ) : ∀ i ∉ Set.range (intervalEmbedding hKL hL), intervalCoefficients u K L i = 0 := by
  intro i hi
  unfold intervalCoefficients
  split_ifs with hh
  · exfalso
    apply hi
    refine ⟨⟨i.val-K, by omega⟩, Fin.ext ?_⟩
    change K + (i.val - K) = i.val
    omega
  · rfl

theorem bilinearSynthesis_coeff_smul {n h : ℕ} (u : Fin n → ℝ)
    (c : ℝ) (X : Fin n → Euclid h × Euclid h) :
    bilinearSynthesis (fun i => c * u i) X = c • bilinearSynthesis u X := by
  unfold bilinearSynthesis
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_smul c (u i) _

/-- Exact coordinate identity between the witness prefix increment and the
original Gaussian projected cluster, including its d^(-1/2) normalization. -/
theorem projectedPrefixBlock_tensor_identity {n h d K L : ℕ}
    (hKL : K ≤ L) (hL : L ≤ n) (u : Fin n → ℝ)
    (z : GaussianEntries n h × GaussianEntries n h) :
    operatorFrobenius (projectedPrefixBlock (fun i => u i / Real.sqrt d)
      (tensorToCanonicalRows n h z) K L) =
    projectedBilinear
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
        (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).1))
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
        (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).2))
      n d z ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) (intervalCoefficients u K L)) := by
  rw [projectedPrefixBlock_eq_residual _ _ hKL]
  have hmask : (fun i : Fin n => if K ≤ i.val ∧ i.val < L then u i / Real.sqrt d else 0) =
      (fun i => (Real.sqrt (d : ℝ))⁻¹ * intervalCoefficients u K L i) := by
    funext i
    unfold intervalCoefficients
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hmask, bilinearSynthesis_coeff_smul]
  have hobs := congrArg frobeniusOperator
    (scaled_bilinearSynthesis_tensorToCanonicalRows n h d (intervalCoefficients u K L) z)
  rw [frobeniusOperator_operatorFrobenius] at hobs
  unfold projectedBilinear
  rw [← hobs]
  unfold leftPrefixProjector rightPrefixProjector
  rw [prefixSpanProjector_eq_selected _ (hKL.trans hL),
    prefixSpanProjector_eq_selected _ (hKL.trans hL)]
  rfl

/-- Actual canonical Gaussian row-law projected-prefix lower tail. The
interval support, independent head law and coordinate identity are proved. -/
theorem canonical_projected_prefix_smallball {n h d K L : ℕ}
    (hKL : K ≤ L) (hL : L ≤ n) (hh : 0 < h) (hbudget : (d : ℝ)/4 + K ≤ h)
    (u : Fin n → ℝ) {σ m R : ℝ} (hσ : 0 < σ)
    (hsum : ∑ i, (intervalCoefficients u K L i)^2 = σ^2)
    (hm : m = ∑ i, |intervalCoefficients u K L i|)
    (hRdef : R = m^2/σ^2) (hR : 4096 ≤ R) (hRd : R ≤ d)
    (hcap : ∀ i, |intervalCoefficients u K L i| ≤ 16*σ/Real.sqrt R) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (fun i => u i / Real.sqrt d) X K L)) <
          projectedConstant * Real.sqrt d * m} ≤ Real.exp (-(d : ℝ)*R/65536) := by
  have hE : MeasurableSet {X : Fin n → Euclid h × Euclid h |
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (fun i => u i / Real.sqrt d) X K L)) <
          projectedConstant * Real.sqrt d * m} :=
    measurableSet_lt (measurable_nuclear_projectedPrefixBlock _ K L) measurable_const
  rw [← (tensorToCanonicalRows_preserving n h).measureReal_preimage hE.nullMeasurableSet]
  have hb := projected_regular_cluster_supported (Fin.castLEEmb (hKL.trans hL))
    (intervalEmbedding hKL hL) (fun i j hij => by
      have he := congrArg Fin.val hij
      change i.val = K + j.val at he
      have hi := i.isLt
      omega) hh hbudget
    ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) (intervalCoefficients u K L))
    (intervalCoefficients_support hKL hL u) hσ hsum hm hRdef hR hRd hcap
  have hevent : (tensorToCanonicalRows n h) ⁻¹'
      {X | spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (fun i => u i / Real.sqrt d) X K L)) <
          projectedConstant * Real.sqrt d * m} =
      {z | spectralNuclearNorm (projectedBilinear
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
          (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).1))
        (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
          (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).2))
        n d z ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) (intervalCoefficients u K L))) <
          projectedConstant * Real.sqrt d * m} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, projectedPrefixBlock_tensor_identity hKL hL]
  rw [hevent]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb

end GaussianEllipsoid.ProjectedClusters
