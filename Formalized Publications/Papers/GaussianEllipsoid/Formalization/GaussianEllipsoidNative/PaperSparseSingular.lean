import CanonicalDimensionCompression
import GaussianMatrixColumns
import Mathlib.Data.EReal.Operations

noncomputable section
open MeasureTheory Finset GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Basis-independent least singular value, with +infinity for empty unit sphere. -/
def paperLeastSingularValue {q h : ℕ} (T : Euclid q →L[ℝ] Euclid h) : EReal :=
  sInf {s : EReal | ∃ v : Euclid q, ‖v‖ = 1 ∧ s = (‖T v‖:EReal)}

theorem paperLeastSingularValue_ge_iff {q h : ℕ} (T : Euclid q →L[ℝ] Euclid h) (c : ℝ) :
    (c:EReal) ≤ paperLeastSingularValue T ↔ ∀ v : Euclid q, ‖v‖ = 1 → c ≤ ‖T v‖ := by
  constructor
  · intro h v hv
    have hh := (le_sInf_iff.mp h) _ ⟨v,hv,rfl⟩
    exact_mod_cast hh
  · intro h
    apply le_sInf
    rintro s ⟨v,hv,rfl⟩
    exact_mod_cast h v hv

/-- The literal small-support singular event with one common absolute c_s
for both the singular lower bound and failure exponent: c_s=1/2048. -/
def paperSparseSingularGood (d n h : ℕ) : Set (Fin n → Euclid h × Euclid h) :=
  {X | ∀ I : Finset (Fin n), 1 ≤ I.card → I.card ≤ sparseSupportSize d →
    (((1/2048:ℝ)*Real.sqrt d : ℝ):EReal) ≤
      paperLeastSingularValue (supportOperator h n I (rowsToMatrixPair h n X).1) ∧
    (((1/2048:ℝ)*Real.sqrt d : ℝ):EReal) ≤
      paperLeastSingularValue (supportOperator h n I (rowsToMatrixPair h n X).2)}

theorem paperSparseSingularGood_isClosed (d n h : ℕ) : IsClosed (paperSparseSingularGood d n h) := by
  unfold paperSparseSingularGood
  simp only [paperLeastSingularValue_ge_iff,Set.setOf_forall,Set.setOf_and]
  apply isClosed_iInter
  intro I
  apply isClosed_iInter
  intro hI1
  apply isClosed_iInter
  intro hI
  apply IsClosed.inter
  · apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro hv
    have hc : Continuous (fun X : Fin n → Euclid h × Euclid h => (rowsToMatrixPair h n X).1) := by
      dsimp [rowsToMatrixPair]
      fun_prop
    exact isClosed_le continuous_const
      (((supportOperator_continuous h n I).comp hc).clm_apply continuous_const).norm
  · apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro hv
    have hc : Continuous (fun X : Fin n → Euclid h × Euclid h => (rowsToMatrixPair h n X).2) := by
      dsimp [rowsToMatrixPair]
      fun_prop
    exact isClosed_le continuous_const
      (((supportOperator_continuous h n I).comp hc).clm_apply continuous_const).norm

theorem supportOperator_coordinate_compress {n k h : ℕ} (e : Fin k ↪ Fin h)
    (I : Finset (Fin n)) (Y : Fin n → Euclid h) (v : Euclid I.card) :
    supportOperator k n I
      (fun p => (ContinuousLinearMap.adjoint (coordinateEmbedding e) (Y p.2)) p.1) v =
      ContinuousLinearMap.adjoint (coordinateEmbedding e)
        (supportOperator h n I (fun p => Y p.2 p.1) v) := by
  ext a
  rw [coordinateEmbedding_adjoint_apply,supportOperator_apply,supportOperator_apply]
  simp only [coordinateEmbedding_adjoint_apply]

theorem supportOperator_coordinate_norm_le {n k h : ℕ} (e : Fin k ↪ Fin h)
    (I : Finset (Fin n)) (Y : Fin n → Euclid h) (v : Euclid I.card) :
    ‖supportOperator k n I
      (fun p => (ContinuousLinearMap.adjoint (coordinateEmbedding e) (Y p.2)) p.1) v‖ ≤
      ‖supportOperator h n I (fun p => Y p.2 p.1) v‖ := by
  rw [supportOperator_coordinate_compress]
  have hU : ‖ContinuousLinearMap.adjoint (coordinateEmbedding e)‖ ≤ 1 := by
    simpa using coordinateEmbedding_norm_le_one e
  exact ((ContinuousLinearMap.adjoint (coordinateEmbedding e)).le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hU (norm_nonneg _))

theorem singular_numeric_lower (d : ℕ) {x : ℝ} (hx : 0 ≤ x) (hsq : (d:ℝ)/12 ≤ x^2) :
    (1/2048:ℝ)*Real.sqrt d ≤ x := by
  apply (sq_le_sq₀ (by positivity) hx).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
  nlinarith [Nat.cast_nonneg d (α:=ℝ)]

theorem sparseRowsGood_compress_subset_paperSparseGood {d n h : ℕ}
    (hd : 24 ≤ d) (hkh : 2*(d/4) ≤ h) :
    compressCanonicalRows (ContinuousLinearMap.adjoint (coordinateEmbedding (Fin.castLEEmb hkh))) ⁻¹'
      sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ⊆ paperSparseSingularGood d n h := by
  intro X hX I _ hI
  let e := Fin.castLEEmb hkh
  constructor
  · apply (paperLeastSingularValue_ge_iff _ _).mpr
    intro v hv
    have hsq := (sparseGood_dimension_lower hd hX I hI v).1
    rw [hv,one_pow,mul_one] at hsq
    have hn := supportOperator_coordinate_norm_le e I (fun i => (X i).2) v
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact singular_numeric_lower d (norm_nonneg _) (hsq.trans hsquare)
  · apply (paperLeastSingularValue_ge_iff _ _).mpr
    intro v hv
    have hsq := (sparseGood_dimension_lower hd hX I hI v).2
    rw [hv,one_pow,mul_one] at hsq
    have hn := supportOperator_coordinate_norm_le e I (fun i => (X i).1) v
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact singular_numeric_lower d (norm_nonneg _) (hsq.trans hsquare)

/-- Paper Lemma7.4 at the literal half dimension, kappa=1/8192 and c_s=1/2048.
All support matrices are actual Gaussian submatrices with the exact column set. -/
theorem paper_sparse_singular_failure_le (A : ℝ) (hA : 0 < A) (d n : ℕ)
    (hd : GaussianEllipsoid.sparseEntropyCutoff A ≤ d)
    (hn : (n:ℝ) ≤ A*(d:ℝ)^2) :
    MeasurableSet (paperSparseSingularGood d n (d/2)) ∧
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      (paperSparseSingularGood d n (d/2))ᶜ ≤ Real.exp (-(d:ℝ)/2048) := by
  refine ⟨(paperSparseSingularGood_isClosed d n (d/2)).measurableSet,?_⟩
  have hdlarge : 8192 ≤ d := (le_max_left _ _).trans hd
  let e : Fin (2*(d/4)) ↪ Fin (d/2) := Fin.castLEEmb (by omega)
  let U := ContinuousLinearMap.adjoint (coordinateEmbedding e)
  have hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _ := by
    simpa only [U,ContinuousLinearMap.adjoint_adjoint] using coordinateEmbedding_adjoint_comp e
  have hp := compressCanonicalRows_preserving (n:=n) U hU
  have hsub : (paperSparseSingularGood d n (d/2))ᶜ ⊆
      compressCanonicalRows U ⁻¹' (sparseRowsGood (2*(d/4)) n (sparseSupportSize d))ᶜ := by
    intro X hBad hGood
    apply hBad
    exact sparseRowsGood_compress_subset_paperSparseGood (by omega) (by omega) hGood
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  rw [hp.measureReal_preimage (sparseRowsGood_measurable _ _ _).compl.nullMeasurableSet,
    sparseRowsGood_failure_eq]
  exact (sparse_good_event A hA d n hd hn).2.1
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_sparse_singular_failure_le
