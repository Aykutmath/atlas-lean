/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending. -/
import GaussianLocalizedDecay
import GaussianLocalizedMeasurability
import GaussianCoordinateMarginal
import CoordinateBlockPinching

noncomputable section
open MeasureTheory Finset GaussianEllipsoid GaussianEllipsoid.SmallBall
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.Localized

def restrictLocalizedSample {n k h : ℕ} (e : Fin k ↪ Fin h)
    (p : BilinearSample h n) : BilinearSample k n :=
  (fun i a => p.1 i (e a), euclideanCoordinateSubfamily (fun a : Fin n × Fin k => (a.1,e a.2)) p.2)

theorem restrictLocalizedSample_preserving {n k h : ℕ} (e : Fin k ↪ Fin h) :
    MeasurePreserving (restrictLocalizedSample (n:=n) e)
      (bilinearGaussianSampleLaw h n) (bilinearGaussianSampleLaw k n) := by
  have hrow : MeasurePreserving (fun x : Fin h → ℝ => fun a : Fin k => x (e a))
      (gaussianProductLaw (Fin h)) (gaussianProductLaw (Fin k)) :=
    ⟨measurable_pi_lambda _ (fun a => measurable_pi_apply (e a)),
      gaussianProductLaw_map_subfamily e e.injective⟩
  have hleft := measurePreserving_pi _ _ (f := fun _ : Fin n => fun x : Fin h → ℝ =>
    fun a : Fin k => x (e a)) (fun _ => hrow)
  let f : Fin n × Fin k → Fin n × Fin h := fun a => (a.1,e a.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · exact congrArg (fun z : Fin n × Fin h => z.1) hab
    · exact e.injective (congrArg (fun z : Fin n × Fin h => z.2) hab)
  have hm : Measurable (euclideanCoordinateSubfamily f) := by
    change Measurable ((MeasurableEquiv.toLp 2 ((Fin n × Fin k) → ℝ)) ∘
      (fun x : (Fin n × Fin h) → ℝ => fun a => x (f a)) ∘
      (MeasurableEquiv.toLp 2 ((Fin n × Fin h) → ℝ)).symm)
    exact (MeasurableEquiv.toLp 2 ((Fin n × Fin k) → ℝ)).measurable.comp
      ((measurable_pi_lambda _ (fun a => measurable_pi_apply (f a))).comp
        (MeasurableEquiv.toLp 2 ((Fin n × Fin h) → ℝ)).symm.measurable)
  have hright : MeasurePreserving (euclideanCoordinateSubfamily f)
      (euclideanGaussianLaw (Fin n × Fin h)) (euclideanGaussianLaw (Fin n × Fin k)) :=
    ⟨hm, euclideanGaussianLaw_map_subfamily f hf⟩
  exact hleft.prod hright

def localizedCoordinateBlock {k h : ℕ} (e : Fin k ↪ Fin h)
    (A : FrobeniusMatrix h h) : FrobeniusMatrix k k :=
  operatorFrobenius ((coordinateEmbedding e).adjoint ∘L frobeniusOperator A ∘L coordinateEmbedding e)

@[simp] theorem localizedCoordinateBlock_apply {k h : ℕ} (e : Fin k ↪ Fin h)
    (A : FrobeniusMatrix h h) (j i : Fin k) : localizedCoordinateBlock e A j i = A (e j) (e i) := by
  simp only [localizedCoordinateBlock, operatorFrobenius_apply, ContinuousLinearMap.comp_apply,
    coordinateEmbedding_basis, coordinateEmbedding_adjoint_apply, frobeniusOperator_basis]

theorem localizedCoordinateBlock_nuclear_le {k h : ℕ} (e : Fin k ↪ Fin h)
    (A : FrobeniusMatrix h h) : spectralNuclearNorm (localizedCoordinateBlock e A) ≤ spectralNuclearNorm A := by
  have hh := spectralNuclear_compression_le (coordinateEmbedding e).adjoint (frobeniusOperator A)
    (coordinateEmbedding e) (by simpa using coordinateEmbedding_norm_le_one e)
    (coordinateEmbedding_norm_le_one e)
  simpa only [localizedCoordinateBlock, operatorFrobenius_frobeniusOperator] using hh

theorem localizedCoordinateBlock_norm_le {k h : ℕ} (e : Fin k ↪ Fin h)
    (A : FrobeniusMatrix h h) : ‖localizedCoordinateBlock e A‖ ≤ ‖A‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq, frobenius_norm_sq]
  simp only [frobeniusToMatrix, localizedCoordinateBlock_apply]
  have hrow (j : Fin h) : (∑ i : Fin k, (A j (e i))^2) ≤ ∑ i : Fin h, (A j i)^2 := by
    exact Finset.sum_le_sum_of_injOn e (fun _ _ _ _ hh => e.injective hh)
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ j : Fin k, ∑ i : Fin h, (A (e j) i)^2 := Finset.sum_le_sum (fun j _ => hrow (e j))
    _ ≤ ∑ j : Fin h, ∑ i : Fin h, (A j i)^2 :=
      Finset.sum_le_sum_of_injOn e (fun _ _ _ _ hh => e.injective hh)
        (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem localizedOperator_restrict {n k h : ℕ} (d : ℝ) (e : Fin k ↪ Fin h)
    (hk : 0 < k) (hh : 0 < h) (p : BilinearSample h n) (z : Coeff n) :
    localizedOperator d k n (restrictLocalizedSample e p) z =
      localizedCoordinateBlock e (localizedOperator d h n p z) := by
  apply (frobeniusEquivEuclidean k k).injective
  ext a
  rcases a with ⟨i,j⟩
  rw [frobeniusEquivEuclidean_apply, localizedOperator_entry d k n hk]
  change _ = localizedCoordinateBlock e (localizedOperator d h n p z) j i
  rw [localizedCoordinateBlock_apply]
  change _ = frobeniusToMatrix (localizedOperator d h n p z) (e i) (e j)
  rw [localizedOperator_entry d h n hh]
  rfl

theorem localized_event_probability_dimension_mono
    (d A β B K c L : ℝ) (n k h : ℕ) (hk : 0 < k) (hkh : k ≤ h) :
    (bilinearGaussianSampleLaw h n).real
      (homogeneousBad (localizedOperator d h n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d h n) L d) ≤
    (bilinearGaussianSampleLaw k n).real
      (homogeneousBad (localizedOperator d k n) A β B K c d ∩
        frobeniusContinuity (localizedOperator d k n) L d) := by
  let e := Fin.castLEEmb hkh
  have hh : 0 < h := hk.trans_le hkh
  let E := homogeneousBad (localizedOperator d k n) A β B K c d ∩
    frobeniusContinuity (localizedOperator d k n) L d
  have hsub : (homogeneousBad (localizedOperator d h n) A β B K c d ∩
      frobeniusContinuity (localizedOperator d h n) L d) ⊆ restrictLocalizedSample e ⁻¹' E := by
    rintro p ⟨⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,hbad⟩,hcont⟩
    refine ⟨⟨q,hq,I,hI,U,V,hU,hV,hhead,hlower,hupper,hcap,?_⟩,?_⟩
    · rw [localizedOperator_restrict d e hk hh]
      exact (localizedCoordinateBlock_nuclear_le e _).trans_lt hbad
    · intro z
      rw [localizedOperator_restrict d e hk hh]
      exact (localizedCoordinateBlock_norm_le e _).trans (hcont z)
  exact (measureReal_mono hsub).trans_eq
    ((restrictLocalizedSample_preserving (n:=n) e).measureReal_preimage
      (measurableSet_localized_event d k n A β B K c L).nullMeasurableSet)

end GaussianEllipsoid.Localized
