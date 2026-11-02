import GaussianSparsePrefixEvent
import GaussianWeightedBilinearMGF
import GaussianSelectedColumns

noncomputable section
open MeasureTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.SparseSupport

/-- Actual matrix columns in Euclidean coordinates. -/
def sampleColumn {h n : ℕ} (x : (Fin h × Fin n) → ℝ) (i : Fin n) : Euclid h :=
  (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)) (fun j => x (j,i))

@[simp] theorem sampleColumn_apply {h n : ℕ} (x : (Fin h × Fin n) → ℝ)
    (i : Fin n) (j : Fin h) : sampleColumn x i j = x (j,i) := rfl

theorem sampleColumn_preserving (h n : ℕ) :
    MeasurePreserving (sampleColumn (h := h) (n := n))
      (gaussianProductLaw (Fin h × Fin n))
      (Measure.pi fun _ : Fin n => euclideanGaussianLaw (Fin h)) := by
  have ht : MeasurePreserving (fun x : (Fin h × Fin n) → ℝ => fun p : Fin n × Fin h => x p.swap)
      (gaussianProductLaw (Fin h × Fin n)) (gaussianProductLaw (Fin n × Fin h)) :=
    ⟨measurable_pi_iff.mpr (fun p => measurable_pi_apply p.swap),
      gaussianProductLaw_map_subfamily Prod.swap Prod.swap_injective⟩
  have hc : MeasurePreserving (fun x : (Fin n × Fin h) → ℝ => fun i a => x (i,a))
      (gaussianProductLaw (Fin n × Fin h))
      (Measure.pi fun _ : Fin n => gaussianProductLaw (Fin h)) :=
    ⟨measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun a => measurable_pi_apply (i,a))),
      gaussianProductLaw_map_curry⟩
  have he := measurePreserving_pi
    (fun _ : Fin n => gaussianProductLaw (Fin h))
    (fun _ : Fin n => euclideanGaussianLaw (Fin h))
    (f := fun _ => (MeasurableEquiv.toLp 2 ((Fin h) → ℝ)))
    (fun _ => ⟨(MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).measurable, rfl⟩)
  exact he.comp (hc.comp ht)

/-- Regroup and swap actual matrices (A,B) into the canonical sample pairs (b,a). -/
def matrixPairToRows (h n : ℕ)
    (p : ((Fin h × Fin n) → ℝ) × ((Fin h × Fin n) → ℝ)) : Fin n → Euclid h × Euclid h :=
  fun i => (sampleColumn p.2 i, sampleColumn p.1 i)

/-- Inverse regrouping of the canonical sample pairs (b,a) into actual matrices (A,B). -/
def rowsToMatrixPair (h n : ℕ) (X : Fin n → Euclid h × Euclid h) :
    ((Fin h × Fin n) → ℝ) × ((Fin h × Fin n) → ℝ) :=
  (fun p => (X p.2).2 p.1, fun p => (X p.2).1 p.1)

theorem matrixPairToRows_preserving (h n : ℕ) :
    MeasurePreserving (matrixPairToRows h n) (matrixPairLaw h n)
      (gaussianBilinearSampleLaw (Fin n) h h) := by
  have hp := (sampleColumn_preserving h n).prod (sampleColumn_preserving h n)
  have hswap : MeasurePreserving Prod.swap (matrixPairLaw h n) (matrixPairLaw h n) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have he := (measurePreserving_arrowProdEquivProdArrow (Euclid h) (Euclid h) (Fin n)
    (fun _ => euclideanGaussianLaw (Fin h)) (fun _ => euclideanGaussianLaw (Fin h))).symm
  exact he.comp (hp.comp hswap)

theorem rowsToMatrixPair_measurable (h n : ℕ) : Measurable (rowsToMatrixPair h n) := by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro p
    exact (measurable_pi_apply p.1).comp (((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm).measurable.comp
      (measurable_snd.comp (measurable_pi_apply p.2)))
  · apply measurable_pi_iff.mpr
    intro p
    exact (measurable_pi_apply p.1).comp (((MeasurableEquiv.toLp 2 ((Fin h) → ℝ)).symm).measurable.comp
      (measurable_fst.comp (measurable_pi_apply p.2)))

@[simp] theorem rowsToMatrixPair_matrixPairToRows (h n : ℕ) (p) :
    rowsToMatrixPair h n (matrixPairToRows h n p) = p := by
  cases p
  rfl

@[simp] theorem matrixPairToRows_rowsToMatrixPair (h n : ℕ) (X) :
    matrixPairToRows h n (rowsToMatrixPair h n X) = X := by
  funext i
  exact Prod.ext (by ext j; rfl) (by ext j; rfl)

/-- Both directions are exact transports of actual laws, including the factor
order. No Gaussian or independence premise is imposed on the caller. -/
theorem rowsToMatrixPair_preserving (h n : ℕ) :
    MeasurePreserving (rowsToMatrixPair h n) (gaussianBilinearSampleLaw (Fin n) h h)
      (matrixPairLaw h n) := by
  refine ⟨rowsToMatrixPair_measurable h n, ?_⟩
  rw [← (matrixPairToRows_preserving h n).map_eq,
    Measure.map_map (rowsToMatrixPair_measurable h n) (matrixPairToRows_preserving h n).measurable]
  have hh : rowsToMatrixPair h n ∘ matrixPairToRows h n = id := by
    funext p
    exact rowsToMatrixPair_matrixPairToRows h n p
  rw [hh, Measure.map_id]

/-- The sparse good event in the canonical (b,a) independent sample law. -/
def sparseRowsGood (h n m : ℕ) : Set (Fin n → Euclid h × Euclid h) :=
  rowsToMatrixPair h n ⁻¹' sparseGood h n m

theorem sparseRowsGood_measurable (h n m : ℕ) : MeasurableSet (sparseRowsGood h n m) :=
  (sparseGood_measurable h n m).preimage (rowsToMatrixPair_measurable h n)

theorem sparseRowsGood_failure_eq (h n m : ℕ) :
    (gaussianBilinearSampleLaw (Fin n) h h).real (sparseRowsGood h n m)ᶜ =
      (matrixPairLaw h n).real (sparseGood h n m)ᶜ := by
  unfold sparseRowsGood Measure.real
  rw [← Set.preimage_compl]
  rw [(rowsToMatrixPair_preserving h n).measure_preimage
    (sparseGood_measurable h n m).compl.nullMeasurableSet]

end GaussianEllipsoid.SparseSupport
