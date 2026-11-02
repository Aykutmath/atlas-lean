import ProjectedGaussianLaw

/-!
Exact joint law of two disjoint sample extractions from the concrete two-factor
Gaussian product measure. No independence or conditional-law hypothesis is used.
Source: paper.tex, Lemma record-lemma-5-1, first paragraph of its proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.ProjectedClusters

/-- Restrict the sample index while retaining every scalar coordinate. -/
def selectEntries {n p h : ℕ} (e : Fin p ↪ Fin n) (x : GaussianEntries n h) :
    GaussianEntries p h := fun ia => x (e ia.1, ia.2)

/-- Select the same sample indices from the left and right Gaussian factors. -/
def selectSample {n p h : ℕ} (e : Fin p ↪ Fin n)
    (z : GaussianEntries n h × GaussianEntries n h) :
    GaussianEntries p h × GaussianEntries p h :=
  (selectEntries e z.1, selectEntries e z.2)

/-- Extract the head and current samples from one actual Gaussian input. -/
def disjointSamples {n p q h : ℕ} (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n)
    (z : GaussianEntries n h × GaussianEntries n h) :
    (GaussianEntries p h × GaussianEntries p h) ×
      (GaussianEntries q h × GaussianEntries q h) :=
  (selectSample eH z, selectSample eJ z)

theorem measurable_selectEntries {n p h : ℕ} (e : Fin p ↪ Fin n) :
    Measurable (selectEntries (h := h) e) :=
  measurable_pi_iff.mpr (fun ia => measurable_pi_apply (e ia.1, ia.2))

theorem measurable_selectSample {n p h : ℕ} (e : Fin p ↪ Fin n) :
    Measurable (selectSample (h := h) e) :=
  ((measurable_selectEntries e).comp measurable_fst).prodMk
    ((measurable_selectEntries e).comp measurable_snd)

theorem measurable_disjointSamples {n p q h : ℕ}
    (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n) :
    Measurable (disjointSamples (h := h) eH eJ) :=
  (measurable_selectSample eH).prodMk (measurable_selectSample eJ)

theorem selectEntries_preserving {n p h : ℕ} (e : Fin p ↪ Fin n) :
    MeasurePreserving (selectEntries (h := h) e)
      (gaussianProductLaw (Fin n × Fin h)) (gaussianProductLaw (Fin p × Fin h)) := by
  refine ⟨measurable_selectEntries e, ?_⟩
  apply gaussianProductLaw_map_subfamily
  intro a b hab
  exact Prod.ext (e.injective (congrArg Prod.fst hab)) (congrArg (fun z : Fin n × Fin h => z.2) hab)

theorem selectSample_preserving {n p h : ℕ} (e : Fin p ↪ Fin n) :
    MeasurePreserving (selectSample (h := h) e)
      (tensorGaussianLaw n h) (tensorGaussianLaw p h) :=
  (selectEntries_preserving e).prod (selectEntries_preserving e)

private abbrev TensorIndex (n h : ℕ) := (Fin n × Fin h) ⊕ (Fin n × Fin h)

private def selectTensorIndex {n p h : ℕ} (e : Fin p ↪ Fin n) :
    TensorIndex p h → TensorIndex n h :=
  Sum.map (fun ia => (e ia.1, ia.2)) (fun ia => (e ia.1, ia.2))

private theorem selectTensorIndex_injective {n p h : ℕ} (e : Fin p ↪ Fin n) :
    Function.Injective (selectTensorIndex (h := h) e) := by
  apply Function.Injective.sumMap <;> intro a b hab <;>
    exact Prod.ext (e.injective (congrArg Prod.fst hab)) (congrArg (fun z : Fin n × Fin h => z.2) hab)

private theorem selectTensorIndex_disjoint {n p q h : ℕ}
    (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n)
    (hd : ∀ i j, eH i ≠ eJ j) :
    ∀ a b, selectTensorIndex (h := h) eH a ≠ selectTensorIndex eJ b := by
  intro a b
  cases a with
  | inl a =>
      cases b with
      | inl b => exact fun hab => hd a.1 b.1 (congrArg Prod.fst (Sum.inl.inj hab))
      | inr b => exact Sum.inl_ne_inr
  | inr a =>
      cases b with
      | inl b => exact Sum.inr_ne_inl
      | inr b => exact fun hab => hd a.1 b.1 (congrArg Prod.fst (Sum.inr.inj hab))

/-- Exact product law for the head and current samples, derived from the actual
scalar iid Gaussian measure and literal disjointness of the sample embeddings. -/
theorem disjointSamples_preserving {n p q h : ℕ}
    (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n)
    (hd : ∀ i j, eH i ≠ eJ j) :
    MeasurePreserving (disjointSamples (h := h) eH eJ) (tensorGaussianLaw n h)
      ((tensorGaussianLaw p h).prod (tensorGaussianLaw q h)) := by
  let f : TensorIndex p h ⊕ TensorIndex q h → TensorIndex n h :=
    Sum.elim (selectTensorIndex eH) (selectTensorIndex eJ)
  have hf : Function.Injective f :=
    (selectTensorIndex_injective eH).sumElim (selectTensorIndex_injective eJ)
      (selectTensorIndex_disjoint eH eJ hd)
  have henc := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : TensorIndex n h => gaussianReal 0 1)
  have hsel : MeasurePreserving
      (fun x : TensorIndex n h → ℝ => fun i => x (f i))
      (gaussianProductLaw (TensorIndex n h))
      (gaussianProductLaw (TensorIndex p h ⊕ TensorIndex q h)) :=
    ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i)),
      gaussianProductLaw_map_subfamily f hf⟩
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : TensorIndex p h ⊕ TensorIndex q h => gaussianReal 0 1)
  have hdecH := measurePreserving_sumPiEquivProdPi
    (fun _ : TensorIndex p h => gaussianReal 0 1)
  have hdecJ := measurePreserving_sumPiEquivProdPi
    (fun _ : TensorIndex q h => gaussianReal 0 1)
  exact (hdecH.prod hdecJ).comp (hsplit.comp (hsel.comp henc))

/-- Map-equality form, convenient for transporting head-dependent events. -/
theorem tensorGaussianLaw_map_disjointSamples {n p q h : ℕ}
    (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n)
    (hd : ∀ i j, eH i ≠ eJ j) :
    (tensorGaussianLaw n h).map (disjointSamples eH eJ) =
      (tensorGaussianLaw p h).prod (tensorGaussianLaw q h) :=
  (disjointSamples_preserving eH eJ hd).map_eq

/-- Independence is a conclusion of the exact joint law, not an assumption. -/
theorem selectSample_indepFun {n p q h : ℕ}
    (eH : Fin p ↪ Fin n) (eJ : Fin q ↪ Fin n)
    (hd : ∀ i j, eH i ≠ eJ j) :
    IndepFun (selectSample (h := h) eH) (selectSample eJ) (tensorGaussianLaw n h) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_selectSample eH).aemeasurable
    (measurable_selectSample eJ).aemeasurable).mpr
  rw [(selectSample_preserving eH).map_eq, (selectSample_preserving eJ).map_eq]
  exact tensorGaussianLaw_map_disjointSamples eH eJ hd

/-- An injective selection preserves any sum whose summands vanish outside
its image. This includes coefficient mass and squared Euclidean norm. -/
theorem sum_select_of_zero_outside {M : Type*} [AddCommMonoid M] {n p : ℕ}
    (e : Fin p ↪ Fin n) (f : Fin n → M) (hf : ∀ i ∉ Set.range e, f i = 0) :
    ∑ i : Fin p, f (e i) = ∑ i : Fin n, f i :=
  Fintype.sum_of_injective e e.injective _ _ hf (fun _ => rfl)

theorem sum_abs_euclideanCoordinateSubfamily {n p : ℕ} (e : Fin p ↪ Fin n)
    (u : Euclid n) (hu : ∀ i ∉ Set.range e, u i = 0) :
    ∑ i, |euclideanCoordinateSubfamily e u i| = ∑ i, |u i| := by
  exact sum_select_of_zero_outside e (fun i => |u i|)
    (fun i hi => by simp [hu i hi])

theorem sum_sq_euclideanCoordinateSubfamily {n p : ℕ} (e : Fin p ↪ Fin n)
    (u : Euclid n) (hu : ∀ i ∉ Set.range e, u i = 0) :
    ∑ i, (euclideanCoordinateSubfamily e u i)^2 = ∑ i, (u i)^2 := by
  exact sum_select_of_zero_outside e (fun i => (u i)^2)
    (fun i hi => by simp [hu i hi])

/-- Reindex the actual bilinear matrix onto any embedding containing the
coefficient support; all discarded summands vanish literally. -/
theorem gaussianBilinearOperator_selectSample {n p h : ℕ} (d : ℕ)
    (e : Fin p ↪ Fin n) (z : GaussianEntries n h × GaussianEntries n h)
    (u : Euclid n) (hu : ∀ i ∉ Set.range e, u i = 0) :
    gaussianBilinearOperator p h d (selectSample e z) (euclideanCoordinateSubfamily e u) =
      gaussianBilinearOperator n h d z u := by
  ext b a
  change frobeniusToMatrix
    (gaussianBilinearOperator p h d (selectSample e z) (euclideanCoordinateSubfamily e u)) a b =
      frobeniusToMatrix (gaussianBilinearOperator n h d z u) a b
  rw [gaussianBilinearOperator_apply, gaussianBilinearOperator_apply]
  congr 1
  apply Fintype.sum_of_injective e e.injective
  · intro i hi
    rw [hu i hi, zero_mul]
  · intro i
    rfl

@[simp] theorem entriesToRows_selectEntries {n p h : ℕ} (e : Fin p ↪ Fin n)
    (x : GaussianEntries n h) (i : Fin p) :
    entriesToRows p h (selectEntries e x) i = entriesToRows n h x (e i) := rfl

@[simp] theorem selectEntries_transformEntries {n p h k : ℕ} (e : Fin p ↪ Fin n)
    (U : Euclid h →L[ℝ] Euclid k) (x : GaussianEntries n h) :
    selectEntries e (transformEntries n U x) =
      transformEntries p U (selectEntries e x) := rfl

@[simp] theorem selectSample_transformSample {n p h k : ℕ} (e : Fin p ↪ Fin n)
    (U V : Euclid h →L[ℝ] Euclid k) (z : GaussianEntries n h × GaussianEntries n h) :
    selectSample e (transformSample n U V z) =
      transformSample p U V (selectSample e z) := rfl

end GaussianEllipsoid.ProjectedClusters
