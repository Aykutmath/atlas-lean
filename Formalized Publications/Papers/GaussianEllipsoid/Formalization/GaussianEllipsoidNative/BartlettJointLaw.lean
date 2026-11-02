import OrthogonalGaussianProjection
import GramSchmidtMeasurable
import GeneralPosition

open InnerProductSpace

noncomputable section
open MeasureTheory ProbabilityTheory Module Finset

namespace GaussianMixedNormHelpers

/-- Sequentially produced values are exactly Mathlib's actual GS squared norms. -/
theorem sequentialMap_gramSchmidtStep {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (n : ℕ) :
    sequentialMap (gramSchmidtStep (E := E)) n =
      (fun f : Fin n → E => fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  induction n with
  | zero => funext f i; exact Fin.elim0 i
  | succ n ih =>
    funext f i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [sequentialMap, Fin.snoc_last, gramSchmidtStep, Fin.snoc_init_self]
    · simp only [sequentialMap, Fin.snoc_castSucc, ih]
      have h := gramSchmidt_snoc_castSucc (Fin.init f) (f (Fin.last n)) j
      rw [Fin.snoc_init_self] at h
      rw [h]

/-- Actual Gaussian row law is absolutely continuous relative to Lebesgue measure. -/
theorem euclideanGaussianLaw_absolutelyContinuous (ι : Type*) [Fintype ι] :
    euclideanGaussianLaw ι ≪ (volume : Measure (EuclideanSpace ℝ ι)) := by
  rw [euclideanGaussianLaw_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- An iid Gaussian row matrix has full row rank almost surely up to ambient dimension. -/
theorem euclideanGaussianRows_ae_linearIndependent (r m : ℕ) (hrm : r ≤ m) :
    ∀ᵐ f ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin m)),
      LinearIndependent ℝ f := by
  apply ae_linearIndependent_pi_of_absolutelyContinuous
    (euclideanGaussianLaw (Fin m)) volume (euclideanGaussianLaw_absolutelyContinuous _) r
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hrm

/-- The one-row Bartlett law on each independent prefix, with exact dimension
`m-k` and no distribution or independence hypothesis. -/
theorem gramSchmidtStep_gaussian_law {m k : ℕ} (hkm : k < m)
    (f : Fin k → EuclideanSpace ℝ (Fin m)) (hf : LinearIndependent ℝ f) :
    Measure.map (gramSchmidtStep k f) (euclideanGaussianLaw (Fin m)) =
      gammaMeasure (((m - k : ℕ) : ℝ) / 2) (1 / 2) := by
  let W := (Submodule.span ℝ (Set.range f))ᗮ
  have hdim : finrank ℝ W = m - k := by
    have h := (Submodule.span ℝ (Set.range f)).finrank_add_finrank_orthogonal
    rw [finrank_span_eq_card hf, finrank_euclideanSpace, Fintype.card_fin,
      Fintype.card_fin] at h
    dsimp [W]
    omega
  have hW : 0 < finrank ℝ W := by rw [hdim]; omega
  have heq : gramSchmidtStep k f = (fun x => ‖W.orthogonalProjection x‖ ^ 2) := by
    funext x
    exact gramSchmidtStep_eq_projection k f x
  rw [heq, euclideanGaussianLaw_map_projection_norm_sq W hW, hdim]

/-- Bartlett's full joint law for iid standard Gaussian rows. All independence
of the residual lengths is proved by sequential Fubini, not assumed. -/
theorem gaussianRows_map_gramSchmidt_norm_sq (r m : ℕ) (hrm : r ≤ m) :
    Measure.map (fun f : Fin r → EuclideanSpace ℝ (Fin m) =>
      fun j => ‖gramSchmidt ℝ f j‖ ^ 2)
      (Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin m))) =
        Measure.pi (fun j : Fin r => gammaMeasure (((m - j.val : ℕ) : ℝ) / 2) (1 / 2)) := by
  let ν : ℕ → Measure ℝ := fun k => gammaMeasure (((m - k : ℕ) : ℝ) / 2) (1 / 2)
  letI (k : ℕ) : SigmaFinite (ν k) := by
    dsimp [ν]
    unfold gammaMeasure gammaPDF
    infer_instance
  have h := measurePreserving_sequentialMap_of_lt (euclideanGaussianLaw (Fin m)) ν
    (gramSchmidtStep (E := EuclideanSpace ℝ (Fin m))) r
    (fun k _ => measurable_gramSchmidtStep k)
    (fun k hk => ?_)
  · rw [sequentialMap_gramSchmidtStep] at h
    exact h.map_eq
  · filter_upwards [euclideanGaussianRows_ae_linearIndependent k m (by omega)] with f hf
    exact gramSchmidtStep_gaussian_law (by omega) f hf

/-- Actual Gram determinant distribution: the product of independent chi-squares
with degrees of freedom `m,m-1,...,m-r+1`. -/
theorem gaussianRows_map_gramDet (r m : ℕ) (hrm : r ≤ m) :
    Measure.map (fun f : Fin r → EuclideanSpace ℝ (Fin m) => (realGramMatrix f).det)
      (Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin m))) =
      Measure.map (fun x : Fin r → ℝ => ∏ j, x j)
        (Measure.pi (fun j : Fin r => gammaMeasure (((m - j.val : ℕ) : ℝ) / 2) (1 / 2))) := by
  have heq : (fun f : Fin r → EuclideanSpace ℝ (Fin m) => (realGramMatrix f).det) =
      (fun x : Fin r → ℝ => ∏ j, x j) ∘
        (fun f : Fin r → EuclideanSpace ℝ (Fin m) => fun j => ‖gramSchmidt ℝ f j‖ ^ 2) := by
    funext f
    exact det_realGramMatrix_eq_prod_gramSchmidt_norm_sq f
  rw [heq, ← Measure.map_map (by fun_prop) measurable_gramSchmidt_norm_sq,
    gaussianRows_map_gramSchmidt_norm_sq r m hrm]

end GaussianMixedNormHelpers
