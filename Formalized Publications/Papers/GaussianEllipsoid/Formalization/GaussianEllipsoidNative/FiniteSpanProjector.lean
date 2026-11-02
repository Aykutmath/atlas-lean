import GramSchmidtMeasurable
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open InnerProductSpace

noncomputable section
set_option maxHeartbeats 400000
open MeasureTheory Module
open scoped BigOperators
namespace GaussianEllipsoid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual ambient orthogonal projector onto the span of a finite vector
family, including all rank-deficient families. -/
def finiteSpanProjector {n : ℕ} (f : Fin n → E) : E →L[ℝ] E :=
  (Submodule.span ℝ (Set.range f)).subtypeL ∘L
    (Submodule.span ℝ (Set.range f)).orthogonalProjection

/-- Exact Gram-Schmidt residual formula. No full-rank assumption is used. -/
theorem finiteSpanProjector_apply {n : ℕ} (f : Fin n → E) (x : E) :
    finiteSpanProjector f x = x - gramSchmidt ℝ (Fin.snoc f x) (Fin.last n) := by
  borelize E
  have h := GaussianMixedNormHelpers.gramSchmidt_eq_sub_priorProjection
    (Fin.snoc f x) (Fin.last n)
  rw [GaussianMixedNormHelpers.priorSpan_snoc_last, Fin.snoc_last] at h
  change ((Submodule.span ℝ (Set.range f)).orthogonalProjection x : E) =
    x - gramSchmidt ℝ (Fin.snoc f x) (Fin.last n)
  rw [h]
  abel

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Joint Borel dependence of the finite-span projection and the vector being
projected. Rank drops cause no exceptional set. -/
theorem measurable_finiteSpanProjector_apply (n : ℕ) :
    Measurable (fun p : (Fin n → E) × E => finiteSpanProjector p.1 p.2) := by
  have hgs : Measurable (fun p : (Fin n → E) × E =>
      gramSchmidt ℝ (Fin.snoc p.1 p.2) (Fin.last n)) := by
    apply (GaussianMixedNormHelpers.measurable_gramSchmidt (Fin.last n)).comp
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using measurable_snd
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  have heq : (fun p : (Fin n → E) × E => finiteSpanProjector p.1 p.2) =
      (fun p => p.2 - gramSchmidt ℝ (Fin.snoc p.1 p.2) (Fin.last n)) := by
    funext p
    exact finiteSpanProjector_apply _ _
  rw [heq]
  exact measurable_snd.sub hgs

/-- The full operator-valued finite-span projector is Borel measurable. This
uses finite coordinate reconstruction, rather than a measurable eigenbasis. -/
theorem measurable_finiteSpanProjector (n : ℕ) :
    Measurable (finiteSpanProjector : (Fin n → E) → (E →L[ℝ] E)) := by
  let b := stdOrthonormalBasis ℝ E
  let L : (Fin (finrank ℝ E) → E) ≃L[ℝ] (E →L[ℝ] E) :=
    ((b.toBasis.constr ℝ).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hm : Measurable (fun f : Fin n → E =>
      fun i : Fin (finrank ℝ E) => finiteSpanProjector f (b i)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hp : Measurable (fun f : Fin n → E => (f, b i)) :=
      measurable_id.prodMk measurable_const
    have hh := (measurable_finiteSpanProjector_apply (E := E) n).comp hp
    simpa only [Function.comp_def] using hh
  have heq : (finiteSpanProjector : (Fin n → E) → (E →L[ℝ] E)) =
      (fun f => L (fun i => finiteSpanProjector f (b i))) := by
    funext f
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    exact (b.toBasis.constr_basis ℝ (fun i => finiteSpanProjector f (b i)) i).symm
  rw [heq]
  exact L.continuous.measurable.comp hm

/-- A prefix projector formed from masked columns. Its range is identified
below with the actual strict-prefix span. -/
def prefixSpanProjector {n : ℕ} (f : Fin n → E) (K : ℕ) : E →L[ℝ] E :=
  finiteSpanProjector (fun i => if i.val < K then f i else 0)

theorem span_masked_eq_prefix {n : ℕ} (f : Fin n → E) (K : ℕ) :
    Submodule.span ℝ (Set.range (fun i : Fin n => if i.val < K then f i else 0)) =
      Submodule.span ℝ (f '' {i : Fin n | i.val < K}) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i.val < K then f i else 0) ∈ Submodule.span ℝ (f '' {i : Fin n | i.val < K})
    split_ifs with hi
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    exact ⟨i, by simpa only [show i.val < K from hi, if_true]⟩

theorem prefixSpanProjector_eq {n : ℕ} (f : Fin n → E) (K : ℕ) :
    prefixSpanProjector f K =
      (Submodule.span ℝ (f '' {i : Fin n | i.val < K})).subtypeL ∘L
        (Submodule.span ℝ (f '' {i : Fin n | i.val < K})).orthogonalProjection := by
  exact congrArg (fun S : Submodule ℝ E => S.subtypeL ∘L S.orthogonalProjection)
    (span_masked_eq_prefix f K)

theorem measurable_prefixSpanProjector (n K : ℕ) :
    Measurable (fun f : Fin n → E => prefixSpanProjector f K) := by
  apply (measurable_finiteSpanProjector n).comp
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val < K
  · simpa only [hi, if_true] using measurable_pi_apply i
  · simp only [hi, if_false]
    exact measurable_const

/-- Prefix increments are Borel even when the input rank changes. -/
theorem measurable_prefixSpanProjector_increment (n K L : ℕ) :
    Measurable (fun f : Fin n → E => prefixSpanProjector f L - prefixSpanProjector f K) :=
  (measurable_prefixSpanProjector n L).sub (measurable_prefixSpanProjector n K)


/-- Prefix projectors are genuinely self-adjoint. -/
theorem prefixSpanProjector_selfAdjoint {n : ℕ} (f : Fin n → E) (K : ℕ) :
    ContinuousLinearMap.adjoint (prefixSpanProjector f K) = prefixSpanProjector f K :=
  (isSelfAdjoint_starProjection
    (Submodule.span ℝ (Set.range (fun i : Fin n => if i.val < K then f i else 0)))).adjoint_eq

theorem prefix_span_mono {n K L : ℕ} (f : Fin n → E) (hKL : K ≤ L) :
    Submodule.span ℝ (f '' {i : Fin n | i.val < K}) ≤
      Submodule.span ℝ (f '' {i : Fin n | i.val < L}) := by
  apply Submodule.span_mono
  exact Set.image_mono (fun i hi => (show i.val < K from hi).trans_le hKL)

/-- Projecting a larger prefix and then a smaller one yields the smaller one. -/
theorem prefixSpanProjector_comp_of_le {n K L : ℕ} (f : Fin n → E) (hKL : K ≤ L) :
    prefixSpanProjector f K ∘L prefixSpanProjector f L = prefixSpanProjector f K := by
  rw [prefixSpanProjector_eq f K, prefixSpanProjector_eq f L]
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_starProjection_of_le
    (prefix_span_mono f hKL) x)

/-- Prefix projectors commute, with product equal to the smaller projector. -/
theorem prefixSpanProjector_comp_of_ge {n K L : ℕ} (f : Fin n → E) (hKL : K ≤ L) :
    prefixSpanProjector f L ∘L prefixSpanProjector f K = prefixSpanProjector f K := by
  have h := congrArg ContinuousLinearMap.adjoint (prefixSpanProjector_comp_of_le f hKL)
  simpa only [ContinuousLinearMap.adjoint_comp, prefixSpanProjector_selfAdjoint] using h

/-- Every fixed prefix increment is an orthogonal projector, even at rank drops. -/
theorem prefixSpanProjector_increment_idempotent {n K L : ℕ} (f : Fin n → E) (hKL : K ≤ L) :
    (prefixSpanProjector f L - prefixSpanProjector f K) ∘L
      (prefixSpanProjector f L - prefixSpanProjector f K) =
        prefixSpanProjector f L - prefixSpanProjector f K := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp,
    prefixSpanProjector_comp_of_le f (le_refl L), prefixSpanProjector_comp_of_le f hKL,
    prefixSpanProjector_comp_of_ge f hKL, prefixSpanProjector_comp_of_le f (le_refl K)]
  abel

theorem prefixSpanProjector_increment_selfAdjoint {n : ℕ} (f : Fin n → E) (K L : ℕ) :
    ContinuousLinearMap.adjoint (prefixSpanProjector f L - prefixSpanProjector f K) =
      prefixSpanProjector f L - prefixSpanProjector f K := by
  simp only [map_sub, prefixSpanProjector_selfAdjoint]

/-- Disjoint ordered prefix increments have orthogonal ranges. -/
theorem prefixSpanProjector_increments_comp_zero {n K L M N : ℕ} (f : Fin n → E)
    (hKL : K ≤ L) (hLM : L ≤ M) (hMN : M ≤ N) :
    (prefixSpanProjector f L - prefixSpanProjector f K) ∘L
      (prefixSpanProjector f N - prefixSpanProjector f M) = 0 := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.sub_comp,
    prefixSpanProjector_comp_of_le f (hLM.trans hMN),
    prefixSpanProjector_comp_of_le f (hKL.trans (hLM.trans hMN)),
    prefixSpanProjector_comp_of_le f hLM,
    prefixSpanProjector_comp_of_le f (hKL.trans hLM)]
  abel

end GaussianEllipsoid
#print axioms GaussianEllipsoid.finiteSpanProjector_apply
#print axioms GaussianEllipsoid.measurable_finiteSpanProjector
#print axioms GaussianEllipsoid.measurable_prefixSpanProjector
#print axioms GaussianEllipsoid.measurable_prefixSpanProjector_increment

#print axioms GaussianEllipsoid.prefixSpanProjector_increment_idempotent
#print axioms GaussianEllipsoid.prefixSpanProjector_increments_comp_zero
