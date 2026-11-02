import RegularizedExpectation
import Mathlib.Logic.Equiv.Fintype

noncomputable section
open MeasureTheory Matrix Finset Set

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reindexing both weights and sample vectors does not alter a covariance. -/
theorem weightedGram_reindex (g : κ → ι → ℝ) (w : κ → ℝ) (e : Equiv.Perm κ) :
    weightedGram (g ∘ e) (w ∘ e) = weightedGram g w := by
  exact Equiv.sum_comp e (fun k => w k • Matrix.vecMulVec (g k) (g k))

theorem regularizedGram_reindex (ε : ℝ) (g : κ → ι → ℝ) (w : κ → ℝ) (e : Equiv.Perm κ) :
    regularizedGram ε (g ∘ e) (w ∘ e) = regularizedGram ε g w := by
  simp only [regularizedGram, weightedGram_reindex]

/-- An iid product measure makes the actual regularized moment permutation invariant. -/
theorem regularizedMoment_perm (μ : Measure (ι → ℝ)) [SigmaFinite μ]
    (ε : ℝ) (s : ℕ) (w : κ → ℝ) (e : Equiv.Perm κ) :
    regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s (w ∘ e) =
      regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s w := by
  let T := MeasurableEquiv.piCongrLeft (fun _ : κ => ι → ℝ) e.symm
  have hT := measurePreserving_piCongrLeft (fun _ : κ => μ) e.symm
  have h := hT.integral_comp T.measurableEmbedding
    (fun g => (regularizedGram ε g (w ∘ e)).det ^ (-(s : ℤ)))
  have hfun : (fun g : κ → ι → ℝ =>
      (regularizedGram ε (T g) (w ∘ e)).det ^ (-(s : ℤ))) =
      (fun g => (regularizedGram ε g w).det ^ (-(s : ℤ))) := by
    funext g
    have hg : T g = g ∘ e := by
      funext k
      simpa [T] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ι → ℝ) e.symm g (e k)
    rw [hg, regularizedGram_reindex]
  change (∫ g, (regularizedGram ε g (w ∘ e)).det ^ (-(s : ℤ))
    ∂Measure.pi (fun _ : κ => μ)) = _
  rw [← h]
  rw [hfun]
  rfl

/-- Equal-cardinality finite subsets are related by a permutation of the whole
index set. The complement is matched too, so this also preserves the iid law. -/
theorem exists_perm_mem_iff (S T : Finset κ) (hcard : S.card = T.card) :
    ∃ e : Equiv.Perm κ, ∀ k, e k ∈ T ↔ k ∈ S := by
  classical
  let eS : (S : Set κ) ≃ (T : Set κ) := Fintype.equivOfCardEq (by simpa using hcard)
  have hcomp : Fintype.card ↥((S : Set κ)ᶜ) = Fintype.card ↥((T : Set κ)ᶜ) := by
    simp only [Fintype.card_compl_set]
    simpa using congrArg (fun k : ℕ => Fintype.card κ - k) hcard
  let eC : ↥((S : Set κ)ᶜ) ≃ ↥((T : Set κ)ᶜ) := Fintype.equivOfCardEq hcomp
  let e : Equiv.Perm κ := (Equiv.Set.sumCompl (S : Set κ)).symm |>.trans
    (Equiv.sumCongr eS eC) |>.trans (Equiv.Set.sumCompl (T : Set κ))
  refine ⟨e, ?_⟩
  intro k
  by_cases hk : k ∈ S
  · have he : e k ∈ T := by
      change ((Equiv.Set.sumCompl (T : Set κ))
        ((Equiv.sumCongr eS eC) ((Equiv.Set.sumCompl (S : Set κ)).symm k))) ∈ T
      rw [Equiv.Set.sumCompl_symm_apply_of_mem (s := (S : Set κ)) hk]
      change (eS ⟨k, hk⟩ : κ) ∈ T
      exact (eS ⟨k, hk⟩).property
    exact iff_of_true he hk
  · have he : e k ∉ T := by
      change ((Equiv.Set.sumCompl (T : Set κ))
        ((Equiv.sumCongr eS eC) ((Equiv.Set.sumCompl (S : Set κ)).symm k))) ∉ T
      rw [Equiv.Set.sumCompl_symm_apply_of_notMem (s := (S : Set κ)) hk]
      change (eC ⟨k, hk⟩ : κ) ∉ T
      exact (eC ⟨k, hk⟩).property
    exact iff_of_false he hk

/-- Every uniform subset of the same size has the same iid determinant moment. -/
theorem regularizedMoment_uniform_eq (μ : Measure (ι → ℝ)) [SigmaFinite μ]
    (ε : ℝ) (s : ℕ) (a : ℝ) (S T : Finset κ) (hcard : S.card = T.card) :
    regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s (fun i => if i ∈ S then a else 0) =
      regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s (fun i => if i ∈ T then a else 0) := by
  obtain ⟨e, he⟩ := exists_perm_mem_iff S T hcard
  have hw : (fun i => if i ∈ S then a else 0) = (fun i => if i ∈ T then a else 0) ∘ e := by
    funext k
    simp only [Function.comp_apply, he k]
  rw [hw]
  exact regularizedMoment_perm μ ε s _ e

/-- The full regularized capped determinant extremizer for iid vectors:
comparison to any fixed uniform subset, with all convexity, permutation,
and Bochner integrability obligations proved rather than postulated. -/
theorem regularizedMoment_le_fixed_uniform_subset
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (s m : ℕ) (hm : 0 < m)
    {w : κ → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1)
    (T : Finset κ) (hT : T.card = m) :
    regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s w ≤
      regularizedMoment (Measure.pi (fun _ : κ => μ)) ε s
        (fun i => if i ∈ T then (m : ℝ)⁻¹ else 0) := by
  obtain ⟨S, hS, hle⟩ := regularizedMoment_le_uniform_subset
    (Measure.pi (fun _ : κ => μ)) hε s m hm hw
  rw [regularizedMoment_uniform_eq μ ε s _ S T (hS.trans hT.symm)] at hle
  exact hle

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.regularizedMoment_le_fixed_uniform_subset
