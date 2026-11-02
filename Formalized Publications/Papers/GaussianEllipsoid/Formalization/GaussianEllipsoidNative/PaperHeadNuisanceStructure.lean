import UCHeadNuisance
import FiniteSpanProjector
import Mathlib.Data.Sym.Card

noncomputable section
open MeasureTheory Module
open scoped BigOperators
namespace UCEscape

/-- Unordered quadratic monomials retain precisely the same head span. -/
def symmetricHeadFeature {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    Option (Sym2 (Fin j)) → EuclideanSpace ℝ (Fin n)
  | none => headFeature h none
  | some s => Sym2.lift ⟨(fun a b : Fin j => headFeature h (some (a,b))), by
      intro a b
      ext i
      simp [headFeature, mul_comm]⟩ s

theorem headNuisanceSpace_eq_symmetric_span {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    headNuisanceSpace h = Submodule.span ℝ (Set.range (symmetricHeadFeature h)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    cases a with
    | none => exact Submodule.subset_span ⟨none,rfl⟩
    | some ab => exact Submodule.subset_span ⟨some (Sym2.mk ab.1 ab.2),rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    cases a with
    | none => exact Submodule.subset_span ⟨none,rfl⟩
    | some s =>
      exact Sym2.ind (fun a b => Submodule.subset_span ⟨some (a,b),rfl⟩) s

/-- Literal manuscript rank bound, using symmetry rather than j² ordered entries. -/
theorem headNuisanceSpace_finrank_symmetric {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    finrank ℝ (headNuisanceSpace h) ≤ 1+j*(j+1)/2 := by
  rw [headNuisanceSpace_eq_symmetric_span]
  change (Set.range (symmetricHeadFeature h)).finrank ℝ ≤ _
  apply (finrank_range_le_card (R := ℝ) (symmetricHeadFeature h)).trans_eq
  simp [Sym2.card, Nat.choose_two_right, Nat.mul_comm, Nat.add_comm]

/-- Exact fixed head-rank budget in the manuscript. -/
theorem headNuisanceSpace_finrank_le_of_le {j n K : ℕ}
    (h : GaussianEllipsoid.Sample j n) (hj : j≤K) :
    finrank ℝ (headNuisanceSpace h) ≤ 1+K*(K+1)/2 := by
  apply (headNuisanceSpace_finrank_symmetric h).trans
  exact Nat.add_le_add_left
    (Nat.div_le_div_right (Nat.mul_le_mul hj (Nat.add_le_add_right hj 1))) 1

theorem measurable_headFeature (j n : ℕ) :
    Measurable (fun h : GaussianEllipsoid.Sample j n => headFeature h) := by
  apply measurable_pi_iff.mpr
  intro a
  cases a with
  | none => exact measurable_const
  | some ab =>
    change Measurable (fun h : GaussianEllipsoid.Sample j n =>
      WithLp.toLp 2 (fun i => h i ab.1 * h i ab.2))
    apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
    fun_prop

/-- Actual ambient orthogonal projector onto the head-generated nuisance space. -/
def headNuisanceProjector {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (headNuisanceSpace h).subtypeL ∘L (headNuisanceSpace h).orthogonalProjection

/-- Borel dependence of the complete nuisance projector, including every rank drop.
The generator list is finite; no eigenbasis or measurable basis choice is assumed. -/
theorem measurable_headNuisanceProjector (j n : ℕ) :
    Measurable (headNuisanceProjector : GaussianEllipsoid.Sample j n → _) := by
  classical
  let I := Option (Fin j × Fin j)
  let e := Fintype.equivFin I
  let F : GaussianEllipsoid.Sample j n → Fin (Fintype.card I) → EuclideanSpace ℝ (Fin n) :=
    fun h i => headFeature h (e.symm i)
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (e.symm i)).comp (measurable_headFeature j n)
  have hrange (h : GaussianEllipsoid.Sample j n) : Set.range (F h) = Set.range (headFeature h) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e.symm i,rfl⟩
    · rintro ⟨a,rfl⟩
      refine ⟨e a,?_⟩
      simp [F]
  have hp (h : GaussianEllipsoid.Sample j n) : headNuisanceProjector h =
      GaussianEllipsoid.finiteSpanProjector (F h) := by
    have hs : Submodule.span ℝ (Set.range (F h)) = headNuisanceSpace h :=
      congrArg (Submodule.span ℝ) (hrange h)
    exact congrArg (fun L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) =>
      L.subtypeL ∘L L.orthogonalProjection) hs.symm
  have heq : (headNuisanceProjector : GaussianEllipsoid.Sample j n → _) =
      (fun h => GaussianEllipsoid.finiteSpanProjector (F h)) := funext hp
  rw [heq]
  exact (GaussianEllipsoid.measurable_finiteSpanProjector (Fintype.card I)).comp hF

#print axioms headNuisanceSpace_finrank_symmetric
#print axioms measurable_headNuisanceProjector
end UCEscape
