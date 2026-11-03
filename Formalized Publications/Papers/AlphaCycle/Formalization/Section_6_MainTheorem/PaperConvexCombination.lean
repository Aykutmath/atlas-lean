import Section_2_Preliminaries.PaperCoordinates

/-! The displayed convex-combination identities in the probabilistic representation proof. -/
namespace AlphaCycle
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite law's moment vector is its explicit convex combination of Boolean lifts. -/
theorem momentVector_eq_convexCombination (S : Finset (Finset V)) (μ : BooleanLaw V) :
    momentVector S μ = ∑ x, μ.mass x • monomialLift S x := by
  funext s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold momentVector moment Law.prob monomialLift
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : s.val ⊆ x <;> simp [h]

namespace PaperHypergraph

/-- The same convex combination in the paper's literal vertex-plus-edge coordinates. -/
theorem toPaper_momentVector_eq_convexCombination (H : PaperHypergraph V) (μ : BooleanLaw V) :
    H.toPaperLinear (momentVector H.coordinateSupport μ) = ∑ x, μ.mass x • H.lift x := by
  rw [momentVector_eq_convexCombination, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact H.toPaperLinear.map_smul (μ.mass x) (monomialLift H.coordinateSupport x)

/-- The displayed convex combination belongs to the literal multilinear polytope. -/
theorem convexCombination_lift_mem_polytope (H : PaperHypergraph V) (μ : BooleanLaw V) :
    (∑ x, μ.mass x • H.lift x) ∈ H.polytope := by
  rw [← H.toPaper_momentVector_eq_convexCombination μ,
    H.polytope_eq_image_multilinearPolytope]
  exact ⟨momentVector H.coordinateSupport μ,
    (mem_multilinearPolytope_iff _ _).mpr ⟨μ, rfl⟩, rfl⟩

end PaperHypergraph
end AlphaCycle
