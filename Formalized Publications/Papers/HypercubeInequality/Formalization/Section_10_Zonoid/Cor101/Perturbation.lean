import Section_10_Zonoid.Cor101.Images
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Convergence under perturbation of finitely many generators

The Hausdorff estimate here is obtained by using the same coefficients in
the two Minkowski sums. It proves convergence of the actual zonotopes.
No volume-continuity assertion is assumed or proved in this file.
-/

noncomputable section

open scoped BigOperators

namespace Cor101

section FiniteGenerators

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- The convex body given by a finite sum of the segments [0,v_i]. -/
def zonotopeBody (v : ι -> E) : ConvexBody E where
  carrier := parallelepiped v
  convex' := convex_parallelepiped v
  isCompact' := by
    unfold parallelepiped
    apply isCompact_Icc.image
    exact continuous_finsetSum Finset.univ
      (fun i _ => (continuous_apply i).smul continuous_const)
  nonempty' := by
    refine ⟨0, (mem_parallelepiped_iff v 0).2 ?_⟩
    exact ⟨0, by simp, by simp⟩

@[simp] theorem coe_zonotopeBody (v : ι -> E) :
    (zonotopeBody v : Set E) = parallelepiped v := rfl

/-- Reusing coefficients in [0,1] controls the displacement of every point
by the sum of the displacements of the generators. -/
theorem same_coefficients_dist_le (v w : ι -> E) (t : ι -> Real)
    (ht : t ∈ Set.Icc (0 : ι -> Real) 1) :
    dist (∑ i, t i • v i) (∑ i, t i • w i) <= ∑ i, ‖v i - w i‖ := by
  classical
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    ‖∑ i, t i • (v i - w i)‖ <= ∑ i, ‖t i • (v i - w i)‖ :=
      norm_sum_le _ _
    _ <= ∑ i, ‖v i - w i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
      exact mul_le_of_le_one_left (norm_nonneg _) (ht.2 i)

/-- The Hausdorff distance of two finite zonotopes is bounded by the sum
of the displacements of their correspondingly indexed generators. -/
theorem zonotopeBody_dist_le_sum (v w : ι -> E) :
    dist (zonotopeBody v) (zonotopeBody w) <= ∑ i, ‖v i - w i‖ := by
  classical
  change Metric.hausdorffDist (parallelepiped v) (parallelepiped w) <= _
  apply Metric.hausdorffDist_le_of_mem_dist (Finset.sum_nonneg (by simp))
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff v x).1 hx
    refine ⟨∑ i, t i • w i, (mem_parallelepiped_iff w _).2 ⟨t, ht, rfl⟩, ?_⟩
    exact same_coefficients_dist_le v w t ht
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff w x).1 hx
    refine ⟨∑ i, t i • v i, (mem_parallelepiped_iff v _).2 ⟨t, ht, rfl⟩, ?_⟩
    simpa only [norm_sub_rev] using same_coefficients_dist_le w v t ht

/-- With the sup norm on the finite family of generators, the zonotope
construction is Lipschitz with constant equal to the number of generators. -/
theorem zonotopeBody_lipschitz :
    LipschitzWith (Fintype.card ι : NNReal) (@zonotopeBody ι E _ _ _) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro v w
  calc
    dist (zonotopeBody v) (zonotopeBody w) <= ∑ i, ‖v i - w i‖ :=
      zonotopeBody_dist_le_sum v w
    _ <= ∑ i : ι, ‖v - w‖ :=
      Finset.sum_le_sum (fun i _ => norm_le_pi_norm (v - w) i)
    _ = ((Fintype.card ι : NNReal) : Real) * dist v w := by
      simp [dist_eq_norm]

/-- Continuous movement of finitely many generators gives Hausdorff
continuous movement of their zonotope. -/
theorem zonotopeBody_continuous : Continuous (@zonotopeBody ι E _ _ _) :=
  zonotopeBody_lipschitz.continuous

end FiniteGenerators

/-- The bundled segment sum agrees with the project's geometric definition
of a zonotope. No nonzero or linear-independence hypothesis is needed. -/
theorem zonotopeBody_isZonotope {d N : Nat} (v : Fin N -> Space d) :
    IsZonotope (zonotopeBody v) := by
  refine ⟨N, 0, v, ?_⟩
  simp only [coe_zonotopeBody, zero_add, Set.image_id']

/-- The unit vector in the final coordinate direction. -/
def verticalUnit (d : Nat) : Space d :=
  EuclideanSpace.basisFun (Fin (d + 1)) Real (Fin.last d)

@[simp] theorem verticalUnit_last (d : Nat) :
    verticalUnit d (Fin.last d) = 1 := by
  simp [verticalUnit, EuclideanSpace.basisFun_apply]

@[simp] theorem verticalUnit_norm (d : Nat) : ‖verticalUnit d‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (d + 1)) Real).norm_eq_one (Fin.last d)

/-- Shift every generator upward by epsilon in its final coordinate. -/
def verticalPerturbation {d N : Nat} (v : Fin N -> Space d) (epsilon : Real) :
    Fin N -> Space d :=
  fun i => v i + epsilon • verticalUnit d

@[simp] theorem verticalPerturbation_last {d N : Nat}
    (v : Fin N -> Space d) (epsilon : Real) (i : Fin N) :
    verticalPerturbation v epsilon i (Fin.last d) = v i (Fin.last d) + epsilon := by
  simp [verticalPerturbation, PiLp.add_apply, PiLp.smul_apply]

/-- After orienting the generators with nonnegative heights, any positive
vertical perturbation makes every height strictly positive. -/
theorem verticalPerturbation_positive {d N : Nat}
    (v : Fin N -> Space d) (hv : forall i, 0 <= v i (Fin.last d))
    {epsilon : Real} (hepsilon : 0 < epsilon) (i : Fin N) :
    0 < verticalPerturbation v epsilon i (Fin.last d) := by
  rw [verticalPerturbation_last]
  exact add_pos_of_nonneg_of_pos (hv i) hepsilon

@[simp] theorem verticalPerturbation_zero {d N : Nat} (v : Fin N -> Space d) :
    verticalPerturbation v 0 = v := by
  funext i
  simp [verticalPerturbation]

theorem verticalPerturbation_continuous {d N : Nat} (v : Fin N -> Space d) :
    Continuous (verticalPerturbation v) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- The upward perturbation converges to the original actual zonotope as
epsilon tends to zero. -/
theorem verticalPerturbation_tendsto {d N : Nat} (v : Fin N -> Space d) :
    Filter.Tendsto (fun epsilon => zonotopeBody (verticalPerturbation v epsilon))
      (nhds 0) (nhds (zonotopeBody v)) := by
  simpa only [Function.comp_def, verticalPerturbation_zero] using
    (zonotopeBody_continuous.comp (verticalPerturbation_continuous v)).tendsto 0

/-- Perturb only generators whose final coordinate is zero. The other
generators are unchanged. -/
def removeHorizontal {d N : Nat} (v : Fin N -> Space d) (epsilon : Real) :
    Fin N -> Space d :=
  fun i => if v i (Fin.last d) = 0 then v i + epsilon • verticalUnit d else v i

/-- Every perturbed generator has nonzero final coordinate whenever
epsilon is nonzero. This includes generators that were zero vectors. -/
theorem removeHorizontal_last_ne_zero {d N : Nat} (v : Fin N -> Space d)
    {epsilon : Real} (hepsilon : epsilon ≠ 0) (i : Fin N) :
    removeHorizontal v epsilon i (Fin.last d) ≠ 0 := by
  classical
  by_cases hi : v i (Fin.last d) = 0
  · simpa [removeHorizontal, hi, PiLp.add_apply, PiLp.smul_apply] using hepsilon
  · simp [removeHorizontal, hi]

@[simp] theorem removeHorizontal_zero {d N : Nat} (v : Fin N -> Space d) :
    removeHorizontal v 0 = v := by
  classical
  funext i
  simp [removeHorizontal]

theorem removeHorizontal_continuous {d N : Nat} (v : Fin N -> Space d) :
    Continuous (removeHorizontal v) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : v i (Fin.last d) = 0
  · simp only [removeHorizontal, hi, ite_true]
    exact continuous_const.add (continuous_id.smul continuous_const)
  · simp only [removeHorizontal, hi, ite_false]
    exact continuous_const

/-- The zonotopes with horizontal generators removed converge in actual
Hausdorff distance to the original zonotope. -/
theorem removeHorizontal_tendsto {d N : Nat} (v : Fin N -> Space d) :
    Filter.Tendsto (fun epsilon => zonotopeBody (removeHorizontal v epsilon))
      (nhds 0) (nhds (zonotopeBody v)) := by
  simpa only [Function.comp_def, removeHorizontal_zero] using
    (zonotopeBody_continuous.comp (removeHorizontal_continuous v)).tendsto 0

/-- Explicit sequence form of the horizontal-generator approximation.
This is set convergence only; passage to volumes is a separate theorem. -/
theorem exists_nonhorizontal_zonotope_sequence {d N : Nat}
    (v : Fin N -> Space d) :
    ∃ w : Nat -> Fin N -> Space d,
      (forall n i, w n i (Fin.last d) ≠ 0) ∧
      Filter.Tendsto (fun n => zonotopeBody (w n)) Filter.atTop
        (nhds (zonotopeBody v)) := by
  refine ⟨fun n => removeHorizontal v (1 / ((n : Real) + 1)), ?_, ?_⟩
  · intro n i
    apply removeHorizontal_last_ne_zero
    positivity
  · exact (removeHorizontal_tendsto v).comp tendsto_one_div_add_atTop_nhds_zero_nat

end Cor101
