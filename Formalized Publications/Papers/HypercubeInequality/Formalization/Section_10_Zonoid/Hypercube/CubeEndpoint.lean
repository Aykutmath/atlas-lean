import Section_10_Zonoid.Hypercube.CubeNormalization
import Section_10_Zonoid.Hypercube.EndpointAssembly
import Section_10_Zonoid.Hypercube.FiniteAtomicGeneric

/-!
The paper's literal weighted cube inequality, obtained from the random-simplex
theorem through an explicit finite probability law. The normalized cube volume
remains factorial times actual Lebesgue convex-hull volume throughout.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.CubeEndpoint

open Paper

def cubeLaw {d : Nat} (q : Cube d -> Real) : Measure (Point d) :=
  FiniteAtomicGeneric.atomicLaw q cubePoint

theorem cubeLaw_probability {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) (hqsum : totalWeight q = 1) :
    IsProbabilityMeasure (cubeLaw q) := by
  let _ := FiniteAtomicGeneric.labelMeasure_isProbability q hq hqsum
  unfold cubeLaw FiniteAtomicGeneric.atomicLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable cubePoint).aemeasurable).mpr inferInstance

theorem cubeLaw_first_moments {d : Nat} (q : Cube d -> Real) :
    finiteCoordinateFirstMoments (cubeLaw q) := by
  intro j
  have hcoord : Measurable (fun z : Point d => |z j|) :=
    continuous_abs.measurable.comp (continuous_apply j).measurable
  unfold cubeLaw FiniteAtomicGeneric.atomicLaw
  apply (integrable_map_measure hcoord.aestronglyMeasurable
    (measurable_of_countable cubePoint).aemeasurable).mpr
  exact Integrable.of_finite

theorem normalizedCubeVolume_embedding {d : Nat}
    (f : Function.Embedding (Fin (d + 1)) (Cube d)) :
    |Geometry.affineDet (fun i => cubePoint (f i))| =
      normalizedCubeVolume (Counting.rangeFinset f) := by
  classical
  have hrange : Set.range (fun i => cubePoint (f i)) =
      cubePoint '' (Counting.rangeFinset f : Set (Cube d)) := by
    ext x
    constructor
    next =>
      intro hx
      cases hx with
      | intro r hr =>
          exact Exists.intro (f r)
            (And.intro ((Counting.mem_range f (f r)).mpr (Exists.intro r rfl)) hr)
    next =>
      intro hx
      cases hx with
      | intro v hv =>
          cases hv with
          | intro hmem hvx =>
              cases (Counting.mem_range f v).mp hmem with
              | intro r hr =>
                  refine Exists.intro r ?_
                  change cubePoint (f r) = x
                  rw [hr]
                  exact hvx
  rw [<- Geometry.simplex_volume_factorial]
  unfold Geometry.simplexVolume Geometry.simplexHull normalizedCubeVolume
  rw [hrange]

theorem cube_tuple_determinant_zero {d : Nat} (f : Fin (d + 1) -> Cube d)
    (hf : Not (Function.Injective f)) :
    |Geometry.affineDet (fun i => cubePoint (f i))| = 0 := by
  apply abs_eq_zero.mpr
  exact Sampling.rowsDet_zero_of_noninjective
    (fun v => Fin.lastCases 1 (cubePoint v)) f hf

/-- Exact source S_d=(d+1) times the normalized subset sum. -/
theorem cubeLaw_expectedSimplexVolume {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) :
    expectedSimplexVolume (cubeLaw q) =
      ((d + 1 : Nat) : Real) * cubeSimplexSum q := by
  have h := EndpointAssembly.expected_volume_normalization (cubeLaw q)
  have hF : StronglyMeasurable
      (fun z : Fin (d + 1) -> Point d => |Geometry.affineDet z|) := by
    simpa only [Function.comp_def] using
      (continuous_abs.comp EndpointAssembly.affineDet_continuous).stronglyMeasurable
  rw [cubeLaw, FiniteAtomicGeneric.iid_atomicLaw_integral q hq cubePoint
    (fun z : Fin (d + 1) -> Point d => |Geometry.affineDet z|) hF] at h
  have hcount := Counting.weighted_tuples_vanishing_repeats (d + 1) q
    (fun f => |Geometry.affineDet (fun i => cubePoint (f i))|)
    normalizedCubeVolume normalizedCubeVolume_embedding cube_tuple_determinant_zero
  rw [hcount] at h
  have hsum : Finset.sum
      (Finset.univ.filter (fun S : Finset (Cube d) => S.card = d + 1))
      (fun S => Finset.prod S q * normalizedCubeVolume S) = cubeSimplexSum q := by
    unfold cubeSimplexSum
    rw [Finset.univ_filter_card_eq]
    apply Finset.sum_congr rfl
    intro S _
    exact mul_comm _ _
  rw [hsum] at h
  have hfac : Not ((d.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero d
  apply (mul_right_inj' hfac).mp
  calc
    (d.factorial : Real) * expectedSimplexVolume (cubeLaw q) =
        ((d + 1).factorial : Real) * cubeSimplexSum q := h
    _ = (d.factorial : Real) * (((d + 1 : Nat) : Real) * cubeSimplexSum q) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      ring

theorem facetWeight_indicator_sum {d : Nat} (q : Cube d -> Real)
    (j : Fin d) (b : Bool) :
    Finset.sum Finset.univ (fun v => q v * (if v j = b then 1 else 0)) =
      facetWeight q j b := by
  classical
  unfold facetWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v j = b
  all_goals simp only [hv, ite_true, ite_false, mul_one, mul_zero]

theorem cube_gap_sum {d : Nat} (q : Cube d -> Real) (j : Fin d) :
    Finset.sum Finset.univ (fun v => Finset.sum Finset.univ
      (fun w => q v * q w * |cubePoint v j - cubePoint w j|)) =
      2 * facetWeight q j true * facetWeight q j false := by
  classical
  let a : Cube d -> Real := fun v => q v * (if v j = true then 1 else 0)
  let b : Cube d -> Real := fun v => q v * (if v j = false then 1 else 0)
  have hpair (v w : Cube d) : q v * q w * |cubePoint v j - cubePoint w j| =
      a v * b w + b v * a w := by
    cases hv : v j
    all_goals cases hw : w j
    all_goals simp [cubePoint, a, b, hv, hw]
  simp_rw [hpair, Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.sum_mul]
  have ha : Finset.sum Finset.univ a = facetWeight q j true :=
    facetWeight_indicator_sum q j true
  have hb : Finset.sum Finset.univ b = facetWeight q j false :=
    facetWeight_indicator_sum q j false
  rw [ha, hb]
  ring

theorem cubeLaw_coordinateGap {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) (j : Fin d) :
    coordinateGap (cubeLaw q) j =
      2 * facetWeight q j true * facetWeight q j false := by
  have hF : StronglyMeasurable
      (fun zz : Prod (Point d) (Point d) => |zz.1 j - zz.2 j|) :=
    (continuous_abs.comp
      (((continuous_apply j).comp continuous_fst).sub
        ((continuous_apply j).comp continuous_snd))).stronglyMeasurable
  unfold coordinateGap cubeLaw
  rw [FiniteAtomicGeneric.pair_atomicLaw_integral q hq cubePoint _ hF]
  exact cube_gap_sum q j

theorem cubeLaw_coordinateGap_probability {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) (hqsum : totalWeight q = 1) (j : Fin d) :
    coordinateGap (cubeLaw q) j =
      2 * facetWeight q j true * (1 - facetWeight q j true) := by
  have h := CubeNormalization.facets_split_total q j
  rw [hqsum] at h
  rw [cubeLaw_coordinateGap q hq j]
  congr 1
  linarith

theorem cubeLaw_coordinateGap_product {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) :
    Finset.prod Finset.univ (fun j => coordinateGap (cubeLaw q) j) =
      (2 : Real) ^ d * Finset.prod Finset.univ
        (fun j => facetWeight q j true * facetWeight q j false) := by
  simp_rw [cubeLaw_coordinateGap q hq]
  have heq (j : Fin d) :
      2 * facetWeight q j true * facetWeight q j false =
        2 * (facetWeight q j true * facetWeight q j false) := by ring
  simp_rw [heq]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]

theorem randomSimplex_cubeLaw_iff_weightedCube {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) (hqsum : totalWeight q = 1) :
    randomSimplexClaim d (cubeLaw q) <-> weightedCubeClaim d q := by
  unfold randomSimplexClaim weightedCubeClaim
  rw [cubeLaw_expectedSimplexVolume q hq, cubeLaw_coordinateGap_product q hq, hqsum]
  simp only [one_pow, mul_one]
  have hc (P : Real) : mainCoefficient d * ((2 : Real) ^ d * P) =
      ((d + 1 : Nat) : Real) * P := by
    unfold mainCoefficient Constants.mainCoefficient
    field_simp
  rw [hc]
  have hprod : Finset.prod Finset.univ
      (fun j => facetWeight q j false * facetWeight q j true) =
      Finset.prod Finset.univ
        (fun j => facetWeight q j true * facetWeight q j false) := by
    apply Finset.prod_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hprod]
  have hpos : 0 < ((d + 1 : Nat) : Real) := by positivity
  constructor
  next => exact fun h => le_of_mul_le_mul_left h hpos
  next => exact fun h => mul_le_mul_of_nonneg_left h hpos.le

theorem cube_probability_form_iff_randomSimplex {d : Nat} (q : Cube d -> Real)
    (hq : forall v, 0 <= q v) (hqsum : totalWeight q = 1) :
    (cubeSimplexSum q <= Finset.prod Finset.univ
      (fun j => facetWeight q j true * (1 - facetWeight q j true))) <->
        randomSimplexClaim d (cubeLaw q) :=
  (CubeNormalization.probability_form_equivalence q hqsum).symm.trans
    (randomSimplex_cubeLaw_iff_weightedCube q hq hqsum).symm

theorem weightedCube_probability_of_randomSimplex
    (hrandom : allDimensionsRandomSimplex) (d : Nat) (hd : 1 <= d)
    (q : Cube d -> Real) (hq : forall v, 0 <= q v) (hqsum : totalWeight q = 1) :
    weightedCubeClaim d q := by
  have h := hrandom d hd (cubeLaw q) (cubeLaw_probability q hq hqsum)
    (cubeLaw_first_moments q)
  unfold randomSimplexClaim at h
  rw [cubeLaw_expectedSimplexVolume q hq, cubeLaw_coordinateGap_product q hq] at h
  have hc (P : Real) : mainCoefficient d * ((2 : Real) ^ d * P) =
      ((d + 1 : Nat) : Real) * P := by
    unfold mainCoefficient Constants.mainCoefficient
    field_simp
  rw [hc] at h
  have hpos : 0 < ((d + 1 : Nat) : Real) := by positivity
  have hsum := le_of_mul_le_mul_left h hpos
  unfold weightedCubeClaim
  rw [hqsum]
  simp only [one_pow, mul_one]
  have hprod : Finset.prod Finset.univ
      (fun j => facetWeight q j true * facetWeight q j false) =
      Finset.prod Finset.univ
        (fun j => facetWeight q j false * facetWeight q j true) := by
    apply Finset.prod_congr rfl
    intro j _
    exact mul_comm _ _
  rw [<- hprod]
  exact hsum

/-- The source weighted Hypercube inequality follows from the actual random-simplex theorem. -/
theorem hypercube_of_randomSimplex (hrandom : allDimensionsRandomSimplex) :
    allDimensionsHypercube := by
  intro d hd x hx
  by_cases hzero : totalWeight x = 0
  next => exact CubeNormalization.weightedCube_zero_total x hx hzero
  next =>
    have hQ : 0 < totalWeight x :=
      lt_of_le_of_ne (CubeNormalization.totalWeight_nonneg x hx) (Ne.symm hzero)
    have hq := CubeNormalization.normalized_nonneg x hx hQ
    have hqsum := CubeNormalization.normalized_total x hQ
    exact (CubeNormalization.normalization_equivalence hd x hQ).mp
      (weightedCube_probability_of_randomSimplex hrandom d hd _ hq hqsum)

end Hypercube.CubeEndpoint
