import Section_10_Zonoid.Cor101.Perturbation
import Section_10_Zonoid.Cor101.Sharpness

/-!
# The line-projection normalization for finite zonotopes

The measure here is the actual normalized Euclidean Hausdorff length from
`Definitions.lean`. No zonotope volume formula is assumed.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Cor101

/-- The real line included isometrically as the final coordinate axis. -/
def lineEmbeddingLinear (d : Nat) : Real →ₗ[Real] Space d :=
  LinearMap.toSpanSingleton Real (Space d) (EuclideanSpace.single (Fin.last d) 1)

theorem lineEmbeddingLinear_apply (d : Nat) (t : Real) :
    lineEmbeddingLinear d t = EuclideanSpace.single (Fin.last d) t := by
  apply PiLp.ext
  intro i
  by_cases hi : i = Fin.last d <;> simp [lineEmbeddingLinear, hi]

theorem lineEmbeddingLinear_isometry (d : Nat) : Isometry (lineEmbeddingLinear d) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [lineEmbeddingLinear_apply, lineEmbeddingLinear_apply]
  exact PiLp.dist_single_same (p := 2) (β := fun _ : Fin (d + 1) => Real)
    (Fin.last d) x y

/-- Projection of an actual finite zonotope onto the common line is the
isometric image of the scalar parallelepiped of its generator heights. -/
theorem commonLineProjection_zonotopeBody {d : Nat} {ι : Type*} [Fintype ι]
    (v : ι → Space d) :
    commonLineProjection d '' (zonotopeBody v : Set (Space d)) =
      lineEmbeddingLinear d '' parallelepiped (fun i => v i (Fin.last d)) := by
  change (commonLineProjection d).toLinearMap '' parallelepiped v =
    lineEmbeddingLinear d '' parallelepiped (fun i => v i (Fin.last d))
  rw [image_parallelepiped (commonLineProjection d).toLinearMap,
    image_parallelepiped (lineEmbeddingLinear d)]
  congr 1
  funext i
  simp only [Function.comp_apply, lineEmbeddingLinear_apply]
  apply PiLp.ext
  intro j
  change (coordinateSubspace d {Fin.last d}).starProjection (v i) j = _
  rw [coordinateSubspace_projection_apply]
  by_cases hj : j = Fin.last d <;> simp [hj]

/-- Positive scalar generators fill precisely the interval from zero to
their total sum. The assertion includes an empty family and total sum zero. -/
theorem scalar_parallelepiped_nonnegative {ι : Type*} [Fintype ι]
    (b : ι → Real) (hb : forall i, 0 <= b i) :
    parallelepiped b = Set.Icc 0 (∑ i, b i) := by
  classical
  ext y
  rw [mem_parallelepiped_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (ht.1 i) (hb i))
    · exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left (hb i) (ht.2 i))
  · intro hy
    have hsum : 0 <= ∑ i, b i := Finset.sum_nonneg (fun i _ => hb i)
    by_cases hzero : ∑ i, b i = 0
    · have hyzero : y = 0 := le_antisymm (hzero ▸ hy.2) hy.1
      subst y
      refine ⟨0, ?_, ?_⟩ <;> simp
    · have hpos : 0 < ∑ i, b i := lt_of_le_of_ne hsum (Ne.symm hzero)
      refine ⟨fun _ => y / (∑ i, b i), ?_, ?_⟩
      · exact ⟨fun _ => div_nonneg hy.1 hsum,
          fun _ => (div_le_one hpos).mpr hy.2⟩
      · simp only [smul_eq_mul]
        rw [← Finset.mul_sum]
        exact (div_mul_cancel₀ y hzero).symm

/-- A scalar zonotope with arbitrary signed generators is the interval
between the sums of the lower and upper endpoints of its segments. -/
theorem scalar_parallelepiped_interval {ι : Type*} [Fintype ι]
    (b : ι → Real) :
    parallelepiped b = Set.Icc (∑ i, min 0 (b i)) (∑ i, max 0 (b i)) := by
  classical
  have hlo : (∑ i, min 0 (b i)) ∈ parallelepiped b := by
    apply (mem_parallelepiped_iff b _).mpr
    refine ⟨fun i => if 0 <= b i then 0 else 1, ?_, ?_⟩
    · constructor <;> intro i <;> dsimp <;> split_ifs <;> norm_num
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hb : 0 <= b i
      · simp [hb]
      · simp [hb, min_eq_right (le_of_not_ge hb)]
  have hhi : (∑ i, max 0 (b i)) ∈ parallelepiped b := by
    apply (mem_parallelepiped_iff b _).mpr
    refine ⟨fun i => if 0 <= b i then 1 else 0, ?_, ?_⟩
    · constructor <;> intro i <;> dsimp <;> split_ifs <;> norm_num
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hb : 0 <= b i
      · simp [hb]
      · simp [hb, max_eq_left (le_of_not_ge hb)]
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff b y).mp hy
    have hbounds (i : ι) : min 0 (b i) <= t i * b i ∧ t i * b i <= max 0 (b i) := by
      by_cases hb : 0 <= b i
      · rw [min_eq_left hb, max_eq_right hb]
        exact ⟨mul_nonneg (ht.1 i) hb, mul_le_of_le_one_left hb (ht.2 i)⟩
      · have hb' : b i <= 0 := le_of_not_ge hb
        rw [min_eq_right hb', max_eq_left hb']
        constructor
        · simpa using (mul_le_mul_of_nonpos_right (ht.2 i) hb')
        · exact mul_nonpos_of_nonneg_of_nonpos (ht.1 i) hb'
    exact ⟨Finset.sum_le_sum (fun i _ => (hbounds i).1),
      Finset.sum_le_sum (fun i _ => (hbounds i).2)⟩
  · have horder : (∑ i, min 0 (b i)) <= ∑ i, max 0 (b i) :=
      Finset.sum_le_sum (fun i _ => le_trans (min_le_left _ _) (le_max_left _ _))
    have hsegment := (convex_iff_segment_subset.mp (convex_parallelepiped b)) hlo hhi
    rwa [segment_eq_Icc horder] at hsegment

/-- The actual common-line length for arbitrary signed generators. -/
theorem lineVolume_zonotopeBody {d : Nat} {ι : Type*} [Fintype ι]
    (v : ι → Space d) :
    lineVolume (zonotopeBody v) = ENNReal.ofReal (∑ i, |v i (Fin.last d)|) := by
  unfold lineVolume
  rw [commonLineProjection_zonotopeBody, scalar_parallelepiped_interval,
    (lineEmbeddingLinear_isometry d).euclideanHausdorffMeasure_image]
  have hmeasure : (Measure.euclideanHausdorffMeasure 1 : Measure Real) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Real))
  rw [hmeasure, Real.volume_Icc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simpa using (max_sub_min_eq_abs (0 : Real) (v i (Fin.last d)))

/-- Real-valued version of the arbitrary-sign line normalization. -/
theorem lineVolume_zonotopeBody_toReal {d : Nat} {ι : Type*} [Fintype ι]
    (v : ι → Space d) :
    (lineVolume (zonotopeBody v)).toReal = ∑ i, |v i (Fin.last d)| := by
  rw [lineVolume_zonotopeBody, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- For nonnegative generator heights, the common-line length is their
sum, with the usual Euclidean normalization. -/
theorem lineVolume_zonotopeBody_nonnegative {d : Nat} {ι : Type*} [Fintype ι]
    (v : ι → Space d) (hv : forall i, 0 <= v i (Fin.last d)) :
    lineVolume (zonotopeBody v) = ENNReal.ofReal (∑ i, v i (Fin.last d)) := by
  unfold lineVolume
  rw [commonLineProjection_zonotopeBody,
    scalar_parallelepiped_nonnegative _ hv,
    (lineEmbeddingLinear_isometry d).euclideanHausdorffMeasure_image]
  have hmeasure : (Measure.euclideanHausdorffMeasure 1 : Measure Real) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Real))
  rw [hmeasure, Real.volume_Icc, sub_zero]

/-- Real-valued form of the line normalization used in the manuscript. -/
theorem lineVolume_zonotopeBody_nonnegative_toReal
    {d : Nat} {ι : Type*} [Fintype ι]
    (v : ι → Space d) (hv : forall i, 0 <= v i (Fin.last d)) :
    (lineVolume (zonotopeBody v)).toReal = ∑ i, v i (Fin.last d) := by
  rw [lineVolume_zonotopeBody_nonnegative v hv, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun i _ => hv i)

end Cor101
