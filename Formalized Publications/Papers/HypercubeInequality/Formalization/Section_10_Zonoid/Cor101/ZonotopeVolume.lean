import Section_10_Zonoid.Cor101.ZonotopeProjection
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Data.Finset.Powerset

/-!
# Arbitrary-generator zonotope volume

The geometric proof first expresses volume as a sum of the ordinary volumes
of the full-dimensional sub-parallelotopes. It uses induction on dimension and
on the generator set, together with the compact-convex extrusion formula.
Repeated vectors, zero vectors and rank-deficient families are allowed.
-/

open MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal Pointwise

noncomputable section

namespace Cor101.Zonotope

variable {ι E F : Type*} [DecidableEq ι]

/-- A zonotope with labels in a finite set; the generators need not be distinct. -/
def finiteZonotope [AddCommGroup E] [Module ℝ E] (s : Finset ι) (v : ι → E) : Set E :=
  ∑ i ∈ s, segment ℝ 0 (v i)

section Algebra

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

omit [DecidableEq ι] in
@[simp] lemma finiteZonotope_empty (v : ι → E) : finiteZonotope ∅ v = {0} := by
  simp only [finiteZonotope, Finset.sum_empty]
  rfl

lemma finiteZonotope_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (v : ι → E) :
    finiteZonotope (insert a s) v = finiteZonotope s v + segment ℝ 0 (v a) := by
  simp only [finiteZonotope, Finset.sum_insert ha]
  exact add_comm _ _

omit [DecidableEq ι] in
lemma finiteZonotope_eq_parallelepiped (s : Finset ι) (v : ι → E) :
    finiteZonotope s v = parallelepiped (fun i : s => v i) := by
  rw [parallelepiped_eq_sum_segment]
  exact (Finset.sum_coe_sort s _).symm

omit [DecidableEq ι] in
lemma linear_image_finiteZonotope (s : Finset ι) (v : ι → E) (f : E →ₗ[ℝ] F) :
    f '' finiteZonotope s v = finiteZonotope s (f ∘ v) := by
  simp only [finiteZonotope_eq_parallelepiped, image_parallelepiped, Function.comp_def]

omit [DecidableEq ι] in
lemma zero_mem_finiteZonotope (s : Finset ι) (v : ι → E) :
    0 ∈ finiteZonotope s v := by
  rw [finiteZonotope_eq_parallelepiped, mem_parallelepiped_iff]
  exact ⟨0, ⟨le_rfl, by intro i; norm_num⟩, by simp⟩

lemma finiteZonotope_insert_zero {a : ι} {s : Finset ι} (ha : a ∉ s)
    (v : ι → E) (hv : v a = 0) :
    finiteZonotope (insert a s) v = finiteZonotope s v := by
  rw [finiteZonotope_insert ha, hv, segment_same]
  change finiteZonotope s v + 0 = finiteZonotope s v
  exact add_zero _

omit [DecidableEq ι] in
lemma finiteZonotope_subset_span (s : Finset ι) (v : ι → E) :
    finiteZonotope s v ⊆ Submodule.span ℝ (range fun i : s => v i) := by
  intro x hx
  rw [finiteZonotope_eq_parallelepiped, mem_parallelepiped_iff] at hx
  rcases hx with ⟨t, ht, rfl⟩
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))

end Algebra

section Topology

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
lemma isCompact_finiteZonotope (s : Finset ι) (v : ι → E) :
    IsCompact (finiteZonotope s v) := by
  rw [finiteZonotope_eq_parallelepiped, parallelepiped]
  exact isCompact_Icc.image (by fun_prop)

omit [DecidableEq ι] in
lemma convex_finiteZonotope (s : Finset ι) (v : ι → E) :
    Convex ℝ (finiteZonotope s v) := by
  rw [finiteZonotope_eq_parallelepiped]
  exact convex_parallelepiped _

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in
/-- Fewer than ambient-dimension generators give zero ambient volume. -/
lemma measure_finiteZonotope_eq_zero_of_card_lt (μ : Measure E) [IsAddHaarMeasure μ]
    (s : Finset ι) (v : ι → E) (hs : s.card < finrank ℝ E) :
    μ (finiteZonotope s v) = 0 := by
  apply measure_mono_null (finiteZonotope_subset_span s v)
  apply Measure.addHaar_submodule μ
  intro htop
  have hle := finrank_le_of_span_eq_top (v := fun i : s => v i) htop
  simp only [Fintype.card_coe] at hle
  omega

end Topology

section Extrusion

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Adding a nonzero generator adds its length times the projected volume. -/
lemma volume_finiteZonotope_insert {a : ι} {s : Finset ι} (ha : a ∉ s)
    (v : ι → E) (hv : v a ≠ 0) :
    volume (finiteZonotope (insert a s) v) = volume (finiteZonotope s v) +
      ENNReal.ofReal ‖v a‖ * volume (finiteZonotope s
        ((perpendicular (‖v a‖⁻¹ • v a)).orthogonalProjectionOnto ∘ v)) := by
  rw [finiteZonotope_insert ha,
    volume_add_segment (v a) hv (isCompact_finiteZonotope s v) (convex_finiteZonotope s v)]
  apply congrArg (fun A : Set (perpendicular (‖v a‖⁻¹ • v a)) =>
    volume (finiteZonotope s v) + ENNReal.ofReal ‖v a‖ * volume A)
  exact linear_image_finiteZonotope s v
    (perpendicular (‖v a‖⁻¹ • v a)).orthogonalProjectionOnto.toLinearMap

end Extrusion

/-- The two classes in the Pascal recurrence for fixed-cardinality subsets
are disjoint, so their summands can be separated without inequalities. -/
lemma sum_powersetCard_succ_insert {M : Type*} [AddCommMonoid M]
    {a : ι} {s : Finset ι} (ha : a ∉ s) (n : ℕ) (f : Finset ι → M) :
    ∑ t ∈ (insert a s).powersetCard (n + 1), f t =
      (∑ t ∈ s.powersetCard (n + 1), f t) +
        ∑ t ∈ s.powersetCard n, f (insert a t) := by
  rw [Finset.powersetCard_succ_insert ha]
  rw [Finset.sum_union]
  · congr 1
    apply Finset.sum_image
    intro t ht u hu htu
    have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.mp ht).1 h)
    have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    ext i
    have he := congrArg (fun r : Finset ι => i ∈ r) htu
    by_cases hi : i = a
    · subst i; simp [hat, hau]
    · simpa [hi] using he
  · apply Finset.disjoint_left.mpr
    intro t ht hti
    rcases Finset.mem_image.mp hti with ⟨u, hu, rfl⟩
    exact ha ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))

universe u

private theorem volume_finiteZonotope_subsets_aux (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
      finrank ℝ E = n → ∀ (s : Finset ι) (v : ι → E),
        volume (finiteZonotope s v) =
          ∑ t ∈ s.powersetCard n, volume (finiteZonotope t v) := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ hdim s v
    let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    simp only [Finset.powersetCard_zero, Finset.sum_singleton]
    congr 1
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx, zero_mem_finiteZonotope]
  | succ n ih =>
    intro E _ _ _ _ _ hdim s v
    induction s using Finset.induction_on with
    | empty =>
      have hz := measure_finiteZonotope_eq_zero_of_card_lt volume (∅ : Finset ι) v
        (by simp [hdim])
      rw [Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty]
      exact hz
    | @insert a s ha hs =>
      rw [sum_powersetCard_succ_insert ha]
      by_cases hva : v a = 0
      · rw [finiteZonotope_insert_zero ha v hva, hs]
        have hz : ∑ t ∈ s.powersetCard n, volume (finiteZonotope (insert a t) v) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          have hts := (Finset.mem_powersetCard.mp ht).1
          have htc := (Finset.mem_powersetCard.mp ht).2
          rw [finiteZonotope_insert_zero (fun hat => ha (hts hat)) v hva]
          apply measure_finiteZonotope_eq_zero_of_card_lt
          omega
        rw [hz, add_zero]
      · let u : E := ‖v a‖⁻¹ • v a
        let p : E →L[ℝ] perpendicular u := (perpendicular u).orthogonalProjectionOnto
        have hu : u ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hva)) hva
        let : Fact (finrank ℝ E = n + 1) := ⟨hdim⟩
        have hdim' : finrank ℝ (perpendicular u) = n :=
          Submodule.finrank_orthogonal_span_singleton hu
        have hrec (t : Finset ι) (hat : a ∉ t) :
            volume (finiteZonotope (insert a t) v) =
              volume (finiteZonotope t v) + ENNReal.ofReal ‖v a‖ *
                volume (finiteZonotope t (p ∘ v)) :=
          volume_finiteZonotope_insert hat v hva
        rw [hrec s ha, hs, ih hdim', Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        have hts := (Finset.mem_powersetCard.mp ht).1
        have htc := (Finset.mem_powersetCard.mp ht).2
        rw [hrec t (fun hat => ha (hts hat)),
          measure_finiteZonotope_eq_zero_of_card_lt volume t v (by omega), zero_add]

/-- The genuine volume of any finite zonotope is the sum of the genuine
volumes of its sub-parallelotopes with ambient-dimension many labels.
No independence, nonzero-generator or full-dimensionality hypothesis is used. -/
theorem volume_finiteZonotope_subsets
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Finset ι) (v : ι → E) :
    volume (finiteZonotope s v) =
      ∑ t ∈ s.powersetCard (finrank ℝ E), volume (finiteZonotope t v) :=
  volume_finiteZonotope_subsets_aux _ rfl s v

end Cor101.Zonotope
