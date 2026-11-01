import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic

/-!
# Volume gained by extruding a compact convex set

The proofs use ordinary product Lebesgue measure and Tonelli's theorem.
The fibers of a compact convex set are closed intervals; adding a vertical
segment increases the length of each nonempty fiber by the segment's length.
No full-dimensionality hypothesis is needed.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

namespace Cor101
namespace Zonotope

/-- Adding a nonnegative interval to a nonempty compact interval. -/
lemma Icc_add_zero_Icc {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    Icc a b + Icc 0 c = Icc a (b + c) := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩
  · intro hx
    by_cases hxb : x ≤ b
    · exact ⟨x, ⟨hx.1, hxb⟩, 0, ⟨le_rfl, hc⟩, add_zero x⟩
    · exact ⟨b, ⟨hab, le_rfl⟩, x - b,
        ⟨by linarith, by linarith [hx.2]⟩, by ring⟩

/-- The one-dimensional measure gain on a nonempty compact convex fiber. -/
lemma volume_add_Icc_of_nonempty {s : Set ℝ} (hs : IsCompact s)
    (hconv : Convex ℝ s) (hne : s.Nonempty) {c : ℝ} (hc : 0 ≤ c) :
    volume (s + Icc 0 c) = volume s + ENNReal.ofReal c := by
  have hinterval : s = Icc (sInf s) (sSup s) :=
    eq_Icc_of_connected_compact ⟨hne, Real.convex_iff_isPreconnected.mp hconv⟩ hs
  have hab : sInf s ≤ sSup s := by
    rw [hinterval] at hne
    exact nonempty_Icc.mp hne
  rw [hinterval, Icc_add_zero_Icc hab hc, Real.volume_Icc, Real.volume_Icc]
  rw [show sSup s + c - sInf s = (sSup s - sInf s) + c by ring,
    ENNReal.ofReal_add (sub_nonneg.mpr hab) hc]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vertical extrusion of a set by a segment of length `c`. -/
def extrusion (K : Set (E × ℝ)) (c : ℝ) : Set (E × ℝ) :=
  K + ({0} ×ˢ Icc 0 c)

/-- The vertical segment is the product of a singleton with its scalar interval. -/
lemma vertical_segment {c : ℝ} (hc : 0 ≤ c) :
    segment ℝ (0 : E × ℝ) (0, c) = ({0} : Set E) ×ˢ Icc 0 c := by
  have hi := image_segment ℝ (LinearMap.inr ℝ E ℝ).toAffineMap (0 : ℝ) c
  rw [segment_eq_Icc hc] at hi
  calc
    segment ℝ (0 : E × ℝ) (0, c) =
        (LinearMap.inr ℝ E ℝ) '' Icc 0 c := by
      simpa only [LinearMap.coe_toAffineMap, LinearMap.inr_apply, ← Prod.zero_eq_mk] using hi.symm
    _ = ({0} : Set E) ×ˢ Icc 0 c := by
      ext ⟨x, y⟩
      simp only [mem_image, LinearMap.inr_apply, Prod.mk.injEq, mem_prod, mem_singleton_iff]
      aesop

omit [NormedSpace ℝ E] in
lemma extrusion_eq_image (K : Set (E × ℝ)) (c : ℝ) :
    extrusion K c = (fun q : (E × ℝ) × ℝ => (q.1.1, q.1.2 + q.2)) ''
      (K ×ˢ Icc 0 c) := by
  ext p
  constructor
  · rintro ⟨q, hq, r, hr, rfl⟩
    have hr0 : r.1 = 0 := hr.1
    refine ⟨(q, r.2), ⟨hq, hr.2⟩, ?_⟩
    ext <;> simp [hr0]
  · rintro ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
    exact ⟨q, hq, (0, t), ⟨rfl, ht⟩, by ext <;> simp⟩

omit [NormedSpace ℝ E] in
lemma isCompact_extrusion {K : Set (E × ℝ)} (hK : IsCompact K) (c : ℝ) :
    IsCompact (extrusion K c) := by
  rw [extrusion_eq_image]
  exact (hK.prod isCompact_Icc).image (by fun_prop)

omit [NormedSpace ℝ E] in
lemma fiber_extrusion (K : Set (E × ℝ)) (c : ℝ) (x : E) :
    Prod.mk x ⁻¹' extrusion K c = (Prod.mk x ⁻¹' K) + Icc 0 c := by
  ext y
  constructor
  · rintro ⟨q, hq, r, hr, hqr⟩
    have hr0 : r.1 = 0 := hr.1
    have hqx : q.1 = x := by simpa [hr0] using congrArg Prod.fst hqr
    exact ⟨q.2, by simpa [← hqx] using hq, r.2, hr.2, congrArg Prod.snd hqr⟩
  · rintro ⟨u, hu, t, ht, hut⟩
    exact ⟨(x, u), hu, (0, t), ⟨rfl, ht⟩, by ext <;> simp [hut]⟩

omit [NormedSpace ℝ E] in
lemma isCompact_fiber {K : Set (E × ℝ)} (hK : IsCompact K) (x : E) :
    IsCompact (Prod.mk x ⁻¹' K) := by
  have heq : Prod.mk x ⁻¹' K =
      Prod.snd '' (K ∩ Prod.fst ⁻¹' ({x} : Set E)) := by
    ext y
    constructor
    · intro hy
      exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨hzt, hz⟩, rfl⟩
      have : z = x := hz
      simpa [← this] using hzt
  rw [heq]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd

lemma convex_fiber {K : Set (E × ℝ)} (hK : Convex ℝ K) (x : E) :
    Convex ℝ (Prod.mk x ⁻¹' K) := by
  intro y hy z hz a b ha hb hab
  have h := hK hy hz ha hb hab
  change (x, a • y + b • z) ∈ K
  simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma fiber_nonempty_iff (K : Set (E × ℝ)) (x : E) :
    (Prod.mk x ⁻¹' K).Nonempty ↔ x ∈ Prod.fst '' K := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨⟨z, y⟩, hzy, rfl⟩
    exact ⟨y, hzy⟩

lemma volume_fiber_extrusion {K : Set (E × ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    volume (Prod.mk x ⁻¹' extrusion K c) =
      volume (Prod.mk x ⁻¹' K) +
        (Prod.fst '' K).indicator (fun _ => ENNReal.ofReal c) x := by
  classical
  rw [fiber_extrusion]
  by_cases hx : x ∈ Prod.fst '' K
  · rw [indicator_of_mem hx]
    exact volume_add_Icc_of_nonempty (isCompact_fiber hK x) (convex_fiber hconv x)
      ((fiber_nonempty_iff K x).mpr hx) hc
  · have he : Prod.mk x ⁻¹' K = ∅ :=
      not_nonempty_iff_eq_empty.mp (fun h => hx ((fiber_nonempty_iff K x).mp h))
    simp [he, hx]

variable [MeasureSpace E] [BorelSpace E]

/-- The volume gained by adding a vertical segment is its length times
 the volume of the base projection. This includes empty or degenerate `K`. -/
theorem volume_extrusion {K : Set (E × ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {c : ℝ} (hc : 0 ≤ c) :
    volume (extrusion K c) = volume K +
      ENNReal.ofReal c * volume (Prod.fst '' K) := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hEm : MeasurableSet (extrusion K c) := (isCompact_extrusion hK c).measurableSet
  have hPm : MeasurableSet (Prod.fst '' K) := (hK.image continuous_fst).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hEm, Measure.prod_apply hKm]
  simp_rw [volume_fiber_extrusion hK hconv hc]
  rw [lintegral_add_left (measurable_measure_prodMk_left hKm),
    lintegral_indicator hPm, setLIntegral_const]

/-- The extrusion formula stated directly with a Minkowski segment. -/
theorem volume_add_vertical_segment {K : Set (E × ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {c : ℝ} (hc : 0 ≤ c) :
    volume (K + segment ℝ (0 : E × ℝ) (0, c)) = volume K +
      ENNReal.ofReal c * volume (Prod.fst '' K) := by
  rw [vertical_segment hc]
  exact volume_extrusion hK hconv hc

/-- Appending a vertical generator gives the geometric extrusion recurrence. -/
theorem volume_parallelepiped_cons_vertical {N : ℕ} (v : Fin N → E × ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    volume (parallelepiped (Fin.cons (0, c) v)) = volume (parallelepiped v) +
      ENNReal.ofReal c * volume (parallelepiped (fun i => (v i).1)) := by
  have hK : IsCompact (parallelepiped v) := by
    unfold parallelepiped
    exact isCompact_Icc.image (by fun_prop)
  have heq : parallelepiped (Fin.cons (0, c) v) =
      parallelepiped v + segment ℝ (0 : E × ℝ) (0, c) := by
    rw [parallelepiped_eq_sum_segment, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← parallelepiped_eq_sum_segment, add_comm]
  rw [heq, volume_add_vertical_segment hK (convex_parallelepiped v) hc]
  congr 2
  exact congrArg volume (image_parallelepiped (LinearMap.fst ℝ E ℝ) v)

end Zonotope
end Cor101
