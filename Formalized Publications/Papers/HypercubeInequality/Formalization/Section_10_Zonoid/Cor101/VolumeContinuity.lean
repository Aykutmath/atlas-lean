import Section_10_Zonoid.Cor101.Definitions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Hausdorff continuity of volume of convex bodies

The proof works for every compact convex body, including bodies with empty
interior. Indicators converge outside the null frontier of the limiting body.
-/

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology ENNReal

namespace Cor101

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point with an interior ball in `K` belongs to every convex body at
Hausdorff distance less than that ball's radius. -/
theorem mem_convexBody_of_closedBall_subset {K L : ConvexBody E} {x : E} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set E)) (hKL : dist K L < r) :
    x ∈ L := by
  by_contra hx
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    L.nonempty L.isCompact.isComplete L.convex x
  have hsep := (norm_eq_iInf_iff_real_inner_le_zero L.convex hy).mp hmin
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (fun h => hx (h ▸ hy))
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr hxy
  let z : E := x + (r / ‖x - y‖) • (x - y)
  have hzx : dist z x = r := by
    simp only [z, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hn)]
    exact div_mul_cancel₀ r (ne_of_gt hn)
  have hz : z ∈ K := hball (mem_closedBall.mpr hzx.le)
  obtain ⟨w, hw, hzw⟩ := exists_dist_lt_of_hausdorffDist_lt hz hKL
    (ConvexBody.hausdorffEDist_ne_top (K := K) (L := L))
  have hsepw := hsep w hw
  have hbound : inner ℝ (x - y) (z - w) < ‖x - y‖ * r := by
    calc
      inner ℝ (x - y) (z - w) ≤ ‖x - y‖ * ‖z - w‖ := real_inner_le_norm _ _
      _ < ‖x - y‖ * r := mul_lt_mul_of_pos_left (by simpa [dist_eq_norm] using hzw) hn
  have hsplit : inner ℝ (x - y) (z - y) =
      inner ℝ (x - y) (z - w) + inner ℝ (x - y) (w - y) := by
    rw [← inner_add_right]
    congr 1
    abel
  have hvalue : inner ℝ (x - y) (z - y) = ‖x - y‖ ^ 2 + r * ‖x - y‖ := by
    have heq : z - y = (x - y) + (r / ‖x - y‖) • (x - y) := by
      dsimp [z]
      abel
    rw [heq, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  nlinarith [sq_nonneg ‖x - y‖]

/-- Every interior point of a convex body remains in all sufficiently close
convex bodies. -/
theorem eventually_mem_convexBody_of_mem_interior (K : ConvexBody E) {x : E}
    (hx : x ∈ interior (K : Set E)) : ∀ᶠ L : ConvexBody E in 𝓝 K, x ∈ L := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hsmall : closedBall x (r / 2) ⊆ (K : Set E) :=
    (closedBall_subset_ball (by linarith)).trans hball
  filter_upwards [Metric.ball_mem_nhds K (half_pos hr)] with L hL
  apply mem_convexBody_of_closedBall_subset (half_pos hr) hsmall
  simpa only [mem_ball, dist_comm] using hL

/-- Exterior points of a closed convex body remain exterior to all sufficiently
close bodies. This fact only uses compactness, not convexity. -/
theorem eventually_notMem_convexBody_of_notMem (K : ConvexBody E) {x : E}
    (hx : x ∉ K) : ∀ᶠ L : ConvexBody E in 𝓝 K, x ∉ L := by
  have hpos : 0 < infDist x (K : Set E) :=
    (K.isClosed.notMem_iff_infDist_pos K.nonempty).mp hx
  filter_upwards [Metric.ball_mem_nhds K hpos] with L hL hxL
  have hle := infDist_le_hausdorffDist_of_mem hxL
    (ConvexBody.hausdorffEDist_ne_top (K := L) (L := K))
  have hlt : dist L K < infDist x (K : Set E) := hL
  exact (not_lt_of_ge hle) hlt

end Geometry

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Haar measure is continuous on compact convex bodies for Hausdorff distance.
No full-dimensionality assumption is needed. -/
theorem continuous_measure_convexBody (μ : Measure E) [IsAddHaarMeasure μ] :
    Continuous (fun K : ConvexBody E => μ (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  apply tendsto_measure_of_ae_tendsto_indicator (𝓝 K) K.isClosed.measurableSet
    (fun L => L.isClosed.measurableSet) (B := cthickening 1 (K : Set E))
    isClosed_cthickening.measurableSet K.isBounded.cthickening.measure_lt_top.ne
  · filter_upwards [Metric.ball_mem_nhds K (by norm_num : (0 : ℝ) < 1)] with L hL
    intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hL
      (ConvexBody.hausdorffEDist_ne_top (K := L) (L := K))
    exact mem_cthickening_of_dist_le x y 1 (K : Set E) hy hxy.le
  · have hfrontier : ∀ᵐ x ∂μ, x ∉ frontier (K : Set E) := by
      apply ae_iff.mpr
      simpa only [not_not, ofPred_mem_eq] using K.convex.addHaar_frontier μ
    filter_upwards [hfrontier] with x hx
    by_cases hxK : x ∈ K
    · have hxint : x ∈ interior (K : Set E) := by
        by_contra hxi
        exact hx ⟨subset_closure hxK, hxi⟩
      filter_upwards [eventually_mem_convexBody_of_mem_interior K hxint] with L hL
      exact iff_of_true hL hxK
    · filter_upwards [eventually_notMem_convexBody_of_notMem K hxK] with L hL
      exact iff_of_false hL hxK

end Measure

/-- The canonical volume of compact convex bodies is Hausdorff-continuous,
including at all lower-dimensional bodies. -/
theorem continuous_volume_convexBody {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)] :
    Continuous (fun K : ConvexBody E => volume (K : Set E)) :=
  continuous_measure_convexBody volume

/-- Continuity of the ambient Euclidean volume used in Corollary 10.1. -/
theorem fullVolume_continuous (d : ℕ) :
    Continuous (fullVolume (d := d)) := continuous_volume_convexBody

end Cor101
