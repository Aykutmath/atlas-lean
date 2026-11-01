import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Section_10_Zonoid.Hypercube.FiniteThreshold
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.Range

/-
Source: hypercube_readable.tex, Appendix B.
The scalar map below clips to [-r,r] and then rounds DOWN to a multiple of
1/r. It is defined also at r=0, but every mathematical bound is stated with
r>=1. The sequence uses precisely the positive paper indices r=n+1.
-/

noncomputable section

open MeasureTheory Filter

namespace Hypercube.Approximation

def clip (r : Nat) (x : Real) : Real := min (r : Real) (max (-(r : Real)) x)

def quantizeScalar (r : Nat) (x : Real) : Real :=
  (Int.floor ((r : Real) * clip r x) : Real) / (r : Real)

def quantize {m : Nat} (r : Nat) (w : Geometry.Point m) : Geometry.Point m :=
  fun j => quantizeScalar r (w j)

theorem clip_le (r : Nat) (x : Real) : clip r x <= (r : Real) := min_le_left _ _

theorem neg_le_clip (r : Nat) (x : Real) : -(r : Real) <= clip r x := by
  exact le_min ((neg_nonpos.mpr (Nat.cast_nonneg r)).trans (Nat.cast_nonneg r)) (le_max_left _ _)

theorem clip_eq_self (r : Nat) (x : Real)
    (hlo : -(r : Real) <= x) (hhi : x <= (r : Real)) : clip r x = x := by
  simp only [clip, max_eq_right hlo, min_eq_right hhi]

theorem clip_abs_le (r : Nat) (x : Real) : |clip r x| <= |x| := by
  by_cases hx : 0 <= x
  case pos =>
    have hn : -(r : Real) <= x := le_trans (neg_nonpos.mpr (Nat.cast_nonneg r)) hx
    simp only [clip, max_eq_right hn]
    have hm : 0 <= min (r : Real) x := le_min (by positivity) hx
    rw [abs_of_nonneg hm, abs_of_nonneg hx]
    exact min_le_right _ _
  case neg =>
    have hx' : x <= 0 := le_of_not_ge hx
    have hm : max (-(r : Real)) x <= (r : Real) := max_le
      ((neg_nonpos.mpr (Nat.cast_nonneg r)).trans (Nat.cast_nonneg r))
      (le_trans hx' (by positivity))
    simp only [clip, min_eq_right hm]
    have hmax : max (-(r : Real)) x <= 0 := max_le (neg_nonpos.mpr (Nat.cast_nonneg r)) hx'
    rw [abs_of_nonpos hmax, abs_of_nonpos hx']
    exact neg_le_neg (le_max_right _ _)

theorem quantizeScalar_error (r : Nat) (hr : 1 <= r) (x : Real) :
    |quantizeScalar r x - clip r x| <= 1 / (r : Real) := by
  have hpos : 0 < (r : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hlo := Int.floor_le ((r : Real) * clip r x)
  have hhi := Int.lt_floor_add_one ((r : Real) * clip r x)
  have herr : |(Int.floor ((r : Real) * clip r x) : Real) - (r : Real) * clip r x| <= 1 :=
    abs_le.mpr (And.intro (by linarith) (by linarith))
  have hid : quantizeScalar r x - clip r x =
      ((Int.floor ((r : Real) * clip r x) : Real) - (r : Real) * clip r x) / (r : Real) := by
    unfold quantizeScalar
    field_simp
  rw [hid, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right herr hpos.le

theorem quantizeScalar_abs_bound (r : Nat) (hr : 1 <= r) (x : Real) :
    |quantizeScalar r x| <= |x| + 1 := by
  have hr' : (1 : Real) <= (r : Real) := by exact_mod_cast hr
  have hrec : 1 / (r : Real) <= 1 := (div_le_one (by positivity)).mpr hr'
  calc
    |quantizeScalar r x| <= |quantizeScalar r x - clip r x| + |clip r x| :=
      by simpa only [sub_add_cancel] using abs_add_le (quantizeScalar r x - clip r x) (clip r x)
    _ <= 1 / (r : Real) + |x| :=
      add_le_add (quantizeScalar_error r hr x) (clip_abs_le r x)
    _ <= |x| + 1 := by linarith

theorem quantizeScalar_measurable (r : Nat) : Measurable (quantizeScalar r) := by
  unfold quantizeScalar clip
  fun_prop

theorem quantize_measurable {m : Nat} (r : Nat) : Measurable (@quantize m r) := by
  apply Measurable.of_eval
  intro j
  exact (quantizeScalar_measurable r).comp (measurable_pi_apply j)

theorem floor_quantization_bounds (r : Nat) (x : Real) :
    And (-(r : Int) * (r : Int) <= Int.floor ((r : Real) * clip r x))
      (Int.floor ((r : Real) * clip r x) <= (r : Int) * (r : Int)) := by
  constructor
  case left =>
    apply Int.le_floor.mpr
    push_cast
    simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left (neg_le_clip r x) (Nat.cast_nonneg r)
  case right =>
    apply Int.floor_le_iff.mpr
    push_cast
    have h := mul_le_mul_of_nonneg_left (clip_le r x) (show 0 <= (r : Real) by positivity)
    linarith

theorem quantizeScalar_finite_range (r : Nat) : (Set.range (quantizeScalar r)).Finite := by
  have hfinite : (Set.Icc (-(r : Int) * (r : Int)) ((r : Int) * (r : Int))).Finite :=
    Set.finite_Icc _ _
  apply (hfinite.image (fun k : Int => (k : Real) / (r : Real))).subset
  intro y hy
  cases hy with
  | intro x hx =>
    refine Exists.intro (Int.floor ((r : Real) * clip r x)) ?_
    exact And.intro (floor_quantization_bounds r x) hx

theorem quantize_finite_range {m : Nat} (r : Nat) : (Set.range (@quantize m r)).Finite := by
  apply (Set.Finite.pi (fun _ : Fin m => quantizeScalar_finite_range r)).subset
  intro y hy j hj
  cases hy with
  | intro w hw => exact Exists.intro (w j) (congrFun hw j)

theorem clip_eventually_eq (x : Real) :
    Filter.Eventually (fun r : Nat => clip r x = x) atTop := by
  have hbound : Filter.Eventually (fun r : Nat => |x| <= (r : Real)) atTop :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |x|)
  apply hbound.mono
  intro r hr
  apply clip_eq_self
  case hlo => linarith [neg_abs_le x]
  case hhi => exact (le_abs_self x).trans hr

theorem quantizeScalar_tendsto (x : Real) :
    Tendsto (fun r : Nat => quantizeScalar r x) atTop (nhds x) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg))
    (show Filter.Eventually (fun r : Nat => dist (quantizeScalar r x) x <= 1 / (r : Real)) atTop from ?_)
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [clip_eventually_eq x, eventually_ge_atTop 1] with r hclip hr
  simpa only [Real.dist_eq, hclip] using quantizeScalar_error r hr x

theorem quantize_tendsto {m : Nat} (w : Geometry.Point m) :
    Tendsto (fun r : Nat => quantize r w) atTop (nhds w) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact quantizeScalar_tendsto (w j)

theorem quantize_rowFactor_bound {m : Nat} (r : Nat) (hr : 1 <= r)
    (w : Geometry.Point m) :
    Moments.rowFactor (quantize r w) <= (m + 1 : Nat) * Moments.rowFactor w := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => quantizeScalar_abs_bound r hr (w j))
  have hnonneg : 0 <= Finset.sum Finset.univ (fun j => |w j|) :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (w j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  unfold Moments.rowFactor quantize
  push_cast
  nlinarith

def quantizePoint {m : Nat} (r : Nat) (z : Paper.Point (m + 1)) : Paper.Point (m + 1) :=
  Geometry.liftedPoint (quantize r (Paper.projectLast z)) (z (Fin.last m))

theorem quantizePoint_height {m : Nat} (r : Nat) (z : Paper.Point (m + 1)) :
    quantizePoint r z (Fin.last m) = z (Fin.last m) := by
  simp only [quantizePoint, Geometry.liftedPoint, Fin.lastCases_last]

theorem quantizePoint_project {m : Nat} (r : Nat) (z : Paper.Point (m + 1)) :
    Paper.projectLast (quantizePoint r z) = quantize r (Paper.projectLast z) := by
  funext j
  simp only [quantizePoint, Paper.projectLast, Geometry.liftedPoint, Fin.lastCases_castSucc]

theorem quantizePoint_measurable {m : Nat} (r : Nat) : Measurable (@quantizePoint m r) := by
  apply Measurable.of_eval
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [quantizePoint_height] using (measurable_pi_apply (Fin.last m))
  next j =>
    simpa only [quantizePoint, Geometry.liftedPoint, Fin.lastCases_castSucc,
      quantize, Paper.projectLast, Function.comp_def] using
      (quantizeScalar_measurable r).comp (measurable_pi_apply j.castSucc)

theorem quantizePoint_tendsto {m : Nat} (z : Paper.Point (m + 1)) :
    Tendsto (fun r : Nat => quantizePoint r z) atTop (nhds z) := by
  apply tendsto_pi_nhds.mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [quantizePoint_height] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => z (Fin.last m)) atTop (nhds (z (Fin.last m))))
  next j =>
    simpa only [quantizePoint, Geometry.liftedPoint, Fin.lastCases_castSucc,
      quantize, Paper.projectLast] using quantizeScalar_tendsto (z j.castSucc)

theorem quantizePoint_height_law {m : Nat} (r : Nat)
    (nu : Measure (Paper.Point (m + 1))) :
    (nu.map (quantizePoint r)).map (fun z => z (Fin.last m)) =
      nu.map (fun z => z (Fin.last m)) := by
  rw [Measure.map_map (measurable_pi_apply (Fin.last m)) (quantizePoint_measurable r)]
  congr 1
  funext z
  exact quantizePoint_height r z

theorem quantizePoint_gap {m : Nat} (r : Nat)
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu] :
    Paper.coordinateGap (nu.map (quantizePoint r)) (Fin.last m) =
      Paper.coordinateGap nu (Fin.last m) := by
  have : IsProbabilityMeasure (nu.map (quantizePoint r)) :=
    (Measure.isProbabilityMeasure_map_iff (quantizePoint_measurable r).aemeasurable).mpr inferInstance
  rw [<- Moments.height_law_pair_gap, quantizePoint_height_law, Moments.height_law_pair_gap]

theorem quantizePoint_finite_projection {m : Nat} (r : Nat) :
    (Set.range (fun z : Paper.Point (m + 1) => Paper.projectLast (quantizePoint r z))).Finite := by
  apply (quantize_finite_range (m := m) r).subset
  intro w hw
  cases hw with
  | intro z hz =>
    exact Exists.intro (Paper.projectLast z) ((quantizePoint_project r z).symm.trans hz)

theorem quantizePoint_firstMoments {m : Nat} (r : Nat) (hr : 1 <= r)
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.finiteCoordinateFirstMoments (nu.map (quantizePoint r)) := by
  intro j
  have hcoord : Measurable (fun z : Paper.Point (m + 1) => z j) := measurable_pi_apply j
  apply (integrable_map_measure
    ((continuous_abs.measurable.comp hcoord).aestronglyMeasurable)
    (quantizePoint_measurable r).aemeasurable).mpr
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [quantizePoint_height, Function.comp_def] using hfirst (Fin.last m)
  next j =>
    have hmeas : Measurable (fun z : Paper.Point (m + 1) =>
        |quantizeScalar r (z j.castSucc)|) :=
      continuous_abs.measurable.comp ((quantizeScalar_measurable r).comp
        (show Measurable (fun z : Paper.Point (m + 1) => z j.castSucc) from measurable_pi_apply j.castSucc))
    have h := ((hfirst j.castSucc).add (integrable_const (1 : Real))).mono_nonneg
      hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => abs_nonneg (quantizeScalar r (z j.castSucc))))
      (Filter.Eventually.of_forall (fun z => quantizeScalar_abs_bound r hr (z j.castSucc)))
    simpa only [quantizePoint, Geometry.liftedPoint, Fin.lastCases_castSucc,
      quantize, Paper.projectLast, Pi.add_apply, Function.comp_def] using h

set_option maxHeartbeats 800000 in
theorem quantized_cofactor_tendsto {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    Tendsto (fun r : Nat =>
      Geometry.cofactor (m := m)
        (fun j : Fin (m + 2) => quantize (m := m) r (Paper.projectLast (m := m) (z j))) i) atTop
      (nhds (Geometry.cofactor (m := m)
        (fun j : Fin (m + 2) => Paper.projectLast (m := m) (z j)) i)) := by
  have htuple : Tendsto
      (fun r : Nat => fun j : Fin (m + 2) => quantize (m := m) r (Paper.projectLast (m := m) (z j))) atTop
      (nhds (fun j : Fin (m + 2) => Paper.projectLast (m := m) (z j))) :=
    tendsto_pi_nhds.mpr (fun j => quantize_tendsto (Paper.projectLast (m := m) (z j)))
  have hc : Tendsto
      (fun w : Fin (m + 2) -> Geometry.Point m => Geometry.cofactor (m := m) w i)
      (nhds (fun j : Fin (m + 2) => Paper.projectLast (m := m) (z j)))
      (nhds (Geometry.cofactor (m := m) (fun j => Paper.projectLast (m := m) (z j)) i)) :=
    (Moments.cofactor_continuous (m := m) i).tendsto _
  exact hc.comp htuple

theorem quantized_radonMass_tendsto {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) :
    Tendsto (fun r : Nat =>
      Geometry.radonMass (fun j => quantize r (Paper.projectLast (z j)))) atTop
      (nhds (Geometry.radonMass (fun j => Paper.projectLast (z j)))) := by
  unfold Geometry.radonMass
  exact (tendsto_finsetSum Finset.univ (fun i _ => (quantized_cofactor_tendsto z i).abs)).const_mul _

theorem quantized_height_determinant_tendsto {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) :
    Tendsto (fun r : Nat =>
      |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i * z i (Fin.last m))|) atTop
      (nhds |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|) := by
  exact (tendsto_finsetSum Finset.univ
    (fun i _ => (quantized_cofactor_tendsto z i).mul_const (z i (Fin.last m)))).abs

theorem expected_quantized_height_determinant_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Tendsto (fun r : Nat => integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i * z i (Fin.last m))|)) atTop
      (nhds (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => |Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|))) := by
  let K : Real := (m + 1 : Nat)
  let bound := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    K ^ (m + 1) * Finset.sum Finset.univ (fun i => Moments.heightDominant z i)
  apply tendsto_integral_filter_of_dominated_convergence bound
  case hF_meas =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact (Thresholds.coefficient_height_sum_integrable
      (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
      (fun z i => z i (Fin.last m))
      (fun i => Moments.mapped_sampled_cofactor_measurable (quantize r) (quantize_measurable r) i)
      (fun i => (Moments.sampled_height_continuous i).measurable)
      (fun i => Moments.mapped_cofactor_height_integrable nu hfirst (quantize r)
        (quantize_measurable r) K (quantize_rowFactor_bound r hr) i)).aestronglyMeasurable
  case h_bound =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        Moments.mapped_determinant_abs_bound (quantize r) K (quantize_rowFactor_bound r hr) z)
  case bound_integrable =>
    exact (integrable_finsetSum Finset.univ
      (fun i _ => Moments.heightDominant_integrable nu hfirst i)).const_mul (K ^ (m + 1))
  case h_lim =>
    exact Filter.Eventually.of_forall quantized_height_determinant_tendsto

theorem expected_quantized_radonMass_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Tendsto (fun r : Nat => integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => Geometry.radonMass (fun j => quantize r (Paper.projectLast (z j))))) atTop
      (nhds (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))))) := by
  let K : Real := (m + 1 : Nat)
  let bound := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    (1 / 2 : Real) * K ^ (m + 1) * Finset.sum Finset.univ (fun i => Moments.cofactorDominant z i)
  apply tendsto_integral_filter_of_dominated_convergence bound
  case hF_meas =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact ((integrable_finsetSum Finset.univ
      (fun i _ => Moments.mapped_cofactor_abs_integrable nu hfirst (quantize r)
        (quantize_measurable r) K (quantize_rowFactor_bound r hr) i)).const_mul (1 / 2 : Real)).aestronglyMeasurable
  case h_bound =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (Geometry.radonMass_nonneg _)]
    unfold Geometry.radonMass bound
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Moments.mapped_cofactor_abs_bound (quantize r) K
        (quantize_rowFactor_bound r hr) z i)
    rw [<- Finset.mul_sum] at hs
    nlinarith
  case bound_integrable =>
    exact (integrable_finsetSum Finset.univ
      (fun i _ => Moments.cofactorDominant_integrable nu hfirst i)).const_mul
      ((1 / 2 : Real) * K ^ (m + 1))
  case h_lim =>
    exact Filter.Eventually.of_forall quantized_radonMass_tendsto

theorem quantized_thresholdCost_tendsto {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) :
    Tendsto (fun r : Nat => Thresholds.thresholdCost
      (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
      (fun i => z i (Fin.last m))) atTop
      (nhds (Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
        (fun i => z i (Fin.last m)))) := by
  have hzero (r : Nat) := Geometry.cofactor_sum_zero
    (fun j => quantize r (Paper.projectLast (z j)))
  have hzero' := Geometry.cofactor_sum_zero (fun j => Paper.projectLast (z j))
  have hlimit : Tendsto (fun r : Nat => Finset.sum Finset.univ (fun i =>
      |Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i -
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m)|))
      atTop (nhds 0) := by
    simpa only [sub_self, abs_zero, zero_mul, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ =>
        (((quantized_cofactor_tendsto z i).sub
          (show Tendsto (fun _ : Nat => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
            atTop (nhds (Geometry.cofactor (fun j => Paper.projectLast (z j)) i)) from tendsto_const_nhds)).abs).mul_const
          |z i (Fin.last m)|)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg))
    (Filter.Eventually.of_forall (fun r => ?_)) hlimit
  simpa only [Real.dist_eq] using Thresholds.thresholdCost_lipschitz_coefficients
    (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
    (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun i => z i (Fin.last m)) (hzero r) hzero'

theorem expected_quantized_thresholdCost_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Tendsto (fun r : Nat => integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
        (fun i => z i (Fin.last m)))) atTop
      (nhds (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Thresholds.thresholdCost
          (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
          (fun i => z i (Fin.last m))))) := by
  let K : Real := (m + 1 : Nat)
  let bound := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    K ^ (m + 1) * Finset.sum Finset.univ (fun i => Moments.heightDominant z i)
  apply tendsto_integral_filter_of_dominated_convergence bound
  case hF_meas =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact (Thresholds.joint_threshold_integrable
      (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
      (fun z i => z i (Fin.last m))
      (fun z => Geometry.cofactor_sum_zero (fun j => quantize r (Paper.projectLast (z j))))
      (fun i => Moments.mapped_sampled_cofactor_measurable (quantize r) (quantize_measurable r) i)
      (fun i => (Moments.sampled_height_continuous i).measurable)
      (fun i => Moments.mapped_cofactor_height_integrable nu hfirst (quantize r)
        (quantize_measurable r) K (quantize_rowFactor_bound r hr) i)).integral_prod_left.aestronglyMeasurable
  case h_bound =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    apply Filter.Eventually.of_forall
    intro z
    have hnonneg : 0 <= Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
        (fun i => z i (Fin.last m)) := integral_nonneg (fun _ => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    apply le_trans (Thresholds.threshold_bound_right _ _
      (Geometry.cofactor_sum_zero (fun j => quantize r (Paper.projectLast (z j)))))
    unfold bound
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact Moments.mapped_cofactor_height_bound (quantize r) K (quantize_rowFactor_bound r hr) z i
  case bound_integrable =>
    exact (integrable_finsetSum Finset.univ
      (fun i _ => Moments.heightDominant_integrable nu hfirst i)).const_mul (K ^ (m + 1))
  case h_lim =>
    exact Filter.Eventually.of_forall quantized_thresholdCost_tendsto

/- This is exactly the limit-passing implication used in Appendix B. Its
finite-projection premise is explicit; it does not assert that premise. -/
theorem height_gate_of_quantized_gates {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hfinite : forall r : Nat, 1 <= r ->
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => |Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i * z i (Fin.last m))|) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => quantize r (Paper.projectLast (z j)))) *
          Paper.coordinateGap nu (Fin.last m)) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) *
          Paper.coordinateGap nu (Fin.last m) := by
  apply le_of_tendsto_of_tendsto
    (expected_quantized_height_determinant_tendsto nu hfirst)
    ((expected_quantized_radonMass_tendsto nu hfirst).mul_const (Paper.coordinateGap nu (Fin.last m)))
  exact (eventually_ge_atTop 1).mono (fun r hr => hfinite r hr)

theorem threshold_gate_of_quantized_threshold_gates {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hfinite : forall r : Nat, 1 <= r ->
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Thresholds.thresholdCost
          (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
          (fun i => z i (Fin.last m))) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => quantize r (Paper.projectLast (z j)))) *
          Paper.coordinateGap nu (Fin.last m)) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
        (fun i => z i (Fin.last m))) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) *
          Paper.coordinateGap nu (Fin.last m) := by
  apply le_of_tendsto_of_tendsto
    (expected_quantized_thresholdCost_tendsto nu hfirst)
    ((expected_quantized_radonMass_tendsto nu hfirst).mul_const (Paper.coordinateGap nu (Fin.last m)))
  exact (eventually_ge_atTop 1).mono (fun r hr => hfinite r hr)

theorem height_gate_of_quantized_threshold_gates {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hfinite : forall r : Nat, 1 <= r ->
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Thresholds.thresholdCost
          (fun i => Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i)
          (fun i => z i (Fin.last m))) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => quantize r (Paper.projectLast (z j)))) *
          Paper.coordinateGap nu (Fin.last m)) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) *
          Paper.coordinateGap nu (Fin.last m) := by
  apply le_trans (integral_mono (Moments.sampled_determinant_integrable nu hfirst)
    (Moments.sampled_threshold_integrable nu hfirst).integral_prod_left
    (fun z => Thresholds.threshold_bound_left _ _
      (Geometry.cofactor_sum_zero (fun j => Paper.projectLast (z j)))))
  exact threshold_gate_of_quantized_threshold_gates nu hfirst hfinite

theorem quantized_cofactor_domination {m : Nat} (r : Nat) (hr : 1 <= r)
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    |Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i| +
      |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| <=
      (((m + 1 : Nat) : Real) ^ (m + 1) + 1) * Moments.cofactorDominant z i := by
  have h := add_le_add (Moments.mapped_cofactor_abs_bound (quantize r)
    ((m + 1 : Nat) : Real) (quantize_rowFactor_bound r hr) z i) (Moments.cofactor_bound z i)
  calc
    _ <= ((m + 1 : Nat) : Real) ^ (m + 1) * Moments.cofactorDominant z i +
      Moments.cofactorDominant z i := h
    _ = _ := by ring

theorem affineDet_continuous (d : Nat) :
    Continuous (Geometry.affineDet : (Fin (d + 1) -> Paper.Point d) -> Real) := by
  unfold Geometry.affineDet
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin (d + 1) -> Paper.Point d => (1 : Real)))
  next j =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_castSucc, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i))

theorem simplexVolume_eq_affineDet_div_factorial {d : Nat}
    (z : Fin (d + 1) -> Paper.Point d) :
    Paper.simplexVolume z = |Geometry.affineDet z| / (Nat.factorial d : Real) := by
  have hfactor := Geometry.simplex_volume_factorial z
  have hpos : (0 : Real) < (Nat.factorial d : Real) := by exact_mod_cast Nat.factorial_pos d
  change Geometry.simplexVolume z = _
  apply (eq_div_iff hpos.ne').mpr
  nlinarith

theorem simplexVolume_continuous (d : Nat) :
    Continuous (@Paper.simplexVolume d) := by
  have heq : @Paper.simplexVolume d =
      (fun z => |Geometry.affineDet z| / (Nat.factorial d : Real)) := by
    funext z
    exact simplexVolume_eq_affineDet_div_factorial z
  rw [heq]
  exact (affineDet_continuous d).abs.div_const _

theorem rowFactor_integrable {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z => Moments.rowFactor z) nu := by
  exact (integrable_const (1 : Real)).add
    (integrable_finsetSum Finset.univ (fun j _ => hfirst j))

theorem expectedSimplexVolume_map {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (Q : Paper.Point d -> Paper.Point d) (hQ : Measurable Q) :
    Paper.expectedSimplexVolume (nu.map Q) =
      integral (Measure.pi (fun _ : Fin (d + 1) => nu))
        (fun z => Paper.simplexVolume (fun i => Q (z i))) := by
  exact Moments.iid_integral_map nu (d + 1) Q hQ
    (fun z => Paper.simplexVolume z) (simplexVolume_continuous d).measurable

/- General approximation interface with actual Lebesgue simplex volumes.
Its domination witness is the row-by-row permutation bound already proved
in Moments. No mixed coordinate moments within one sample are assumed. -/
theorem expectedSimplexVolume_map_tendsto {d : Nat}
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (Q : Nat -> Paper.Point d -> Paper.Point d)
    (hQmeas : forall r, Measurable (Q r)) (K : Real)
    (hQbound : Filter.Eventually (fun r => forall z,
      Moments.rowFactor (Q r z) <= K * Moments.rowFactor z) atTop)
    (hQlim : forall z, Tendsto (fun r => Q r z) atTop (nhds z)) :
    Tendsto (fun r => Paper.expectedSimplexVolume (nu.map (Q r))) atTop
      (nhds (Paper.expectedSimplexVolume nu)) := by
  simp_rw [expectedSimplexVolume_map nu _ (hQmeas _)]
  let bound := fun z : Fin (d + 1) -> Paper.Point d =>
    (Nat.factorial (d + 1) : Real) / (Nat.factorial d : Real) *
      K ^ (d + 1) * Finset.prod Finset.univ (fun i => Moments.rowFactor (z i))
  apply tendsto_integral_filter_of_dominated_convergence bound
  case hF_meas =>
    apply Filter.Eventually.of_forall
    intro r
    have htuple : Measurable (fun z : Fin (d + 1) -> Paper.Point d => fun i => Q r (z i)) :=
      Measurable.of_eval (fun i => (hQmeas r).comp (measurable_pi_apply i))
    exact ((simplexVolume_continuous d).measurable.comp htuple).aestronglyMeasurable
  case h_bound =>
    apply hQbound.mono
    intro r hr
    apply Filter.Eventually.of_forall
    intro z
    have hv : 0 <= Paper.simplexVolume (fun i => Q r (z i)) := Geometry.simplexVolume_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hv,
      simplexVolume_eq_affineDet_div_factorial]
    have hdet := Moments.affineDet_mapped_bound (Q r) K hr z
    have hdiv := div_le_div_of_nonneg_right hdet (show (0 : Real) <= (Nat.factorial d : Real) by positivity)
    apply le_trans hdiv
    unfold bound
    apply le_of_eq
    ring
  case bound_integrable =>
    exact (Integrable.fintype_prod (fun _ : Fin (d + 1) => rowFactor_integrable nu hfirst)).const_mul
      ((Nat.factorial (d + 1) : Real) / (Nat.factorial d : Real) * K ^ (d + 1))
  case h_lim =>
    apply Filter.Eventually.of_forall
    intro z
    have htuple : Tendsto (fun r => fun i : Fin (d + 1) => Q r (z i)) atTop (nhds z) :=
      tendsto_pi_nhds.mpr (fun i => hQlim (z i))
    exact (simplexVolume_continuous d).continuousAt.tendsto.comp htuple

theorem quantizePoint_abs_bound {m : Nat} (r : Nat) (hr : 1 <= r)
    (z : Paper.Point (m + 1)) (j : Fin (m + 1)) :
    |quantizePoint r z j| <= |z j| + 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    rw [quantizePoint_height]
    linarith
  next j =>
    simpa only [quantizePoint, Geometry.liftedPoint, Fin.lastCases_castSucc,
      quantize, Paper.projectLast] using quantizeScalar_abs_bound r hr (z j.castSucc)

theorem quantizePoint_rowFactor_bound {m : Nat} (r : Nat) (hr : 1 <= r)
    (z : Paper.Point (m + 1)) :
    Moments.rowFactor (quantizePoint r z) <= (m + 2 : Nat) * Moments.rowFactor z := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => quantizePoint_abs_bound r hr z j)
  have hnonneg : 0 <= Finset.sum Finset.univ (fun j => |z j|) :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (z j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  unfold Moments.rowFactor
  push_cast
  push_cast at hsum
  nlinarith

theorem expected_quantized_simplexVolume_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Tendsto (fun r : Nat => Paper.expectedSimplexVolume (nu.map (quantizePoint r))) atTop
      (nhds (Paper.expectedSimplexVolume nu)) := by
  apply expectedSimplexVolume_map_tendsto nu hfirst quantizePoint
    (fun r => quantizePoint_measurable r) ((m + 2 : Nat) : Real)
  case hQbound =>
    exact (eventually_ge_atTop 1).mono (fun r hr z => quantizePoint_rowFactor_bound r hr z)
  case hQlim =>
    exact quantizePoint_tendsto

theorem projected_firstMoments {m : Nat}
    (nu : Measure (Paper.Point (m + 1)))
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.finiteCoordinateFirstMoments (nu.map Paper.projectLast) := by
  intro j
  have hcoord : Measurable (fun w : Paper.Point m => w j) := measurable_pi_apply j
  apply (integrable_map_measure (continuous_abs.measurable.comp hcoord).aestronglyMeasurable
    Moments.projectLast_continuous.measurable.aemeasurable).mpr
  simpa only [Paper.projectLast, Function.comp_def] using hfirst j.castSucc

theorem quantizePoint_projected_law {m : Nat} (r : Nat)
    (nu : Measure (Paper.Point (m + 1))) :
    (nu.map (quantizePoint r)).map Paper.projectLast =
      (nu.map Paper.projectLast).map (quantize r) := by
  rw [Measure.map_map Moments.projectLast_continuous.measurable (quantizePoint_measurable r),
    Measure.map_map (quantize_measurable r) Moments.projectLast_continuous.measurable]
  congr 1
  funext z
  exact quantizePoint_project r z

theorem expected_quantized_projected_simplexVolume_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Tendsto (fun r : Nat => Paper.expectedSimplexVolume
      ((nu.map (quantizePoint r)).map Paper.projectLast)) atTop
      (nhds (Paper.expectedSimplexVolume (nu.map Paper.projectLast))) := by
  have : IsProbabilityMeasure (nu.map (Paper.projectLast : Paper.Point (m + 1) -> Paper.Point m)) :=
    (Measure.isProbabilityMeasure_map_iff Moments.projectLast_continuous.measurable.aemeasurable).mpr inferInstance
  simp_rw [quantizePoint_projected_law]
  apply expectedSimplexVolume_map_tendsto (nu.map Paper.projectLast)
    (projected_firstMoments nu hfirst) quantize (fun r => quantize_measurable r)
    ((m + 1 : Nat) : Real)
  case hQbound =>
    exact (eventually_ge_atTop 1).mono (fun r hr w => quantize_rowFactor_bound r hr w)
  case hQlim =>
    exact quantize_tendsto

theorem quantized_threshold_level_tendsto {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (t : Real) :
    Tendsto (fun r : Nat => |Finset.sum Finset.univ (fun i =>
      Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i *
        Thresholds.threshold (z i (Fin.last m)) t)|) atTop
      (nhds |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
          Thresholds.threshold (z i (Fin.last m)) t)|) := by
  exact (tendsto_finsetSum Finset.univ (fun i _ =>
    (quantized_cofactor_tendsto z i).mul_const (Thresholds.threshold (z i (Fin.last m)) t))).abs

theorem expected_quantized_threshold_level_tendsto {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (t : Real) :
    Tendsto (fun r : Nat => integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i *
          Thresholds.threshold (z i (Fin.last m)) t)|)) atTop
      (nhds (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => |Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
            Thresholds.threshold (z i (Fin.last m)) t)|))) := by
  let K : Real := (m + 1 : Nat)
  let bound := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    K ^ (m + 1) * Finset.sum Finset.univ (fun i => Moments.cofactorDominant z i)
  apply tendsto_integral_filter_of_dominated_convergence bound
  case hF_meas =>
    apply Filter.Eventually.of_forall
    intro r
    have hm : Measurable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
        Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i *
            Thresholds.threshold (z i (Fin.last m)) t)) :=
      Finset.measurable_sum Finset.univ (fun i _ =>
        (Moments.mapped_sampled_cofactor_measurable (quantize r) (quantize_measurable r) i).mul
          (Thresholds.threshold_joint_measurable
            (fun z : Fin (m + 2) -> Paper.Point (m + 1) => z i (Fin.last m))
            (fun _ : Fin (m + 2) -> Paper.Point (m + 1) => t)
            (Moments.sampled_height_continuous i).measurable measurable_const))
    exact (continuous_abs.measurable.comp hm).aestronglyMeasurable
  case h_bound =>
    filter_upwards [eventually_ge_atTop 1] with r hr
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i *
            Thresholds.threshold (z i (Fin.last m)) t)| <=
        Finset.sum Finset.univ (fun i =>
          |Geometry.cofactor (fun j => quantize r (Paper.projectLast (z j))) i *
            Thresholds.threshold (z i (Fin.last m)) t|) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun i => K ^ (m + 1) * Moments.cofactorDominant z i) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hth : |Thresholds.threshold (z i (Fin.last m)) t| <= 1 := by
          unfold Thresholds.threshold
          split_ifs <;> norm_num
        apply le_trans (mul_le_mul_of_nonneg_left hth (abs_nonneg _))
        simpa only [mul_one] using Moments.mapped_cofactor_abs_bound (quantize r) K
          (quantize_rowFactor_bound r hr) z i
      _ = bound z := by unfold bound; rw [Finset.mul_sum]
  case bound_integrable =>
    exact (integrable_finsetSum Finset.univ
      (fun i _ => Moments.cofactorDominant_integrable nu hfirst i)).const_mul (K ^ (m + 1))
  case h_lim =>
    exact Filter.Eventually.of_forall (fun z => quantized_threshold_level_tendsto z t)

/- This additional bridge is derived from the finite-support theorem and the
checked approximation. It matches the endpoint's universal strict-threshold
Bernoulli claim with no unresolved geometric or probabilistic premise. -/
theorem global_levelwise_bernoulli_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (t : Real) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
          Thresholds.threshold (z i (Fin.last m)) t)|) <=
    2 * nu.real {z | t < z (Fin.last m)} * (1 - nu.real {z | t < z (Fin.last m)}) *
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) := by
  apply le_of_tendsto_of_tendsto (expected_quantized_threshold_level_tendsto nu hfirst t)
    ((expected_quantized_radonMass_tendsto nu hfirst).const_mul
      (2 * nu.real {z | t < z (Fin.last m)} * (1 - nu.real {z | t < z (Fin.last m)})))
  apply Filter.Eventually.of_forall
  intro r
  have hfinite : (Set.range (fun z : Paper.Point (m + 1) => quantize r (Paper.projectLast z))).Finite := by
    simpa only [quantizePoint_project] using quantizePoint_finite_projection (m := m) r
  exact FiniteThreshold.finite_projection_levelwise_gate nu
    (fun z => quantize r (Paper.projectLast z))
    ((quantize_measurable r).comp Moments.projectLast_continuous.measurable) hfinite
    (fun z => z (Fin.last m)) (measurable_pi_apply (Fin.last m)) t

/- The paper's complete Appendix B C* gate, with its finite-projection
premise now discharged by the checked finite-support Bernoulli theorem. -/
theorem global_thresholdCost_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
        (fun i => z i (Fin.last m))) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) *
          Paper.coordinateGap nu (Fin.last m) := by
  apply threshold_gate_of_quantized_threshold_gates nu hfirst
  intro r hr
  exact FiniteThreshold.finite_projection_thresholdCost_gate nu hfirst (quantize r)
    (quantize_measurable r) (quantize_finite_range r) ((m + 1 : Nat) : Real)
    (quantize_rowFactor_bound r hr)

theorem global_height_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j))) *
          Paper.coordinateGap nu (Fin.last m) := by
  apply height_gate_of_quantized_threshold_gates nu hfirst
  intro r hr
  exact FiniteThreshold.finite_projection_thresholdCost_gate nu hfirst (quantize r)
    (quantize_measurable r) (quantize_finite_range r) ((m + 1 : Nat) : Real)
    (quantize_rowFactor_bound r hr)

end Hypercube.Approximation
