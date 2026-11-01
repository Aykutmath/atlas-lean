import Section_10_Zonoid.Hypercube.FiniteAtomic
import Section_10_Zonoid.Hypercube.Moments
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/- A finite projected support together with its binary threshold label is an
ordinary finite probability law. The independent sample law is transferred
explicitly through this map; no conditional-independence premise is hidden. -/

noncomputable section

namespace Hypercube.FiniteThreshold

open MeasureTheory

theorem finite_projection_labels {Space : Type*} [MeasurableSpace Space] {m : Nat}
    (W : Space -> Geometry.Point m) (hW : Measurable W)
    (hfinite : Set.Finite (Set.range W)) :
    Exists (fun N : Nat => Exists (fun label : Space -> Fin N =>
      Exists (fun points : Fin N -> Geometry.Point m =>
        And (Measurable label) (forall z, points (label z) = W z)))) := by
  classical
  let : Fintype (Set.range W) := hfinite.fintype
  let e := Fintype.equivFin (Set.range W)
  let label : Space -> Fin (Fintype.card (Set.range W)) :=
    fun z => e (Subtype.mk (W z) (Exists.intro z rfl))
  let points : Fin (Fintype.card (Set.range W)) -> Geometry.Point m :=
    fun i => (e.symm i).val
  refine Exists.intro (Fintype.card (Set.range W))
    (Exists.intro label (Exists.intro points (And.intro ?_ ?_)))
  next =>
    exact (measurable_of_countable e).comp hW.subtype_mk
  next =>
    intro z
    simp [label, points]

def thresholdBit {Space : Type*} (T : Space -> Real) (t : Real) (z : Space) : Fin 2 :=
  if t < T z then 1 else 0

theorem thresholdBit_measurable {Space : Type*} [MeasurableSpace Space]
    (T : Space -> Real) (hT : Measurable T) (t : Real) :
    Measurable (thresholdBit T t) := by
  unfold thresholdBit
  exact Measurable.ite (measurableSet_lt measurable_const hT) measurable_const measurable_const

theorem thresholdBit_real {Space : Type*} (T : Space -> Real) (t : Real) (z : Space) :
    ((thresholdBit T t z).val : Real) = Thresholds.threshold (T z) t := by
  unfold thresholdBit Thresholds.threshold
  split_ifs <;> norm_num

theorem finite_labels_levelwise_gate {Space : Type*} [MeasurableSpace Space] {N m : Nat}
    (P : Measure Space) [IsProbabilityMeasure P]
    (label : Space -> Fin N) (hlabel : Measurable label)
    (points : Fin N -> Geometry.Point m) (T : Space -> Real) (hT : Measurable T)
    (t : Real) :
    integral (Measure.pi (fun _ : Fin (m + 2) => P))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => points (label (z j))) i *
          Thresholds.threshold (T (z i)) t)|) <=
      2 * P.real {z | t < T z} * (1 - P.real {z | t < T z}) *
        integral (Measure.pi (fun _ : Fin (m + 2) => P))
          (fun z => Geometry.radonMass (fun j => points (label (z j)))) := by
  classical
  let joint : Space -> Fin (N * 2) :=
    fun z => finProdFinEquiv (label z, thresholdBit T t z)
  have hjoint : Measurable joint :=
    (measurable_of_finite finProdFinEquiv).comp
      (hlabel.prodMk (thresholdBit_measurable T hT t))
  let W : Fin (N * 2) -> Geometry.Point m := fun i => points (finProdFinEquiv.symm i).1
  let X : Fin (N * 2) -> Real := fun i => ((finProdFinEquiv.symm i).2.val : Real)
  have hWX (z : Space) : W (joint z) = points (label z) := by
    change points (finProdFinEquiv.symm
      (finProdFinEquiv (label z, thresholdBit T t z))).1 = points (label z)
    rw [Equiv.symm_apply_apply]
  have hXX (z : Space) : X (joint z) = Thresholds.threshold (T z) t := by
    change ((finProdFinEquiv.symm
      (finProdFinEquiv (label z, thresholdBit T t z))).2.val : Real) = _
    rw [Equiv.symm_apply_apply]
    exact thresholdBit_real T t z
  have hbinary (i : Fin (N * 2)) : Or (X i = 0) (X i = 1) := by
    let b : Fin 2 := (finProdFinEquiv.symm i).2
    change Or ((b.val : Real) = 0) ((b.val : Real) = 1)
    have hb : Or (b.val = 0) (b.val = 1) := by omega
    rcases hb with h | h
    next => exact Or.inl (by rw [h]; norm_num)
    next => exact Or.inr (by rw [h]; norm_num)
  have : IsProbabilityMeasure (P.map joint) :=
    (Measure.isProbabilityMeasure_map_iff hjoint.aemeasurable).mpr inferInstance
  have hp : integral (P.map joint) X = P.real {z | t < T z} := by
    rw [integral_map hjoint.aemeasurable (measurable_of_finite X).aestronglyMeasurable]
    simp_rw [hXX]
    have heq : (fun z => Thresholds.threshold (T z) t) =
        ({z | t < T z} : Set Space).indicator (fun _ => (1 : Real)) := by
      funext z
      simp [Thresholds.threshold, Set.indicator]
    rw [heq, integral_indicator_const _ (measurableSet_lt measurable_const hT)]
    simp
  have hgate := FiniteAtomic.finite_probability_binary_gate (P.map joint) X W hbinary
  dsimp only at hgate
  rw [hp,
    Moments.iid_integral_map P (m + 2) joint hjoint _ (measurable_of_finite _),
    Moments.iid_integral_map P (m + 2) joint hjoint _ (measurable_of_finite _)] at hgate
  simpa only [hWX, hXX] using hgate

theorem finite_projection_levelwise_gate {Space : Type*} [MeasurableSpace Space] {m : Nat}
    (P : Measure Space) [IsProbabilityMeasure P]
    (W : Space -> Geometry.Point m) (hW : Measurable W)
    (hfinite : Set.Finite (Set.range W)) (T : Space -> Real) (hT : Measurable T)
    (t : Real) :
    integral (Measure.pi (fun _ : Fin (m + 2) => P))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => W (z j)) i * Thresholds.threshold (T (z i)) t)|) <=
      2 * P.real {z | t < T z} * (1 - P.real {z | t < T z}) *
        integral (Measure.pi (fun _ : Fin (m + 2) => P))
          (fun z => Geometry.radonMass (fun j => W (z j))) := by
  cases finite_projection_labels W hW hfinite with
  | intro N hN =>
      cases hN with
      | intro label hl =>
          cases hl with
          | intro points hp =>
              have hgate := finite_labels_levelwise_gate P label hp.1 points T hT t
              simpa only [hp.2] using hgate

/-- Expected optimal threshold cost for a finite projected approximation.
The row-factor bound is used only for product-moment integrability. -/
theorem finite_projection_thresholdCost_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (Q : Geometry.Point m -> Geometry.Point m) (hQmeas : Measurable Q)
    (hfinite : Set.Finite (Set.range Q))
    (K : Real) (hQ : forall w, Moments.rowFactor (Q w) <= K * Moments.rowFactor w) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => Thresholds.thresholdCost
        (fun i => Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i)
        (fun i => z i (Fin.last m))) <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => Geometry.radonMass (fun j => Q (Paper.projectLast (z j)))) *
          Paper.coordinateGap nu (Fin.last m) := by
  let c := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    fun i => Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i
  let height := fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    fun i => z i (Fin.last m)
  let P := Measure.pi (fun _ : Fin (m + 2) => nu)
  let mu := nu.map (fun z => z (Fin.last m))
  let L := integral P (fun z => Geometry.radonMass (fun j => Q (Paper.projectLast (z j))))
  have hT : Measurable (fun z : Paper.Point (m + 1) => z (Fin.last m)) :=
    (continuous_apply (Fin.last m)).measurable
  have : IsProbabilityMeasure mu :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hzero : forall z, Finset.sum Finset.univ (c z) = 0 :=
    fun z => Geometry.cofactor_sum_zero (fun j => Q (Paper.projectLast (z j)))
  have hF := Thresholds.joint_threshold_integrable P c height hzero
    (fun i => Moments.mapped_sampled_cofactor_measurable Q hQmeas i)
    (fun i => (Moments.sampled_height_continuous i).measurable)
    (fun i => Moments.mapped_cofactor_height_integrable nu hfirst Q hQmeas K hQ i)
  have hW : Measurable (fun z : Paper.Point (m + 1) => Q (Paper.projectLast z)) :=
    hQmeas.comp Moments.projectLast_continuous.measurable
  have hWfinite : Set.Finite (Set.range (fun z : Paper.Point (m + 1) => Q (Paper.projectLast z))) :=
    hfinite.subset (Set.range_comp_subset_range Paper.projectLast Q)
  have hlevel (t : Real) : integral P (fun z =>
      |Finset.sum Finset.univ (fun i => c z i * Thresholds.threshold (height z i) t)|) <=
      2 * Thresholds.tailProbability mu t * (1 - Thresholds.tailProbability mu t) * L := by
    have hg := finite_projection_levelwise_gate nu
      (fun z => Q (Paper.projectLast z)) hW hWfinite (fun z => z (Fin.last m)) hT t
    simpa only [c, height, P, L, mu,
      Thresholds.tailProbability_map nu (fun z => z (Fin.last m)) hT]
      using hg
  have hg := Thresholds.lift_thresholdCost_levelwise_gate P mu c height L
    (Moments.height_law_firstMoment nu hfirst) hF hlevel
  rw [Moments.height_law_pair_gap nu] at hg
  exact hg

end Hypercube.FiniteThreshold
