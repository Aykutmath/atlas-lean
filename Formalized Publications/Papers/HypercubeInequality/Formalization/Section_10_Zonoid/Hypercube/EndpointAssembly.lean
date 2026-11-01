import Section_10_Zonoid.Hypercube.Statements
import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Section_10_Zonoid.Hypercube.Sampling
import Mathlib.Algebra.BigOperators.Fin

/-
Paper endpoint assembly. Each conditional theorem names its mathematical
premises in its signature. In particular, a sampled height gate is not
silently promoted to an unconditional one-step theorem.
-/

noncomputable section

namespace Hypercube.EndpointAssembly

open MeasureTheory

def sampledHeightObjective {m : Nat} (nu : Measure (Paper.Point (m + 1))) : Real :=
  integral (Measure.pi (fun _ : Fin (m + 2) => nu))
    (fun z => |Finset.sum Finset.univ (fun i =>
      Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|)

def expectedRadonMass {m : Nat} (nu : Measure (Paper.Point (m + 1))) : Real :=
  integral (Measure.pi (fun _ : Fin (m + 2) => nu))
    (fun z => Geometry.radonMass (fun j => Paper.projectLast (z j)))

/-- The source threshold cost C_* for one sampled configuration. -/
def sampledThresholdCost {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) : Real :=
  Thresholds.thresholdCost (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun i => z i (Fin.last m))

/-- The source Bernoulli gate applied to the strict height threshold at every level. -/
def levelwiseBernoulliClaim {m : Nat} (nu : Measure (Paper.Point (m + 1))) : Prop :=
  forall t, integral (Measure.pi (fun _ : Fin (m + 2) => nu))
    (fun z => |Finset.sum Finset.univ (fun i =>
      Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
        Thresholds.threshold (z i (Fin.last m)) t)|) <=
    2 * nu.real {z | t < z (Fin.last m)} *
      (1 - nu.real {z | t < z (Fin.last m)}) * expectedRadonMass nu

theorem affineDet_continuous {m : Nat} :
    Continuous (fun z : Fin (m + 1) -> Geometry.Point m => Geometry.affineDet z) := by
  unfold Geometry.affineDet
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin (m + 1) -> Geometry.Point m => (1 : Real)))
  next j =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_castSucc, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i))

/-- Omission of one iid coordinate preserves the law of all remaining samples. -/
theorem iid_omit_map {X : Type*} [MeasurableSpace X]
    (nu : Measure X) [IsProbabilityMeasure nu] (n : Nat) (i : Fin (n + 1)) :
    (Measure.pi (fun _ : Fin (n + 1) => nu)).map (fun z j => z (i.succAbove j)) =
      Measure.pi (fun _ : Fin n => nu) := by
  have hs : MeasurePreserving (Prod.snd : Prod X (Fin n -> X) -> (Fin n -> X))
      (nu.prod (Measure.pi (fun _ : Fin n => nu))) (Measure.pi (fun _ : Fin n => nu)) :=
    measurePreserving_snd
  have ho := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => nu) i
  exact (hs.comp ho).map_eq

theorem iid_omit_integral {X : Type*} [MeasurableSpace X]
    (nu : Measure X) [IsProbabilityMeasure nu] (n : Nat) (i : Fin (n + 1))
    (F : (Fin n -> X) -> Real) (hF : Measurable F) :
    integral (Measure.pi (fun _ : Fin n => nu)) F =
      integral (Measure.pi (fun _ : Fin (n + 1) => nu))
        (fun z => F (fun j => z (i.succAbove j))) := by
  have homeas : Measurable (fun z : Fin (n + 1) -> X => fun j => z (i.succAbove j)) :=
    Measurable.of_eval (fun j => measurable_pi_apply _)
  rw [<- iid_omit_map nu n i]
  exact integral_map homeas.aemeasurable hF.aestronglyMeasurable

theorem sampled_cofactor_integral {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu] (i : Fin (m + 2)) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|) =
      integral (Measure.pi (fun _ : Fin (m + 1) => nu.map Paper.projectLast))
        (fun w => |Geometry.affineDet w|) := by
  have hdet : Measurable (fun w : Fin (m + 1) -> Geometry.Point m => |Geometry.affineDet w|) :=
    (continuous_abs.comp affineDet_continuous).measurable
  have hproject : Measurable (fun z : Fin (m + 1) -> Paper.Point (m + 1) =>
      |Geometry.affineDet (fun j => Paper.projectLast (z j))|) :=
    hdet.comp (Measurable.of_eval (fun j =>
      Moments.projectLast_continuous.measurable.comp (measurable_pi_apply j)))
  rw [Moments.iid_integral_map nu (m + 1) Paper.projectLast
    Moments.projectLast_continuous.measurable _ hdet,
    iid_omit_integral nu (m + 1) i _ hproject]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    simp [Geometry.cofactor, abs_mul, abs_pow])

/-- Source R': the only remaining premise is the projected volume/determinant identity. -/
theorem radon_normalization_of_projected_volume {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hprojected : (m.factorial : Real) *
      Paper.expectedSimplexVolume (nu.map Paper.projectLast) =
        integral (Measure.pi (fun _ : Fin (m + 1) => nu.map Paper.projectLast))
          (fun w => |Geometry.affineDet w|)) :
    expectedRadonMass nu =
      ((m + 2 : Nat) : Real) / 2 * (m.factorial : Real) *
        Paper.expectedSimplexVolume (nu.map Paper.projectLast) := by
  unfold expectedRadonMass Geometry.radonMass
  rw [integral_const_mul, integral_finsetSum]
  next =>
    simp_rw [sampled_cofactor_integral nu]
    rw [<- hprojected]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  next =>
    intro i _
    exact Moments.sampled_cofactor_abs_integrable nu hfirst i

theorem coordinateGap_nonneg {d : Nat} (nu : Measure (Paper.Point d)) (j : Fin d) :
    0 <= Paper.coordinateGap nu j := by
  unfold Paper.coordinateGap
  exact integral_nonneg (fun z => abs_nonneg _)

theorem projection_probability {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (nu.map Paper.projectLast) :=
  (Measure.isProbabilityMeasure_map_iff Moments.projectLast_continuous.measurable.aemeasurable).mpr
    inferInstance

theorem projection_first_moments {m : Nat}
    (nu : Measure (Paper.Point (m + 1)))
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.finiteCoordinateFirstMoments (nu.map Paper.projectLast) := by
  intro j
  have hcoord : Measurable (fun z : Paper.Point m => |z j|) :=
    continuous_abs.measurable.comp (continuous_apply j).measurable
  apply (integrable_map_measure hcoord.aestronglyMeasurable
    Moments.projectLast_continuous.measurable.aemeasurable).mpr
  exact hfirst j.castSucc

theorem coordinateGap_projection {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu] (j : Fin m) :
    Paper.coordinateGap (nu.map Paper.projectLast) j = Paper.coordinateGap nu j.castSucc := by
  have hproj : Measurable (Paper.projectLast : Paper.Point (m + 1) -> Paper.Point m) :=
    Moments.projectLast_continuous.measurable
  have hleft : Measurable (fun zz : Prod (Paper.Point m) (Paper.Point m) => zz.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hright : Measurable (fun zz : Prod (Paper.Point m) (Paper.Point m) => zz.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hgap : Measurable (fun zz : Prod (Paper.Point m) (Paper.Point m) => |zz.1 j - zz.2 j|) :=
    continuous_abs.measurable.comp (hleft.sub hright)
  unfold Paper.coordinateGap
  rw [Measure.map_prod_map nu nu hproj hproj,
    integral_map (hproj.prodMap hproj).aemeasurable hgap.aestronglyMeasurable]
  rfl

/-- Integrating the actual pointwise determinant-volume formula introduces no extra normalization. -/
theorem expected_volume_normalization_of_pointwise {d : Nat}
    (nu : Measure (Paper.Point d))
    (hvolume : forall z : Fin (d + 1) -> Geometry.Point d,
      (d.factorial : Real) * Geometry.simplexVolume z = |Geometry.affineDet z|) :
    (d.factorial : Real) * Paper.expectedSimplexVolume nu =
      integral (Measure.pi (fun _ : Fin (d + 1) => nu)) (fun z => |Geometry.affineDet z|) := by
  unfold Paper.expectedSimplexVolume
  rw [<- integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => hvolume z)

theorem project_height_reconstruct {m : Nat} (z : Paper.Point (m + 1)) :
    Geometry.liftedPoint (Paper.projectLast z) (z (Fin.last m)) = z := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next => simp [Geometry.liftedPoint]
  next => simp [Geometry.liftedPoint, Paper.projectLast]

theorem sampled_height_absolute_determinant {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) :
    |Geometry.affineDet z| =
      |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))| := by
  have h := Geometry.paper_height_absolute_determinant
    (fun j => Paper.projectLast (z j)) (fun j => z j (Fin.last m))
  have hr : (fun j => Geometry.liftedPoint (Paper.projectLast (z j)) (z j (Fin.last m))) = z := by
    funext j
    exact project_height_reconstruct (z j)
  rw [hr] at h
  exact h

theorem height_volume_normalization_of_pointwise {m : Nat}
    (nu : Measure (Paper.Point (m + 1)))
    (hvolume : forall z : Fin (m + 2) -> Geometry.Point (m + 1),
      ((m + 1).factorial : Real) * Geometry.simplexVolume z = |Geometry.affineDet z|) :
    ((m + 1).factorial : Real) * Paper.expectedSimplexVolume nu =
      sampledHeightObjective nu := by
  rw [expected_volume_normalization_of_pointwise nu hvolume]
  unfold sampledHeightObjective
  apply integral_congr_ae
  exact Filter.Eventually.of_forall sampled_height_absolute_determinant

theorem simplexVolume_one_of_pointwise
    (hvolume : forall z : Fin 2 -> Geometry.Point 1,
      (Nat.factorial 1 : Real) * Geometry.simplexVolume z = |Geometry.affineDet z|)
    (z : Fin 2 -> Paper.Point 1) :
    Paper.simplexVolume z = |z 0 0 - z 1 0| := by
  have h := hvolume z
  have hdet : Geometry.affineDet z = z 0 0 - z 1 0 := by
    unfold Geometry.affineDet
    rw [Matrix.det_fin_two]
    change z 0 0 * 1 - 1 * z 1 0 = z 0 0 - z 1 0
    ring
  have hn : Geometry.simplexVolume z = |Geometry.affineDet z| := by
    simpa only [Nat.factorial_one, Nat.cast_one, one_mul] using h
  change Geometry.simplexVolume z = _
  rw [hn, hdet]

/-- Source S_1=D_1, including the exact iid-to-independent-pair measure bridge. -/
theorem base_one_of_pointwise (nu : Measure (Paper.Point 1)) [IsProbabilityMeasure nu]
    (hvolume : forall z : Fin 2 -> Geometry.Point 1,
      (Nat.factorial 1 : Real) * Geometry.simplexVolume z = |Geometry.affineDet z|) :
    Paper.expectedSimplexVolume nu = Paper.coordinateGap nu 0 := by
  unfold Paper.expectedSimplexVolume Paper.coordinateGap
  have hleft : integral (Measure.pi (fun _ : Fin 2 => nu)) (fun z => Paper.simplexVolume z) =
      integral (Measure.pi (fun _ : Fin 2 => nu)) (fun z => |z 0 0 - z 1 0|) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (simplexVolume_one_of_pointwise hvolume)
  rw [hleft]
  exact (measurePreserving_finTwoArrow nu).integral_comp'
    (fun zz => |zz.1 0 - zz.2 0|)

theorem expected_volume_normalization {d : Nat} (nu : Measure (Paper.Point d)) :
    (d.factorial : Real) * Paper.expectedSimplexVolume nu =
      integral (Measure.pi (fun _ : Fin (d + 1) => nu)) (fun z => |Geometry.affineDet z|) :=
  expected_volume_normalization_of_pointwise nu Geometry.simplex_volume_factorial

theorem height_volume_normalization {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) :
    ((m + 1).factorial : Real) * Paper.expectedSimplexVolume nu =
      sampledHeightObjective nu :=
  height_volume_normalization_of_pointwise nu Geometry.simplex_volume_factorial

theorem radon_normalization {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    expectedRadonMass nu =
      ((m + 2 : Nat) : Real) / 2 * (m.factorial : Real) *
        Paper.expectedSimplexVolume (nu.map Paper.projectLast) :=
  radon_normalization_of_projected_volume nu hfirst
    (expected_volume_normalization (nu.map Paper.projectLast))

/-- The source moment hypothesis suffices for the actual sampled simplex volume. -/
theorem sampled_simplexVolume_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) => Paper.simplexVolume z)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hfac : Not (((m + 1).factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  apply ((Moments.sampled_determinant_integrable nu hfirst).const_mul
    (1 / ((m + 1).factorial : Real))).congr
  exact Filter.Eventually.of_forall (fun z => by
    change (1 / ((m + 1).factorial : Real)) *
      |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))| =
      Paper.simplexVolume z
    rw [<- sampled_height_absolute_determinant,
      <- Geometry.simplex_volume_factorial]
    change (1 / ((m + 1).factorial : Real)) *
      (((m + 1).factorial : Real) * Paper.simplexVolume z) = Paper.simplexVolume z
    field_simp)

theorem base_one (nu : Measure (Paper.Point 1)) [IsProbabilityMeasure nu] :
    Paper.expectedSimplexVolume nu = Paper.coordinateGap nu 0 :=
  base_one_of_pointwise nu Geometry.simplex_volume_factorial

/-- Exact source normalization: d=m+1 and the peeled coordinate is Fin.last m. -/
theorem oneStep_of_height_gate_and_normalizations {m : Nat}
    (nu : Measure (Paper.Point (m + 1)))
    (hvolume : ((m + 1).factorial : Real) * Paper.expectedSimplexVolume nu =
      sampledHeightObjective nu)
    (hrad : expectedRadonMass nu =
      ((m + 2 : Nat) : Real) / 2 * (m.factorial : Real) *
        Paper.expectedSimplexVolume (nu.map Paper.projectLast))
    (hgate : sampledHeightObjective nu <=
      expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m)) :
    Paper.oneStepClaim m nu := by
  unfold Paper.oneStepClaim
  have hpositive : 0 < ((m + 1).factorial : Real) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  apply le_of_mul_le_mul_left (a := ((m + 1).factorial : Real)) ?_ hpositive
  calc
    ((m + 1).factorial : Real) * Paper.expectedSimplexVolume nu =
        sampledHeightObjective nu := hvolume
    _ <= expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m) := hgate
    _ = ((m + 1).factorial : Real) *
        (((m + 2 : Nat) : Real) / (2 * ((m + 1 : Nat) : Real)) *
          Paper.coordinateGap nu (Fin.last m) *
            Paper.expectedSimplexVolume (nu.map Paper.projectLast)) := by
      rw [hrad, Nat.factorial_succ, Nat.cast_mul]
      have hnonzero : Not (((m + 1 : Nat) : Real) = 0) := by positivity
      field_simp

/-- The only gate premise here is the paper's exact levelwise Bernoulli estimate. -/
theorem oneStep_of_levelwise_and_normalizations {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hvolume : ((m + 1).factorial : Real) * Paper.expectedSimplexVolume nu =
      sampledHeightObjective nu)
    (hrad : expectedRadonMass nu =
      ((m + 2 : Nat) : Real) / 2 * (m.factorial : Real) *
        Paper.expectedSimplexVolume (nu.map Paper.projectLast))
    (hlevel : forall t, integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
          Thresholds.threshold (z i (Fin.last m)) t)|) <=
      2 * nu.real {z | t < z (Fin.last m)} *
        (1 - nu.real {z | t < z (Fin.last m)}) * expectedRadonMass nu) :
    Paper.oneStepClaim m nu := by
  apply oneStep_of_height_gate_and_normalizations nu hvolume hrad
  exact Moments.sampled_height_gate_of_levelwise nu hfirst (expectedRadonMass nu) hlevel

/-- Theorem 1.3 follows from the height gate; both normalizations are now proved. -/
theorem oneStep_of_height_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hgate : sampledHeightObjective nu <=
      expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m)) :
    Paper.oneStepClaim m nu :=
  oneStep_of_height_gate_and_normalizations nu
    (height_volume_normalization nu) (radon_normalization nu hfirst) hgate

theorem sampledThresholdCost_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z => sampledThresholdCost z) (Measure.pi (fun _ : Fin (m + 2) => nu)) :=
  (Moments.sampled_threshold_integrable nu hfirst).integral_prod_left

/-- The first inequality of the source height/threshold-cost chain. -/
theorem sampled_height_le_thresholdCost {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    sampledHeightObjective nu <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu)) (fun z => sampledThresholdCost z) := by
  apply integral_mono (Moments.sampled_determinant_integrable nu hfirst)
    (sampledThresholdCost_integrable nu hfirst)
  intro z
  exact Thresholds.threshold_bound_left
    (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun i => z i (Fin.last m)) (Geometry.cofactor_sum_zero _)

/-- The second inequality of the source height/threshold-cost chain. -/
theorem sampled_thresholdCost_gate_of_levelwise {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hlevel : levelwiseBernoulliClaim nu) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu)) (fun z => sampledThresholdCost z) <=
      expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m) := by
  have hmeas : Measurable (fun z : Paper.Point (m + 1) => z (Fin.last m)) :=
    (continuous_apply (Fin.last m)).measurable
  have : IsProbabilityMeasure (nu.map (fun z => z (Fin.last m))) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  have h := Thresholds.lift_thresholdCost_levelwise_gate
    (Measure.pi (fun _ : Fin (m + 2) => nu))
    (nu.map (fun z => z (Fin.last m)))
    (fun z i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun z i => z i (Fin.last m)) (expectedRadonMass nu)
    (Moments.height_law_firstMoment nu hfirst)
    (Moments.sampled_threshold_integrable nu hfirst)
    (by simpa only [Thresholds.tailProbability_map nu (fun z => z (Fin.last m)) hmeas,
      levelwiseBernoulliClaim] using hlevel)
  rw [Moments.height_law_pair_gap nu] at h
  exact h

/-- The full source height inequality includes the intermediate threshold cost. -/
theorem sampled_height_cost_chain_of_levelwise {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hlevel : levelwiseBernoulliClaim nu) :
    And (sampledHeightObjective nu <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu)) (fun z => sampledThresholdCost z))
      (integral (Measure.pi (fun _ : Fin (m + 2) => nu)) (fun z => sampledThresholdCost z) <=
        expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m)) :=
  And.intro (sampled_height_le_thresholdCost nu hfirst)
    (sampled_thresholdCost_gate_of_levelwise nu hfirst hlevel)

/-- Exact one-step endpoint; the levelwise estimate is the sole remaining premise. -/
theorem oneStep_of_levelwise {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hlevel : levelwiseBernoulliClaim nu) :
    Paper.oneStepClaim m nu :=
  oneStep_of_levelwise_and_normalizations nu hfirst
    (height_volume_normalization nu) (radon_normalization nu hfirst) hlevel

theorem random_simplex_succ_of_oneStep {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hstep : Paper.oneStepClaim m nu)
    (hproject : Paper.randomSimplexClaim m (nu.map Paper.projectLast)) :
    Paper.randomSimplexClaim (m + 1) nu := by
  have hcoefficient : 0 <= Constants.oneStepCoefficient (m + 1) := by
    unfold Constants.oneStepCoefficient
    positivity
  have hgap := coordinateGap_nonneg nu (Fin.last m)
  change Paper.expectedSimplexVolume nu <=
    Constants.mainCoefficient (m + 1) * Finset.univ.prod (fun j => Paper.coordinateGap nu j)
  have hs : Paper.expectedSimplexVolume nu <=
      Constants.oneStepCoefficient (m + 1) * Paper.coordinateGap nu (Fin.last m) *
        Paper.expectedSimplexVolume (nu.map Paper.projectLast) := by
    simpa only [Paper.oneStepClaim, Constants.oneStepCoefficient, Nat.add_assoc] using hstep
  have hp : Paper.expectedSimplexVolume (nu.map Paper.projectLast) <=
      Constants.mainCoefficient m *
        Finset.univ.prod (fun j => Paper.coordinateGap (nu.map Paper.projectLast) j) := hproject
  calc
    Paper.expectedSimplexVolume nu <=
        Constants.oneStepCoefficient (m + 1) * Paper.coordinateGap nu (Fin.last m) *
          Paper.expectedSimplexVolume (nu.map Paper.projectLast) := hs
    _ <= Constants.oneStepCoefficient (m + 1) * Paper.coordinateGap nu (Fin.last m) *
        (Constants.mainCoefficient m *
          Finset.univ.prod (fun j => Paper.coordinateGap (nu.map Paper.projectLast) j)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hcoefficient hgap)
    _ = Constants.mainCoefficient (m + 1) *
        Finset.univ.prod (fun j => Paper.coordinateGap nu j) := by
      rw [Constants.mainCoefficient_succ, Fin.prod_univ_castSucc]
      simp_rw [coordinateGap_projection]
      ring

/-- Exact main endpoint implication. The base and one-step premises stay explicit. -/
theorem all_dimensions_random_simplex_of_oneStep_and_base
    (hstep : Paper.allDimensionsOneStep)
    (hbase : forall (nu : Measure (Paper.Point 1)), IsProbabilityMeasure nu ->
      Paper.finiteCoordinateFirstMoments nu ->
      Paper.expectedSimplexVolume nu = Paper.coordinateGap nu 0) :
    Paper.allDimensionsRandomSimplex := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      intro nu hprob hfirst
      change Paper.expectedSimplexVolume nu <=
        Constants.mainCoefficient 1 * Finset.univ.prod (fun j => Paper.coordinateGap nu j)
      rw [Constants.mainCoefficient_one, Fin.prod_univ_one, hbase nu hprob hfirst]
      simp
  | succ d hd ih =>
      intro nu hprob hfirst
      let _ := hprob
      let _ := projection_probability nu
      have hproj := ih (nu.map Paper.projectLast) inferInstance (projection_first_moments nu hfirst)
      exact random_simplex_succ_of_oneStep nu (hstep d hd nu hprob hfirst) hproj

/-- Exact source induction, with its base case and projection bridges discharged. -/
theorem all_dimensions_random_simplex_of_oneStep
    (hstep : Paper.allDimensionsOneStep) : Paper.allDimensionsRandomSimplex := by
  apply all_dimensions_random_simplex_of_oneStep_and_base hstep
  intro nu hprob _
  let _ := hprob
  exact base_one nu

/-- Every assumption needed to close the universal one-step theorem is explicit. -/
theorem all_dimensions_oneStep_of_levelwise
    (hlevel : forall (m : Nat), 1 <= m ->
      forall (nu : Measure (Paper.Point (m + 1))), IsProbabilityMeasure nu ->
        Paper.finiteCoordinateFirstMoments nu -> levelwiseBernoulliClaim nu) :
    Paper.allDimensionsOneStep := by
  intro m hm nu hprob hfirst
  let _ := hprob
  exact oneStep_of_levelwise nu hfirst (hlevel m hm nu hprob hfirst)

/-- The source main endpoint with exactly the universal levelwise premise exposed. -/
theorem all_dimensions_random_simplex_of_levelwise
    (hlevel : forall (m : Nat), 1 <= m ->
      forall (nu : Measure (Paper.Point (m + 1))), IsProbabilityMeasure nu ->
        Paper.finiteCoordinateFirstMoments nu -> levelwiseBernoulliClaim nu) :
    Paper.allDimensionsRandomSimplex :=
  all_dimensions_random_simplex_of_oneStep (all_dimensions_oneStep_of_levelwise hlevel)

end Hypercube.EndpointAssembly
