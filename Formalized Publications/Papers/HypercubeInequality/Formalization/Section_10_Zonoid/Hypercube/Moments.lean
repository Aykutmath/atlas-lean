import Section_10_Zonoid.Hypercube.Statements
import Section_10_Zonoid.Hypercube.Geometry
import Section_10_Zonoid.Hypercube.Thresholds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/- Source: hypercube_readable.tex, the arbitrary-height integrability step
and Appendix on quantization. Each cofactor omits its own height sample.
Consequently the dominating product uses one integrable function per sample;
no moment of height times projected coordinates from the same sample occurs. -/

noncomputable section

open MeasureTheory

namespace Hypercube.Moments

def rowFactor {m : Nat} (w : Geometry.Point m) : Real :=
  1 + Finset.sum Finset.univ (fun j => |w j|)

theorem rowFactor_nonneg {m : Nat} (w : Geometry.Point m) : 0 <= rowFactor w := by
  have hs : 0 <= Finset.sum Finset.univ (fun j => |w j|) :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (w j))
  unfold rowFactor
  linarith

theorem affineMatrix_entry_bound {m : Nat}
    (w : Fin (m + 1) -> Geometry.Point m) (i j : Fin (m + 1)) :
    |Geometry.affineMatrix w i j| <= rowFactor (w i) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    have hs : 0 <= Finset.sum Finset.univ (fun j => |w i j|) :=
      Finset.sum_nonneg (fun j _ => abs_nonneg (w i j))
    simp only [Geometry.affineMatrix, Fin.lastCases_last, abs_one, rowFactor]
    linarith
  next j =>
    have hj : |w i j| <= Finset.sum Finset.univ (fun k => |w i k|) :=
      Finset.single_le_sum (fun k _ => abs_nonneg (w i k)) (Finset.mem_univ j)
    simp only [Geometry.affineMatrix, Fin.lastCases_castSucc, rowFactor]
    linarith

theorem determinant_abs_row_bound {n : Nat}
    (M : Matrix (Fin n) (Fin n) Real) (B : Fin n -> Real)
    (hB : forall i j, |M i j| <= B i) :
    |M.det| <= (Nat.factorial n : Real) * Finset.prod Finset.univ B := by
  rw [Matrix.det_apply']
  calc
    |Finset.sum Finset.univ (fun s : Equiv.Perm (Fin n) =>
        ((Equiv.Perm.sign s : Int) : Real) * Finset.prod Finset.univ (fun j => M (s j) j))| <=
      Finset.sum Finset.univ (fun s : Equiv.Perm (Fin n) =>
        |((Equiv.Perm.sign s : Int) : Real) * Finset.prod Finset.univ (fun j => M (s j) j)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun _ : Equiv.Perm (Fin n) =>
        Finset.prod Finset.univ B) := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, <- Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul,
        Finset.abs_prod]
      calc
        Finset.prod Finset.univ (fun j => |M (s j) j|) <=
          Finset.prod Finset.univ (fun j => B (s j)) := by
          gcongr with j hj
          exact hB (s j) j
        _ = Finset.prod Finset.univ B := Equiv.prod_comp s B
    _ = (Nat.factorial n : Real) * Finset.prod Finset.univ B := by
      simp [Finset.sum_const, Fintype.card_perm, nsmul_eq_mul]

theorem affineDet_abs_bound {m : Nat}
    (w : Fin (m + 1) -> Geometry.Point m) :
    |Geometry.affineDet w| <= (Nat.factorial (m + 1) : Real) *
      Finset.prod Finset.univ (fun i => rowFactor (w i)) :=
  determinant_abs_row_bound (Geometry.affineMatrix w) (fun i => rowFactor (w i))
    (affineMatrix_entry_bound w)

theorem cofactor_abs {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (i : Fin (m + 2)) :
    |Geometry.cofactor w i| = |Geometry.affineDet (fun j => w (i.succAbove j))| := by
  simp [Geometry.cofactor, abs_mul, abs_pow]

def heightDominant {m : Nat} (z : Fin (m + 2) -> Paper.Point (m + 1))
    (i : Fin (m + 2)) : Real :=
  (Nat.factorial (m + 1) : Real) * Finset.prod Finset.univ
    (fun j => if j = i then |z j (Fin.last m)| else rowFactor (Paper.projectLast (z j)))

theorem heightDominant_product {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    Finset.prod Finset.univ
      (fun j => if j = i then |z j (Fin.last m)| else rowFactor (Paper.projectLast (z j))) =
      |z i (Fin.last m)| * Finset.prod Finset.univ
        (fun j : Fin (m + 1) => rowFactor (Paper.projectLast (z (i.succAbove j)))) := by
  rw [Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

theorem cofactor_height_bound {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m)| <=
      heightDominant z i := by
  rw [cofactor_abs]
  have hdet := affineDet_abs_bound (fun j => Paper.projectLast (z (i.succAbove j)))
  calc
    |Geometry.affineDet (fun j => Paper.projectLast (z (i.succAbove j)))| *
        |z i (Fin.last m)| <=
      ((Nat.factorial (m + 1) : Real) * Finset.prod Finset.univ
        (fun j => rowFactor (Paper.projectLast (z (i.succAbove j))))) * |z i (Fin.last m)| :=
      mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
    _ = heightDominant z i := by
      unfold heightDominant
      rw [heightDominant_product]
      ring

theorem projected_rowFactor_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z => rowFactor (Paper.projectLast z)) nu := by
  exact (integrable_const (1 : Real)).add
    (integrable_finsetSum Finset.univ (fun j _ => hfirst j.castSucc))

theorem heightDominant_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (i : Fin (m + 2)) :
    Integrable (fun z => heightDominant z i)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hrow (j : Fin (m + 2)) : Integrable
      (fun z : Paper.Point (m + 1) =>
        if j = i then |z (Fin.last m)| else rowFactor (Paper.projectLast z)) nu := by
    by_cases hj : j = i
    case pos =>
      simpa [hj] using hfirst (Fin.last m)
    case neg =>
      simpa [hj] using projected_rowFactor_integrable nu hfirst
  exact (Integrable.fintype_prod hrow).const_mul (Nat.factorial (m + 1) : Real)

theorem sampled_cofactor_continuous {m : Nat} (i : Fin (m + 2)) :
    Continuous (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      Geometry.cofactor (fun j => Paper.projectLast (z j)) i) := by
  unfold Geometry.cofactor Geometry.affineDet
  apply continuous_const.mul
  apply Continuous.matrix_det
  apply continuous_pi
  intro r
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin (m + 2) -> Paper.Point (m + 1) => (1 : Real)))
  next j =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_castSucc, Paper.projectLast,
      Function.comp_def] using
      ((continuous_apply j.castSucc).comp (continuous_apply (i.succAbove r)))

theorem sampled_height_continuous {m : Nat} (i : Fin (m + 2)) :
    Continuous (fun z : Fin (m + 2) -> Paper.Point (m + 1) => z i (Fin.last m)) :=
  (continuous_apply (Fin.last m)).comp (continuous_apply i)

theorem cofactor_height_product_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (i : Fin (m + 2)) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m)|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hmeas : Measurable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m)|) :=
    ((sampled_cofactor_continuous i).abs.mul (sampled_height_continuous i).abs).measurable
  apply (heightDominant_integrable nu hfirst i).mono_nonneg hmeas.aestronglyMeasurable
  case hnonneg =>
    exact Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  case h =>
    exact Filter.Eventually.of_forall (fun z => cofactor_height_bound z i)

theorem sampled_threshold_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Prod (Fin (m + 2) -> Paper.Point (m + 1)) Real =>
      |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z.1 j)) i *
          Thresholds.threshold (z.1 i (Fin.last m)) z.2)|)
      ((Measure.pi (fun _ : Fin (m + 2) => nu)).prod volume) :=
  Thresholds.joint_threshold_integrable
    (Measure.pi (fun _ : Fin (m + 2) => nu))
    (fun z i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun z i => z i (Fin.last m))
    (fun z => Geometry.cofactor_sum_zero (fun j => Paper.projectLast (z j)))
    (fun i => (sampled_cofactor_continuous i).measurable)
    (fun i => (sampled_height_continuous i).measurable)
    (fun i => cofactor_height_product_integrable nu hfirst i)

theorem sampled_determinant_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) :=
  Thresholds.coefficient_height_sum_integrable
    (Measure.pi (fun _ : Fin (m + 2) => nu))
    (fun z i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun z i => z i (Fin.last m))
    (fun i => (sampled_cofactor_continuous i).measurable)
    (fun i => (sampled_height_continuous i).measurable)
    (fun i => cofactor_height_product_integrable nu hfirst i)

def cofactorDominant {m : Nat} (z : Fin (m + 2) -> Paper.Point (m + 1))
    (i : Fin (m + 2)) : Real :=
  (Nat.factorial (m + 1) : Real) * Finset.prod Finset.univ
    (fun j => if j = i then 1 else rowFactor (Paper.projectLast (z j)))

theorem cofactorDominant_product {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    Finset.prod Finset.univ
      (fun j => if j = i then 1 else rowFactor (Paper.projectLast (z j))) =
      Finset.prod Finset.univ
        (fun j : Fin (m + 1) => rowFactor (Paper.projectLast (z (i.succAbove j)))) := by
  rw [Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

theorem cofactor_bound {m : Nat}
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| <= cofactorDominant z i := by
  rw [cofactor_abs]
  unfold cofactorDominant
  rw [cofactorDominant_product]
  exact affineDet_abs_bound (fun j => Paper.projectLast (z (i.succAbove j)))

theorem cofactorDominant_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (i : Fin (m + 2)) :
    Integrable (fun z => cofactorDominant z i)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hrow (j : Fin (m + 2)) : Integrable
      (fun z : Paper.Point (m + 1) =>
        if j = i then (1 : Real) else rowFactor (Paper.projectLast z)) nu := by
    by_cases hj : j = i
    case pos =>
      simp [hj]
    case neg =>
      simpa [hj] using projected_rowFactor_integrable nu hfirst
  exact (Integrable.fintype_prod hrow).const_mul (Nat.factorial (m + 1) : Real)

theorem sampled_cofactor_abs_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (i : Fin (m + 2)) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  apply (cofactorDominant_integrable nu hfirst i).mono_nonneg
    (sampled_cofactor_continuous i).abs.measurable.aestronglyMeasurable
  case hnonneg =>
    exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
  case h =>
    exact Filter.Eventually.of_forall (fun z => cofactor_bound z i)

theorem sampled_radonMass_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      Geometry.radonMass (fun j => Paper.projectLast (z j)))
      (Measure.pi (fun _ : Fin (m + 2) => nu)) :=
  (integrable_finsetSum Finset.univ
    (fun i _ => sampled_cofactor_abs_integrable nu hfirst i)).const_mul (1 / 2 : Real)

theorem height_law_firstMoment {m : Nat}
    (nu : Measure (Paper.Point (m + 1)))
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Integrable (fun t : Real => t) (nu.map (fun z => z (Fin.last m))) := by
  have hmeas : Measurable (fun z : Paper.Point (m + 1) => z (Fin.last m)) :=
    (continuous_apply (Fin.last m)).measurable
  have hheight : Integrable (fun z : Paper.Point (m + 1) => z (Fin.last m)) nu := by
    apply (integrable_norm_iff hmeas.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hfirst (Fin.last m)
  exact (integrable_map_measure measurable_id.aestronglyMeasurable hmeas.aemeasurable).mpr hheight

theorem height_law_pair_gap {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu] :
    integral ((nu.map (fun z => z (Fin.last m))).prod
      (nu.map (fun z => z (Fin.last m)))) (fun z => |z.1 - z.2|) =
      Paper.coordinateGap nu (Fin.last m) := by
  have hmeas : Measurable (fun z : Paper.Point (m + 1) => z (Fin.last m)) :=
    (continuous_apply (Fin.last m)).measurable
  have hdistmeas : Measurable (fun z : Prod Real Real => |z.1 - z.2|) :=
    continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
  rw [Measure.map_prod_map nu nu hmeas hmeas,
    integral_map (hmeas.prodMap hmeas).aemeasurable hdistmeas.aestronglyMeasurable]
  rfl

/- Paper-facing conditional analytic gate. The sole unresolved mathematical
premise here is the levelwise Bernoulli bound; all integrability, product-law,
strict-threshold, marginal-law, and independent-copy bridges are proved. -/

theorem sampled_height_gate_of_levelwise {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (L : Real)
    (hlevel : forall t, integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
          Thresholds.threshold (z i (Fin.last m)) t)|) <=
      2 * nu.real {z | t < z (Fin.last m)} *
        (1 - nu.real {z | t < z (Fin.last m)}) * L) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))|) <=
      L * Paper.coordinateGap nu (Fin.last m) := by
  have hmeas : Measurable (fun z : Paper.Point (m + 1) => z (Fin.last m)) :=
    (continuous_apply (Fin.last m)).measurable
  have : IsProbabilityMeasure (nu.map (fun z => z (Fin.last m))) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).mpr inferInstance
  have h := Thresholds.lift_levelwise_gate_of_product_moments
    (Measure.pi (fun _ : Fin (m + 2) => nu))
    (nu.map (fun z => z (Fin.last m)))
    (fun z i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
    (fun z i => z i (Fin.last m)) L
    (fun z => Geometry.cofactor_sum_zero (fun j => Paper.projectLast (z j)))
    (height_law_firstMoment nu hfirst)
    (fun i => (sampled_cofactor_continuous i).measurable)
    (fun i => (sampled_height_continuous i).measurable)
    (fun i => cofactor_height_product_integrable nu hfirst i)
    (by simpa only [Thresholds.tailProbability_map nu (fun z => z (Fin.last m)) hmeas] using hlevel)
  rw [height_law_pair_gap nu] at h
  exact h

theorem cofactor_continuous {m : Nat} (i : Fin (m + 2)) :
    Continuous (fun w : Fin (m + 2) -> Geometry.Point m => Geometry.cofactor w i) := by
  unfold Geometry.cofactor Geometry.affineDet
  apply continuous_const.mul
  apply Continuous.matrix_det
  apply continuous_pi
  intro r
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : Fin (m + 2) -> Geometry.Point m => (1 : Real)))
  next j =>
    simpa only [Geometry.affineMatrix, Fin.lastCases_castSucc, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply (i.succAbove r)))

theorem projectLast_continuous {m : Nat} :
    Continuous (Paper.projectLast : Paper.Point (m + 1) -> Geometry.Point m) :=
  continuous_pi (fun j => continuous_apply j.castSucc)

theorem affineDet_mapped_bound {m : Nat}
    (Q : Geometry.Point m -> Geometry.Point m) (K : Real)
    (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (w : Fin (m + 1) -> Geometry.Point m) :
    |Geometry.affineDet (fun j => Q (w j))| <= K ^ (m + 1) *
      ((Nat.factorial (m + 1) : Real) * Finset.prod Finset.univ (fun j => rowFactor (w j))) := by
  have hp : Finset.prod Finset.univ (fun j => rowFactor (Q (w j))) <=
      Finset.prod Finset.univ (fun j => K * rowFactor (w j)) := by
    gcongr with j hj
    all_goals first
      | exact rowFactor_nonneg _
      | exact hQ _
      | intro j hj; exact rowFactor_nonneg _
  calc
    |Geometry.affineDet (fun j => Q (w j))| <=
      (Nat.factorial (m + 1) : Real) *
        Finset.prod Finset.univ (fun j => rowFactor (Q (w j))) :=
      affineDet_abs_bound _
    _ <= (Nat.factorial (m + 1) : Real) *
        Finset.prod Finset.univ (fun j => K * rowFactor (w j)) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = K ^ (m + 1) * ((Nat.factorial (m + 1) : Real) *
        Finset.prod Finset.univ (fun j => rowFactor (w j))) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

theorem mapped_cofactor_height_bound {m : Nat}
    (Q : Geometry.Point m -> Geometry.Point m) (K : Real)
    (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i| * |z i (Fin.last m)| <=
      K ^ (m + 1) * heightDominant z i := by
  rw [cofactor_abs]
  have hdet := affineDet_mapped_bound Q K hQ
    (fun j => Paper.projectLast (z (i.succAbove j)))
  calc
    |Geometry.affineDet (fun j => Q (Paper.projectLast (z (i.succAbove j))))| *
        |z i (Fin.last m)| <=
      (K ^ (m + 1) * ((Nat.factorial (m + 1) : Real) * Finset.prod Finset.univ
        (fun j => rowFactor (Paper.projectLast (z (i.succAbove j)))))) * |z i (Fin.last m)| :=
      mul_le_mul_of_nonneg_right hdet (abs_nonneg _)
    _ = K ^ (m + 1) * heightDominant z i := by
      unfold heightDominant
      rw [heightDominant_product]
      ring

theorem mapped_cofactor_abs_bound {m : Nat}
    (Q : Geometry.Point m -> Geometry.Point m) (K : Real)
    (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (z : Fin (m + 2) -> Paper.Point (m + 1)) (i : Fin (m + 2)) :
    |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i| <=
      K ^ (m + 1) * cofactorDominant z i := by
  rw [cofactor_abs]
  unfold cofactorDominant
  rw [cofactorDominant_product]
  exact affineDet_mapped_bound Q K hQ (fun j => Paper.projectLast (z (i.succAbove j)))

theorem mapped_sampled_cofactor_measurable {m : Nat}
    (Q : Geometry.Point m -> Geometry.Point m) (hQ : Measurable Q) (i : Fin (m + 2)) :
    Measurable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i) := by
  have hmap : Measurable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      fun j => Q (Paper.projectLast (z j))) := by
    apply Measurable.of_eval
    intro j
    simpa only [Function.comp_def] using
      hQ.comp (projectLast_continuous.comp (continuous_apply j)).measurable
  simpa only [Function.comp_def] using (cofactor_continuous i).measurable.comp hmap

theorem mapped_cofactor_height_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (Q : Geometry.Point m -> Geometry.Point m) (hQmeas : Measurable Q)
    (K : Real) (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (i : Fin (m + 2)) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i| * |z i (Fin.last m)|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hmeas : Measurable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i| * |z i (Fin.last m)|) :=
    (continuous_abs.measurable.comp (mapped_sampled_cofactor_measurable Q hQmeas i)).mul
      (sampled_height_continuous i).abs.measurable
  apply ((heightDominant_integrable nu hfirst i).const_mul (K ^ (m + 1))).mono_nonneg
    hmeas.aestronglyMeasurable
  case hnonneg =>
    exact Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  case h =>
    exact Filter.Eventually.of_forall (fun z => mapped_cofactor_height_bound Q K hQ z i)

theorem mapped_cofactor_abs_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (Q : Geometry.Point m -> Geometry.Point m) (hQmeas : Measurable Q)
    (K : Real) (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (i : Fin (m + 2)) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  apply ((cofactorDominant_integrable nu hfirst i).const_mul (K ^ (m + 1))).mono_nonneg
    (continuous_abs.measurable.comp
      (mapped_sampled_cofactor_measurable Q hQmeas i)).aestronglyMeasurable
  case hnonneg =>
    exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
  case h =>
    exact Filter.Eventually.of_forall (fun z => mapped_cofactor_abs_bound Q K hQ z i)

theorem mapped_determinant_abs_bound {m : Nat}
    (Q : Geometry.Point m -> Geometry.Point m) (K : Real)
    (hQ : forall w, rowFactor (Q w) <= K * rowFactor w)
    (z : Fin (m + 2) -> Paper.Point (m + 1)) :
    |Finset.sum Finset.univ (fun i =>
      Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i * z i (Fin.last m))| <=
      K ^ (m + 1) * Finset.sum Finset.univ (fun i => heightDominant z i) := by
  calc
    |Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i * z i (Fin.last m))| <=
      Finset.sum Finset.univ (fun i =>
        |Geometry.cofactor (fun j => Q (Paper.projectLast (z j))) i * z i (Fin.last m)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun i => K ^ (m + 1) * heightDominant z i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mapped_cofactor_height_bound Q K hQ z i
    _ = K ^ (m + 1) * Finset.sum Finset.univ (fun i => heightDominant z i) := by
      rw [Finset.mul_sum]

/- Explicit probability product bridge: applying the same measurable map
to every iid sample gives the iid product of the pushforward marginal. -/

theorem iid_map_commutes {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) [IsProbabilityMeasure nu] (n : Nat)
    (Q : X -> Y) (hQ : Measurable Q) :
    (Measure.pi (fun _ : Fin n => nu)).map (fun z i => Q (z i)) =
      Measure.pi (fun _ : Fin n => nu.map Q) := by
  have : IsProbabilityMeasure (nu.map Q) :=
    (Measure.isProbabilityMeasure_map_iff hQ.aemeasurable).mpr inferInstance
  exact Measure.pi_map_pi (fun _ : Fin n => hQ.aemeasurable)

theorem iid_integral_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) [IsProbabilityMeasure nu] (n : Nat)
    (Q : X -> Y) (hQ : Measurable Q) (f : (Fin n -> Y) -> Real) (hf : Measurable f) :
    integral (Measure.pi (fun _ : Fin n => nu.map Q)) f =
      integral (Measure.pi (fun _ : Fin n => nu)) (fun z => f (fun i => Q (z i))) := by
  have hsample : Measurable (fun z : Fin n -> X => fun i => Q (z i)) :=
    Measurable.of_eval (fun i => hQ.comp (measurable_pi_apply i))
  rw [<- iid_map_commutes nu n Q hQ]
  exact integral_map_of_stronglyMeasurable hsample hf.stronglyMeasurable

/- Source Appendix B, final paragraph: finiteness of the marginal gap is
equivalent to the first absolute moment. `Integrable` records finiteness of
the absolute Lebesgue expectation, rather than the value of an undefined
Bochner integral. -/

theorem integrable_gap_iff_firstMoment (mu : Measure Real) [IsProbabilityMeasure mu] :
    Integrable (fun z : Prod Real Real => |z.1 - z.2|) (mu.prod mu) <->
      Integrable (fun a : Real => |a|) mu := by
  constructor
  case mp =>
    intro hgap
    let hpoint := hgap.prod_right_ae.exists
    let a := hpoint.choose
    have ha : Integrable (fun b : Real => |a - b|) mu := hpoint.choose_spec
    have hmeas : Measurable (fun b : Real => a - b) := measurable_const.sub measurable_id
    have hsub : Integrable (fun b : Real => a - b) mu := by
      apply (integrable_norm_iff hmeas.aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using ha
    have hid : Integrable (fun b : Real => b) mu := by
      have hh := (integrable_const a).sub hsub
      have heq : (fun b : Real => a - (a - b)) = (fun b => b) := by
        funext b
        ring
      change Integrable (fun b : Real => a - (a - b)) mu at hh
      rw [heq] at hh
      exact hh
    exact hid.abs
  case mpr =>
    intro hfirst
    have hid : Integrable (fun a : Real => a) mu := by
      apply (integrable_norm_iff measurable_id.aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs, id_eq] using hfirst
    exact ((hid.comp_fst mu).sub (hid.comp_snd mu)).abs

end Hypercube.Moments
