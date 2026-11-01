import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open MeasureTheory

namespace Hypercube.Thresholds

/- Source: hypercube_readable.tex, equations layer-cake and threshold-bound.
The strict threshold is exactly the paper's indicator of {a > t}.
Centering at zero avoids separately integrating two infinite half-lines. -/

noncomputable def threshold (a t : Real) : Real := by
  classical
  exact if t < a then 1 else 0

noncomputable def centeredThreshold (a t : Real) : Real :=
  threshold a t - threshold 0 t

theorem centeredThreshold_of_nonneg (a : Real) (ha : 0 <= a) :
    centeredThreshold a = (Set.Ico 0 a).indicator (fun _ => (1 : Real)) := by
  classical
  funext t
  by_cases ht0 : t < 0
  case pos =>
    have hta : t < a := lt_of_lt_of_le ht0 ha
    simp [centeredThreshold, threshold, Set.indicator, Set.mem_Ico,
      ht0, hta, not_le_of_gt ht0]
  case neg =>
    have h0t : 0 <= t := le_of_not_gt ht0
    by_cases hta : t < a
    all_goals simp [centeredThreshold, threshold, Set.indicator,
      Set.mem_Ico, ht0, hta, h0t]

theorem centeredThreshold_of_nonpos (a : Real) (ha : a <= 0) :
    centeredThreshold a = -(Set.Ico a 0).indicator (fun _ => (1 : Real)) := by
  classical
  funext t
  by_cases hta : t < a
  case pos =>
    have ht0 : t < 0 := lt_of_lt_of_le hta ha
    simp [centeredThreshold, threshold, Set.indicator, Set.mem_Ico,
      ht0, hta, not_le_of_gt hta]
  case neg =>
    have hat : a <= t := le_of_not_gt hta
    by_cases ht0 : t < 0
    all_goals simp [centeredThreshold, threshold, Set.indicator,
      Set.mem_Ico, ht0, hta, hat]

theorem threshold_values (a t : Real) :
    Or (threshold a t = 0) (threshold a t = 1) := by
  unfold threshold
  split <;> simp

theorem threshold_shift (a b t : Real) :
    threshold a t - threshold b t = centeredThreshold (a - b) (t - b) := by
  have hta : (t - b < a - b) = (t < a) := by simp
  have htb : (t - b < 0) = (t < b) := by simp
  simp [centeredThreshold, threshold, hta, htb]

theorem threshold_difference_of_le (a b : Real) (hab : a <= b) :
    (fun t => threshold b t - threshold a t) =
      (Set.Ico a b).indicator (fun _ => (1 : Real)) := by
  classical
  funext t
  by_cases hta : t < a
  case pos =>
    have htb : t < b := lt_of_lt_of_le hta hab
    simp [threshold, Set.indicator, Set.mem_Ico, hta, htb, not_le_of_gt hta]
  case neg =>
    have hat : a <= t := le_of_not_gt hta
    by_cases htb : t < b
    all_goals simp [threshold, Set.indicator, Set.mem_Ico, hta, htb, hat]

theorem cofactor_threshold_centering {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) (t : Real) :
    Finset.sum Finset.univ (fun i => c i * threshold (height i) t) =
      Finset.sum Finset.univ (fun i => c i * centeredThreshold (height i) t) := by
  simp only [centeredThreshold, mul_sub, Finset.sum_sub_distrib]
  rw [<- Finset.sum_mul, hc, zero_mul, sub_zero]

theorem centered_threshold_abs_bound {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (t : Real) :
    |Finset.sum Finset.univ (fun i => c i * centeredThreshold (height i) t)| <=
      Finset.sum Finset.univ (fun i => |c i| * |centeredThreshold (height i) t|) := by
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (fun i => c i * centeredThreshold (height i) t)
      Finset.univ)

theorem interval_indicator_integrable (a b : Real) :
    Integrable ((Set.Ico a b).indicator (fun _ => (1 : Real))) volume := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  exact integrableOn_const (C := (1 : Real)) (by simp [Real.volume_Ico])

theorem interval_indicator_integral (a b : Real) (hab : a <= b) :
    integral volume ((Set.Ico a b).indicator (fun _ => (1 : Real))) = b - a := by
  rw [integral_indicator_const 1 measurableSet_Ico]
  simp [measureReal_def, Real.volume_Ico, smul_eq_mul, sub_nonneg.mpr hab]

theorem interval_indicator_abs (a b : Real) :
    (fun t => |(Set.Ico a b).indicator (fun _ => (1 : Real)) t|) =
      (Set.Ico a b).indicator (fun _ => (1 : Real)) := by
  classical
  funext t
  by_cases ht : And (a <= t) (t < b)
  all_goals simp [Set.indicator, Set.mem_Ico, ht]

theorem centeredThreshold_integrable (a : Real) :
    Integrable (centeredThreshold a) volume := by
  by_cases ha : 0 <= a
  case pos =>
    rw [centeredThreshold_of_nonneg a ha]
    exact interval_indicator_integrable 0 a
  case neg =>
    rw [centeredThreshold_of_nonpos a (le_of_not_ge ha)]
    exact (interval_indicator_integrable a 0).neg

theorem centeredThreshold_integral (a : Real) :
    integral volume (centeredThreshold a) = a := by
  by_cases ha : 0 <= a
  case pos =>
    rw [centeredThreshold_of_nonneg a ha, interval_indicator_integral 0 a ha]
    simp
  case neg =>
    have ha' : a <= 0 := le_of_not_ge ha
    rw [centeredThreshold_of_nonpos a ha']
    change integral volume (fun t => -((Set.Ico a 0).indicator (fun _ => (1 : Real)) t)) = a
    rw [integral_neg, interval_indicator_integral a 0 ha']
    ring

theorem centeredThreshold_abs_integral (a : Real) :
    integral volume (fun t => |centeredThreshold a t|) = |a| := by
  by_cases ha : 0 <= a
  case pos =>
    rw [centeredThreshold_of_nonneg a ha, interval_indicator_abs,
      interval_indicator_integral 0 a ha, abs_of_nonneg ha]
    simp
  case neg =>
    have ha' : a <= 0 := le_of_not_ge ha
    rw [centeredThreshold_of_nonpos a ha']
    simp only [Pi.neg_apply, abs_neg]
    rw [interval_indicator_abs, interval_indicator_integral a 0 ha', abs_of_nonpos ha']
    simp

theorem finite_layer_cake {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) :
    integral volume (fun t =>
      Finset.sum Finset.univ (fun i => c i * threshold (height i) t)) =
      Finset.sum Finset.univ (fun i => c i * height i) := by
  simp_rw [cofactor_threshold_centering c height hc]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (centeredThreshold_integrable (height i)).const_mul (c i))]
  simp only [integral_const_mul, centeredThreshold_integral]

theorem threshold_sum_integrable {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) :
    Integrable (fun t =>
      Finset.sum Finset.univ (fun i => c i * threshold (height i) t)) volume := by
  simp_rw [cofactor_threshold_centering c height hc]
  exact integrable_finsetSum Finset.univ
    (fun i _ => (centeredThreshold_integrable (height i)).const_mul (c i))

noncomputable def thresholdCost {Index : Type*} [Fintype Index]
    (c height : Index -> Real) : Real :=
  integral volume (fun t =>
    |Finset.sum Finset.univ (fun i => c i * threshold (height i) t)|)

theorem threshold_bound_left {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) :
    |Finset.sum Finset.univ (fun i => c i * height i)| <= thresholdCost c height := by
  rw [<- finite_layer_cake c height hc]
  exact abs_integral_le_integral_abs

theorem threshold_bound_right {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) :
    thresholdCost c height <=
      Finset.sum Finset.univ (fun i => |c i| * |height i|) := by
  unfold thresholdCost
  simp_rw [cofactor_threshold_centering c height hc]
  have hsum := integrable_finsetSum Finset.univ
    (fun i _ => (centeredThreshold_integrable (height i)).const_mul (c i))
  have hmajor := integrable_finsetSum Finset.univ
    (fun i _ => (centeredThreshold_integrable (height i)).abs.const_mul |c i|)
  calc
    integral volume (fun t =>
      |Finset.sum Finset.univ (fun i => c i * centeredThreshold (height i) t)|) <=
        integral volume (fun t => Finset.sum Finset.univ
          (fun i => |c i| * |centeredThreshold (height i) t|)) :=
      integral_mono hsum.abs hmajor (centered_threshold_abs_bound c height)
    _ = Finset.sum Finset.univ (fun i => |c i| * |height i|) := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => (centeredThreshold_integrable (height i)).abs.const_mul |c i|)]
      simp only [integral_const_mul, centeredThreshold_abs_integral]

theorem threshold_bound {Index : Type*} [Fintype Index]
    (c height : Index -> Real) (hc : Finset.sum Finset.univ c = 0) :
    And (|Finset.sum Finset.univ (fun i => c i * height i)| <= thresholdCost c height)
      (thresholdCost c height <=
        Finset.sum Finset.univ (fun i => |c i| * |height i|)) :=
  And.intro (threshold_bound_left c height hc) (threshold_bound_right c height hc)

/- The pointwise identity underlying equation gini. Its expectation and
probability factor 2 require the separate product-measure Tonelli argument. -/

theorem threshold_difference_integrable (a b : Real) :
    Integrable (fun t => threshold a t - threshold b t) volume := by
  have heq : (fun t => threshold a t - threshold b t) =
      (fun t => centeredThreshold a t - centeredThreshold b t) := by
    funext t
    simp [centeredThreshold]
  rw [heq]
  exact (centeredThreshold_integrable a).sub (centeredThreshold_integrable b)

theorem threshold_difference_abs_integral (a b : Real) :
    integral volume (fun t => |threshold a t - threshold b t|) = |a - b| := by
  by_cases hab : a <= b
  case pos =>
    have heq : (fun t => |threshold a t - threshold b t|) =
        (fun t => |threshold b t - threshold a t|) := by
      funext t
      exact abs_sub_comm _ _
    have hinterval : (fun t => |threshold b t - threshold a t|) =
        (Set.Ico a b).indicator (fun _ => (1 : Real)) := by
      funext t
      rw [congrFun (threshold_difference_of_le a b hab) t]
      exact congrFun (interval_indicator_abs a b) t
    rw [heq, hinterval,
      interval_indicator_integral a b hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  case neg =>
    have hba : b <= a := le_of_not_ge hab
    have hinterval : (fun t => |threshold a t - threshold b t|) =
        (Set.Ico b a).indicator (fun _ => (1 : Real)) := by
      funext t
      rw [congrFun (threshold_difference_of_le b a hba) t]
      exact congrFun (interval_indicator_abs b a) t
    rw [hinterval,
      interval_indicator_integral b a hba, abs_of_nonneg (sub_nonneg.mpr hba)]

theorem binary_disagreement (a b : Real)
    (ha : Or (a = 0) (a = 1)) (hb : Or (b = 0) (b = 1)) :
    |a - b| = a + b - 2 * a * b := by
  rcases ha with ha | ha
  all_goals rcases hb with hb | hb
  all_goals subst a; subst b; norm_num

theorem weighted_binary_disagreement {Index : Type*} [Fintype Index]
    (q f : Index -> Real) (hq : Finset.sum Finset.univ q = 1)
    (hf : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => q i * q j * |f i - f j|)) = 2 * p * (1 - p) := by
  dsimp only
  let p := Finset.sum Finset.univ (fun i => q i * f i)
  change Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => q i * q j * |f i - f j|)) = 2 * p * (1 - p)
  have hrow (i : Index) :
      Finset.sum Finset.univ (fun j => q i * q j * |f i - f j|) =
        q i * f i + q i * p - (2 * p) * (q i * f i) := by
    have hterm (j : Index) :
        q i * q j * |f i - f j| =
          (q i * f i) * q j + q i * (q j * f j) -
            (2 * q i * f i) * (q j * f j) := by
      rw [binary_disagreement (f i) (f j) (hf i) (hf j)]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [<- Finset.mul_sum, <- Finset.mul_sum, <- Finset.mul_sum, hq]
    change (q i * f i) * 1 + q i * p - (2 * q i * f i) * p =
      q i * f i + q i * p - (2 * p) * (q i * f i)
    ring
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [<- Finset.sum_mul, <- Finset.mul_sum, hq]
  change p + 1 * p - (2 * p) * p = 2 * p * (1 - p)
  ring

/- Finite-law version of equation gini. The double weighted sum is exactly
the expectation for two independent draws from the same labeled finite law.
No positivity is needed for this algebraic identity; probability laws satisfy
the additional nonnegativity requirement when using it as an expectation. -/

theorem finite_gini {Index : Type*} [Fintype Index]
    (q height : Index -> Real) (hq : Finset.sum Finset.univ q = 1) :
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => q i * q j * |height i - height j|)) =
        2 * integral volume (fun t =>
          (Finset.sum Finset.univ (fun i => q i * threshold (height i) t)) *
          (1 - Finset.sum Finset.univ (fun i => q i * threshold (height i) t))) := by
  have hpoint (t : Real) :=
    weighted_binary_disagreement q (fun i => threshold (height i) t) hq
      (fun i => threshold_values (height i) t)
  dsimp only at hpoint
  have hinner (i : Index) : Integrable (fun t =>
      Finset.sum Finset.univ (fun j =>
        q i * q j * |threshold (height i) t - threshold (height j) t|)) volume :=
    integrable_finsetSum Finset.univ (fun j _ =>
      (threshold_difference_integrable (height i) (height j)).abs.const_mul (q i * q j))
  calc
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => q i * q j * |height i - height j|)) =
      integral volume (fun t => Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j =>
          q i * q j * |threshold (height i) t - threshold (height j) t|))) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hinner i)]
      congr 1
      funext i
      rw [integral_finsetSum Finset.univ (fun j _ =>
        (threshold_difference_integrable (height i) (height j)).abs.const_mul (q i * q j))]
      simp only [integral_const_mul, threshold_difference_abs_integral]
    _ = 2 * integral volume (fun t =>
          (Finset.sum Finset.univ (fun i => q i * threshold (height i) t)) *
          (1 - Finset.sum Finset.univ (fun i => q i * threshold (height i) t))) := by
      simp_rw [hpoint]
      simp only [mul_assoc, integral_const_mul]

theorem threshold_as_indicator (t : Real) :
    (fun a => threshold a t) = (Set.Ioi t).indicator (fun _ => (1 : Real)) := by
  classical
  funext a
  simp [threshold, Set.indicator, Set.mem_Ioi]

theorem threshold_integrable (mu : Measure Real) [IsFiniteMeasure mu] (t : Real) :
    Integrable (fun a => threshold a t) mu := by
  rw [threshold_as_indicator]
  exact (integrable_const (1 : Real)).indicator measurableSet_Ioi

noncomputable def tailProbability (mu : Measure Real) (t : Real) : Real :=
  integral mu (fun a => threshold a t)

theorem tailProbability_eq_mass (mu : Measure Real) (t : Real) :
    tailProbability mu t = mu.real (Set.Ioi t) := by
  unfold tailProbability
  rw [threshold_as_indicator, integral_indicator_const 1 measurableSet_Ioi]
  simp [smul_eq_mul]

theorem threshold_joint_measurable {Omega : Type*} [MeasurableSpace Omega]
    (a t : Omega -> Real) (ha : Measurable a) (ht : Measurable t) :
    Measurable (fun x => threshold (a x) (t x)) := by
  classical
  exact Measurable.ite (measurableSet_lt ht ha) measurable_const measurable_const

theorem iid_threshold_disagreement (mu : Measure Real) [IsProbabilityMeasure mu]
    (t : Real) :
    integral (mu.prod mu) (fun z => |threshold z.1 t - threshold z.2 t|) =
      2 * tailProbability mu t * (1 - tailProbability mu t) := by
  let f : Real -> Real := fun a => threshold a t
  let p := tailProbability mu t
  have hf : Integrable f mu := threshold_integrable mu t
  have hpair : Integrable (fun z : Prod Real Real => |f z.1 - f z.2|)
      (mu.prod mu) := ((hf.comp_fst mu).sub (hf.comp_snd mu)).abs
  change integral (mu.prod mu) (fun z => |f z.1 - f z.2|) = 2 * p * (1 - p)
  rw [integral_prod _ hpair]
  have hrow (a : Real) :
      integral mu (fun b => |f a - f b|) = f a + p - (2 * p) * f a := by
    have heq : (fun b => |f a - f b|) =
        (fun b => f a + f b - (2 * f a) * f b) := by
      funext b
      exact binary_disagreement (f a) (f b)
        (threshold_values a t) (threshold_values b t)
    rw [heq, integral_sub (f := fun b => f a + f b) (g := fun b => (2 * f a) * f b)
        ((integrable_const (f a)).add hf) (hf.const_mul (2 * f a)),
      integral_add (f := fun _ => f a) (g := f) (integrable_const (f a)) hf,
      integral_const, integral_const_mul]
    change mu.real Set.univ * f a + p - (2 * f a) * p = f a + p - (2 * p) * f a
    rw [probReal_univ]
    ring
  simp_rw [hrow]
  rw [integral_sub (f := fun a => f a + p) (g := fun a => (2 * p) * f a)
      (hf.add (integrable_const p)) (hf.const_mul (2 * p)),
    integral_add (f := f) (g := fun _ => p) hf (integrable_const p),
    integral_const, integral_const_mul]
  change p + mu.real Set.univ * p - (2 * p) * p = 2 * p * (1 - p)
  rw [probReal_univ]
  ring

/- Equation gini for an arbitrary height law, with the independent copy
represented by the product probability measure. The finite first absolute
moment appears as integrability of the identity function. -/

theorem gini (mu : Measure Real) [IsProbabilityMeasure mu]
    (hfirst : Integrable (fun a : Real => a) mu) :
    integral (mu.prod mu) (fun z => |z.1 - z.2|) =
      2 * integral volume (fun t => tailProbability mu t * (1 - tailProbability mu t)) := by
  let H : Prod (Prod Real Real) Real -> Real := fun z =>
    |threshold z.1.1 z.2 - threshold z.1.2 z.2|
  have hHmeas : Measurable H :=
    continuous_abs.measurable.comp
    ((threshold_joint_measurable (fun z : Prod (Prod Real Real) Real => z.1.1) (fun z => z.2)
      measurable_fst.fst measurable_snd).sub
     (threshold_joint_measurable (fun z : Prod (Prod Real Real) Real => z.1.2) (fun z => z.2)
      measurable_fst.snd measurable_snd))
  have hdist : Integrable (fun z : Prod Real Real => |z.1 - z.2|) (mu.prod mu) :=
    ((hfirst.comp_fst mu).sub (hfirst.comp_snd mu)).abs
  have hH : Integrable H ((mu.prod mu).prod volume) := by
    apply (integrable_prod_iff hHmeas.aestronglyMeasurable).mpr
    constructor
    case left =>
      exact Filter.Eventually.of_forall (fun z =>
        (threshold_difference_integrable z.1 z.2).abs)
    case right =>
      have heq : (fun z : Prod Real Real => integral volume (fun t =>
          norm (H (z, t)))) = (fun z => |z.1 - z.2|) := by
        funext z
        simp only [H, Real.norm_eq_abs, abs_abs, threshold_difference_abs_integral]
      rw [heq]
      exact hdist
  calc
    integral (mu.prod mu) (fun z => |z.1 - z.2|) =
      integral (mu.prod mu) (fun z => integral volume (fun t => H (z, t))) := by
      congr 1
      funext z
      exact (threshold_difference_abs_integral z.1 z.2).symm
    _ = integral volume (fun t => integral (mu.prod mu) (fun z => H (z, t))) :=
      integral_integral_swap hH
    _ = 2 * integral volume (fun t =>
        tailProbability mu t * (1 - tailProbability mu t)) := by
      simp only [H, iid_threshold_disagreement]
      simp only [mul_assoc, integral_const_mul]

theorem tailVariance_integrable (mu : Measure Real) [IsProbabilityMeasure mu]
    (hfirst : Integrable (fun a : Real => a) mu) :
    Integrable (fun t => tailProbability mu t * (1 - tailProbability mu t)) volume := by
  let H : Prod (Prod Real Real) Real -> Real := fun z =>
    |threshold z.1.1 z.2 - threshold z.1.2 z.2|
  have hHmeas : Measurable H :=
    continuous_abs.measurable.comp
    ((threshold_joint_measurable (fun z : Prod (Prod Real Real) Real => z.1.1) (fun z => z.2)
      measurable_fst.fst measurable_snd).sub
     (threshold_joint_measurable (fun z : Prod (Prod Real Real) Real => z.1.2) (fun z => z.2)
      measurable_fst.snd measurable_snd))
  have hdist : Integrable (fun z : Prod Real Real => |z.1 - z.2|) (mu.prod mu) :=
    ((hfirst.comp_fst mu).sub (hfirst.comp_snd mu)).abs
  have hH : Integrable H ((mu.prod mu).prod volume) := by
    apply (integrable_prod_iff hHmeas.aestronglyMeasurable).mpr
    constructor
    case left =>
      exact Filter.Eventually.of_forall (fun z =>
        (threshold_difference_integrable z.1 z.2).abs)
    case right =>
      have heq : (fun z : Prod Real Real => integral volume (fun t =>
          norm (H (z, t)))) = (fun z => |z.1 - z.2|) := by
        funext z
        simp only [H, Real.norm_eq_abs, abs_abs, threshold_difference_abs_integral]
      rw [heq]
      exact hdist
  have htwo : Integrable (fun t => integral (mu.prod mu) (fun z => H (z, t))) volume :=
    hH.integral_prod_right
  have heq : (fun t => integral (mu.prod mu) (fun z => H (z, t))) =
      (fun t => 2 * (tailProbability mu t * (1 - tailProbability mu t))) := by
    funext t
    simp only [H, iid_threshold_disagreement, mul_assoc]
  rw [heq] at htwo
  have hscaled := htwo.const_mul (1 / 2 : Real)
  convert hscaled using 1
  funext t
  ring

theorem tailProbability_map {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (T : Omega -> Real) (hT : Measurable T) (t : Real) :
    tailProbability (P.map T) t = P.real {w | t < T w} := by
  rw [tailProbability_eq_mass, map_measureReal_apply hT measurableSet_Ioi]
  rfl

/- The explicit bridge from a height law to the paper's random-variable
notation. The independent copy lives on the second factor of P.prod P. -/

theorem gini_random_variable {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (T : Omega -> Real) (hT : Measurable T) (hfirst : Integrable T P) :
    integral (P.prod P) (fun z => |T z.1 - T z.2|) =
      2 * integral volume (fun t =>
        P.real {w | t < T w} * (1 - P.real {w | t < T w})) := by
  have : IsProbabilityMeasure (P.map T) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hmapfirst : Integrable (fun a : Real => a) (P.map T) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hT.aemeasurable).mpr hfirst
  have hdistmeas : Measurable (fun z : Prod Real Real => |z.1 - z.2|) :=
    continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
  calc
    integral (P.prod P) (fun z => |T z.1 - T z.2|) =
      integral ((P.map T).prod (P.map T)) (fun z => |z.1 - z.2|) := by
        rw [Measure.map_prod_map P P hT hT,
          integral_map (hT.prodMap hT).aemeasurable hdistmeas.aestronglyMeasurable]
        rfl
    _ = 2 * integral volume (fun t =>
        P.real {w | t < T w} * (1 - P.real {w | t < T w})) := by
      rw [gini (P.map T) hmapfirst]
      simp_rw [tailProbability_map P T hT]

/- Conditional interface for the paper's arbitrary-height lifting step.
The levelwise Bernoulli inequality is a named, explicit hypothesis. This
declaration does not prove that central Bernoulli inequality. The
other two integral hypotheses are the joint threshold integrability and
the absolute determinant integrability supplied by the sample-law analysis.
The coefficient mass L is constant after taking expectation; it need not be
independent of the heights in the sampled configuration. -/

theorem lift_levelwise_gate {Omega Index : Type*}
    [MeasurableSpace Omega] [Fintype Index]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (c height : Omega -> Index -> Real) (L : Real)
    (hzero : forall w, Finset.sum Finset.univ (c w) = 0)
    (hfirst : Integrable (fun a : Real => a) mu)
    (hmain : Integrable (fun w =>
      |Finset.sum Finset.univ (fun i => c w i * height w i)|) P)
    (hF : Integrable (fun z : Prod Omega Real =>
      |Finset.sum Finset.univ (fun i => c z.1 i * threshold (height z.1 i) z.2)|)
      (P.prod volume))
    (hlevel : forall t, integral P (fun w =>
      |Finset.sum Finset.univ (fun i => c w i * threshold (height w i) t)|) <=
      2 * tailProbability mu t * (1 - tailProbability mu t) * L) :
    integral P (fun w => |Finset.sum Finset.univ (fun i => c w i * height w i)|) <=
      L * integral (mu.prod mu) (fun z => |z.1 - z.2|) := by
  have hmajor : Integrable (fun t =>
      2 * tailProbability mu t * (1 - tailProbability mu t) * L) volume := by
    have hscaled := (tailVariance_integrable mu hfirst).const_mul (2 * L)
    convert hscaled using 1
    funext t
    ring
  calc
    integral P (fun w => |Finset.sum Finset.univ (fun i => c w i * height w i)|) <=
      integral P (fun w => thresholdCost (c w) (height w)) :=
        integral_mono hmain hF.integral_prod_left
          (fun w => threshold_bound_left (c w) (height w) (hzero w))
    _ = integral volume (fun t => integral P (fun w =>
        |Finset.sum Finset.univ (fun i => c w i * threshold (height w i) t)|)) :=
      integral_integral_swap hF
    _ <= integral volume (fun t =>
        2 * tailProbability mu t * (1 - tailProbability mu t) * L) :=
      integral_mono hF.integral_prod_right hmajor hlevel
    _ = L * integral (mu.prod mu) (fun z => |z.1 - z.2|) := by
      have heq : (fun t =>
          2 * tailProbability mu t * (1 - tailProbability mu t) * L) =
          (fun t => (2 * L) * (tailProbability mu t * (1 - tailProbability mu t))) := by
        funext t
        ring
      rw [heq, integral_const_mul, gini mu hfirst]
      ring

theorem coefficient_centeredThreshold_integrable {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (c height : Omega -> Real) (hc : Measurable c) (hheight : Measurable height)
    (hproduct : Integrable (fun w => |c w| * |height w|) P) :
    Integrable (fun z : Prod Omega Real =>
      c z.1 * centeredThreshold (height z.1) z.2) (P.prod volume) := by
  have hmeas : Measurable (fun z : Prod Omega Real =>
      c z.1 * centeredThreshold (height z.1) z.2) :=
    (hc.comp measurable_fst).mul
      ((threshold_joint_measurable (fun z : Prod Omega Real => height z.1)
          (fun z => z.2) (hheight.comp measurable_fst) measurable_snd).sub
       (threshold_joint_measurable (fun _ : Prod Omega Real => (0 : Real))
          (fun z => z.2) measurable_const measurable_snd))
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  case left =>
    exact Filter.Eventually.of_forall (fun w =>
      (centeredThreshold_integrable (height w)).const_mul (c w))
  case right =>
    have heq : (fun w => integral volume (fun t =>
        norm (c w * centeredThreshold (height w) t))) =
        (fun w => |c w| * |height w|) := by
      funext w
      simp only [Real.norm_eq_abs, abs_mul, integral_const_mul, centeredThreshold_abs_integral]
    rw [heq]
    exact hproduct

theorem joint_threshold_integrable {Omega Index : Type*}
    [MeasurableSpace Omega] [Fintype Index]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (c height : Omega -> Index -> Real)
    (hzero : forall w, Finset.sum Finset.univ (c w) = 0)
    (hc : forall i, Measurable (fun w => c w i))
    (hheight : forall i, Measurable (fun w => height w i))
    (hproduct : forall i, Integrable (fun w => |c w i| * |height w i|) P) :
    Integrable (fun z : Prod Omega Real =>
      |Finset.sum Finset.univ (fun i => c z.1 i * threshold (height z.1 i) z.2)|)
      (P.prod volume) := by
  have heq : (fun z : Prod Omega Real =>
      |Finset.sum Finset.univ (fun i => c z.1 i * threshold (height z.1 i) z.2)|) =
      (fun z => |Finset.sum Finset.univ (fun i =>
        c z.1 i * centeredThreshold (height z.1 i) z.2)|) := by
    funext z
    rw [cofactor_threshold_centering (c z.1) (height z.1) (hzero z.1)]
  rw [heq]
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    coefficient_centeredThreshold_integrable P (fun w => c w i) (fun w => height w i)
      (hc i) (hheight i) (hproduct i))).abs

theorem coefficient_height_sum_integrable {Omega Index : Type*}
    [MeasurableSpace Omega] [Fintype Index] (P : Measure Omega)
    (c height : Omega -> Index -> Real)
    (hc : forall i, Measurable (fun w => c w i))
    (hheight : forall i, Measurable (fun w => height w i))
    (hproduct : forall i, Integrable (fun w => |c w i| * |height w i|) P) :
    Integrable (fun w => |Finset.sum Finset.univ (fun i => c w i * height w i)|) P := by
  have hterm (i : Index) : Integrable (fun w => c w i * height w i) P := by
    apply (integrable_norm_iff ((hc i).mul (hheight i)).aestronglyMeasurable).mp
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using hproduct i
  exact (integrable_finsetSum Finset.univ (fun i _ => hterm i)).abs

theorem lift_levelwise_gate_of_product_moments {Omega Index : Type*}
    [MeasurableSpace Omega] [Fintype Index]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (c height : Omega -> Index -> Real) (L : Real)
    (hzero : forall w, Finset.sum Finset.univ (c w) = 0)
    (hfirst : Integrable (fun a : Real => a) mu)
    (hc : forall i, Measurable (fun w => c w i))
    (hheight : forall i, Measurable (fun w => height w i))
    (hproduct : forall i, Integrable (fun w => |c w i| * |height w i|) P)
    (hlevel : forall t, integral P (fun w =>
      |Finset.sum Finset.univ (fun i => c w i * threshold (height w i) t)|) <=
      2 * tailProbability mu t * (1 - tailProbability mu t) * L) :
    integral P (fun w => |Finset.sum Finset.univ (fun i => c w i * height w i)|) <=
      L * integral (mu.prod mu) (fun z => |z.1 - z.2|) :=
  lift_levelwise_gate P mu c height L hzero hfirst
    (coefficient_height_sum_integrable P c height hc hheight hproduct)
    (joint_threshold_integrable P c height hzero hc hheight hproduct) hlevel

theorem lift_thresholdCost_levelwise_gate {Omega Index : Type*}
    [MeasurableSpace Omega] [Fintype Index]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (c height : Omega -> Index -> Real) (L : Real)
    (hfirst : Integrable (fun a : Real => a) mu)
    (hF : Integrable (fun z : Prod Omega Real =>
      |Finset.sum Finset.univ (fun i => c z.1 i * threshold (height z.1 i) z.2)|)
      (P.prod volume))
    (hlevel : forall t, integral P (fun w =>
      |Finset.sum Finset.univ (fun i => c w i * threshold (height w i) t)|) <=
      2 * tailProbability mu t * (1 - tailProbability mu t) * L) :
    integral P (fun w => thresholdCost (c w) (height w)) <=
      L * integral (mu.prod mu) (fun z => |z.1 - z.2|) := by
  have hmajor : Integrable (fun t =>
      2 * tailProbability mu t * (1 - tailProbability mu t) * L) volume := by
    have hscaled := (tailVariance_integrable mu hfirst).const_mul (2 * L)
    convert hscaled using 1
    funext t
    ring
  calc
    integral P (fun w => thresholdCost (c w) (height w)) =
      integral volume (fun t => integral P (fun w =>
        |Finset.sum Finset.univ (fun i => c w i * threshold (height w i) t)|)) :=
        integral_integral_swap hF
    _ <= integral volume (fun t =>
        2 * tailProbability mu t * (1 - tailProbability mu t) * L) :=
      integral_mono hF.integral_prod_right hmajor hlevel
    _ = L * integral (mu.prod mu) (fun z => |z.1 - z.2|) := by
      have heq : (fun t =>
          2 * tailProbability mu t * (1 - tailProbability mu t) * L) =
          (fun t => (2 * L) * (tailProbability mu t * (1 - tailProbability mu t))) := by
        funext t
        ring
      rw [heq, integral_const_mul, gini mu hfirst]
      ring

theorem thresholdCost_lipschitz_coefficients {Index : Type*} [Fintype Index]
    (c d height : Index -> Real)
    (hc : Finset.sum Finset.univ c = 0) (hd : Finset.sum Finset.univ d = 0) :
    |thresholdCost c height - thresholdCost d height| <=
      Finset.sum Finset.univ (fun i => |c i - d i| * |height i|) := by
  have hci := threshold_sum_integrable c height hc
  have hdi := threshold_sum_integrable d height hd
  have hzero : Finset.sum Finset.univ (fun i => c i - d i) = 0 := by
    rw [Finset.sum_sub_distrib, hc, hd]
    simp
  have hdiff (t : Real) :
      Finset.sum Finset.univ (fun i => c i * threshold (height i) t) -
        Finset.sum Finset.univ (fun i => d i * threshold (height i) t) =
      Finset.sum Finset.univ (fun i => (c i - d i) * threshold (height i) t) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  calc
    |thresholdCost c height - thresholdCost d height| =
      |integral volume (fun t =>
        |Finset.sum Finset.univ (fun i => c i * threshold (height i) t)| -
          |Finset.sum Finset.univ (fun i => d i * threshold (height i) t)|)| := by
      unfold thresholdCost
      rw [integral_sub (f := fun t =>
        |Finset.sum Finset.univ (fun i => c i * threshold (height i) t)|)
        (g := fun t => |Finset.sum Finset.univ (fun i => d i * threshold (height i) t)|)
        hci.abs hdi.abs]
    _ <= integral volume (fun t =>
        abs (|Finset.sum Finset.univ (fun i => c i * threshold (height i) t)| -
          |Finset.sum Finset.univ (fun i => d i * threshold (height i) t)|)) :=
      abs_integral_le_integral_abs
    _ <= integral volume (fun t =>
        |Finset.sum Finset.univ (fun i => c i * threshold (height i) t) -
          Finset.sum Finset.univ (fun i => d i * threshold (height i) t)|) :=
      integral_mono (hci.abs.sub hdi.abs).abs (hci.sub hdi).abs
        (fun t => abs_abs_sub_abs_le_abs_sub _ _)
    _ = thresholdCost (fun i => c i - d i) height := by
      unfold thresholdCost
      simp_rw [hdiff]
    _ <= Finset.sum Finset.univ (fun i => |c i - d i| * |height i|) :=
      threshold_bound_right (fun i => c i - d i) height hzero

end Hypercube.Thresholds
