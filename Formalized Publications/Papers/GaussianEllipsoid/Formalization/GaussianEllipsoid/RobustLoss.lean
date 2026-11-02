/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.
Kernel-checked deterministic Section 4 lemmas. These do not assert a probability limit or
existence/measurability of the spectral minimizers.
-/
import GaussianEllipsoid.Huber
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

namespace GaussianEllipsoid

/-- Clearing a positive averaging denominator does not change the ridge factor. -/
theorem scale_mean_add_penalty {mass : Real} (hmass : Not (mass = 0))
    (total penalty : Real) :
    mass * (total / mass + penalty) = total + mass * penalty := by
  field_simp [hmass]

/-- The scalar algebra obtained after multiplying the two objective comparisons.
Here headA/headB are the sums over all observations except the deleted one. -/
theorem full_deleted_loss_comparison_unscaled
    {n headA headB a b ridgeA ridgeB : Real}
    (hfull : headA + huber a + n * ridgeA <= headB + huber b + n * ridgeB)
    (hdeleted : headB + (n - 1) * ridgeB <= headA + (n - 1) * ridgeA) :
    huber a + ridgeA <= huber b + ridgeB := by
  nlinarith

/-- The exact normalized full/deleted minimizer comparison.
Only the two pathwise minimization inequalities are needed. -/
theorem full_deleted_loss_comparison
    {n headA headB a b ridgeA ridgeB : Real} (hn : 1 < n)
    (hfull : (headA + huber a) / n + ridgeA <=
      (headB + huber b) / n + ridgeB)
    (hdeleted : headB / (n - 1) + ridgeB <= headA / (n - 1) + ridgeA) :
    huber a + ridgeA <= huber b + ridgeB := by
  have hn0 : 0 < n := by linarith
  have hnm1 : 0 < n - 1 := by linarith
  have hf := mul_le_mul_of_nonneg_left hfull hn0.le
  have hd := mul_le_mul_of_nonneg_left hdeleted hnm1.le
  simp only [scale_mean_add_penalty (ne_of_gt hn0)] at hf
  simp only [scale_mean_add_penalty (ne_of_gt hnm1)] at hd
  exact full_deleted_loss_comparison_unscaled hf hd

/-- Dropping a nonnegative full-sample ridge gives the stated additive loss error. -/
theorem huber_comparison_of_ridge_bounds
    {a b ridgeA ridgeB error : Real}
    (hcomparison : huber a + ridgeA <= huber b + ridgeB)
    (hA : 0 <= ridgeA) (hB : ridgeB <= error) :
    huber a <= huber b + error := by
  linarith

/-- Deterministic full/deleted residual domination with a Huber-sized ridge bound. -/
theorem full_deleted_abs_comparison
    {n headA headB a b ridgeA ridgeB e : Real} (hn : 1 < n)
    (hfull : (headA + huber a) / n + ridgeA <=
      (headB + huber b) / n + ridgeB)
    (hdeleted : headB / (n - 1) + ridgeB <= headA / (n - 1) + ridgeA)
    (hA : 0 <= ridgeA) (hB : ridgeB <= huber e) (he : 0 <= e) :
    |a| <= |b| + e := by
  apply abs_le_add_of_huber_le he
  exact huber_comparison_of_ridge_bounds
    (full_deleted_loss_comparison hn hfull hdeleted) hA hB

/-- The finite-dimensional specialization e=b0/d from the manuscript. -/
theorem full_deleted_abs_comparison_div
    {n headA headB a b ridgeA ridgeB b0 d : Real} (hn : 1 < n)
    (hfull : (headA + huber a) / n + ridgeA <=
      (headB + huber b) / n + ridgeB)
    (hdeleted : headB / (n - 1) + ridgeB <= headA / (n - 1) + ridgeA)
    (hA : 0 <= ridgeA) (hB : ridgeB <= b0 ^ 2 / (2 * d ^ 2))
    (hb0 : 0 <= b0) (hd : 0 < d) (hsmall : b0 / d <= 1) :
    |a| <= |b| + b0 / d := by
  apply abs_le_add_div_of_huber_le hb0 hd hsmall
  exact huber_comparison_of_ridge_bounds
    (full_deleted_loss_comparison hn hfull hdeleted) hA hB

/-- Pointwise transfer of a strict squared tail to the deleted residual. -/
theorem tailSquare_le_of_abs_le_add {a b e M : Real}
    (he : 0 <= e) (hM : 2 * e <= M) (hab : |a| <= |b| + e) :
    tailSquare a M <= 2 * tailSquare b (M / 2) + 2 * e ^ 2 := by
  by_cases ha : M < |a|
  next =>
    have hb : M / 2 < |b| := by linarith
    simp only [tailSquare, ite_eq_left ha, ite_eq_left hb]
    have hprod := mul_nonneg (sub_nonneg.mpr hab)
      (show 0 <= |b| + e + |a| by positivity)
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|b| - e)]
  next =>
    simp only [tailSquare, ite_eq_right ha]
    change 0 <= 2 * tailSquare b (M / 2) + 2 * e ^ 2
    have hb := tailSquare_nonneg b (M / 2)
    nlinarith [sq_nonneg e]

/-- The arithmetic mean over a finite index type; empty types give zero. -/
def empiricalAverage {Index : Type*} [Fintype Index] (f : Index -> Real) : Real :=
  (Finset.univ.sum f) / (Fintype.card Index : Real)

/-- The finite empirical Huber risk. -/
def empiricalHuber {Index : Type*} [Fintype Index] (a : Index -> Real) : Real :=
  empiricalAverage (fun j => huber (a j))

theorem empiricalAverage_nonneg {Index : Type*} [Fintype Index]
    {f : Index -> Real} (hf : forall j, 0 <= f j) : 0 <= empiricalAverage f := by
  apply div_nonneg
  next =>
    exact Finset.sum_nonneg (fun j _ => hf j)
  next =>
    positivity

theorem empiricalAverage_mono {Index : Type*} [Fintype Index]
    {f g : Index -> Real} (hfg : forall j, f j <= g j) :
    empiricalAverage f <= empiricalAverage g := by
  apply div_le_div_of_nonneg_right
  next =>
    exact Finset.sum_le_sum (fun j _ => hfg j)
  next =>
    positivity

theorem empiricalAverage_add {Index : Type*} [Fintype Index]
    (f g : Index -> Real) :
    empiricalAverage (fun j => f j + g j) = empiricalAverage f + empiricalAverage g := by
  simp only [empiricalAverage, Finset.sum_add_distrib, add_div]

theorem empiricalAverage_mul {Index : Type*} [Fintype Index]
    (c : Real) (f : Index -> Real) :
    empiricalAverage (fun j => c * f j) = c * empiricalAverage f := by
  unfold empiricalAverage
  rw [(Finset.mul_sum Finset.univ f c).symm]
  ring

theorem empiricalAverage_const {Index : Type*} [Fintype Index] [Nonempty Index]
    (c : Real) : empiricalAverage (fun _ : Index => c) = c := by
  have hn : Not ((Fintype.card Index : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [empiricalAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]

/-- The paper's bounded-residual contribution, averaged over the sample. -/
theorem empirical_truncatedSquare_le {Index : Type*} [Fintype Index]
    (a : Index -> Real) {M : Real} (hM : 1 <= M) :
    empiricalAverage (fun j => truncatedSquare (a j) M) <= 2 * M * empiricalHuber a := by
  calc
    empiricalAverage (fun j => truncatedSquare (a j) M)
        <= empiricalAverage (fun j => (2 * M) * huber (a j)) :=
      empiricalAverage_mono (fun j => truncatedSquare_le_two_mul_huber (a j) hM)
    _ = 2 * M * empiricalHuber a := by
      rw [empiricalAverage_mul]
      rfl

/-- The exact empirical squared-tail transfer in the robust-loss proof. -/
theorem empirical_tailSquare_transfer {Index : Type*} [Fintype Index] [Nonempty Index]
    {a b : Index -> Real} {e M : Real} (he : 0 <= e) (hM : 2 * e <= M)
    (hab : forall j, |a j| <= |b j| + e) :
    empiricalAverage (fun j => tailSquare (a j) M) <=
      2 * empiricalAverage (fun j => tailSquare (b j) (M / 2)) + 2 * e ^ 2 := by
  calc
    empiricalAverage (fun j => tailSquare (a j) M)
        <= empiricalAverage (fun j => 2 * tailSquare (b j) (M / 2) + 2 * e ^ 2) :=
      empiricalAverage_mono (fun j => tailSquare_le_of_abs_le_add he hM (hab j))
    _ = 2 * empiricalAverage (fun j => tailSquare (b j) (M / 2)) + 2 * e ^ 2 := by
      rw [empiricalAverage_add, empiricalAverage_mul, empiricalAverage_const]

/-- Decomposition at the exact weak/strict cutoff pair. -/
theorem empirical_square_decomposition {Index : Type*} [Fintype Index]
    (a : Index -> Real) (M : Real) :
    empiricalAverage (fun j => (a j) ^ 2) =
      empiricalAverage (fun j => truncatedSquare (a j) M) +
      empiricalAverage (fun j => tailSquare (a j) M) := by
  rw [(empiricalAverage_add (fun j => truncatedSquare (a j) M)
    (fun j => tailSquare (a j) M)).symm]
  congr 1
  funext j
  exact sq_eq_truncatedSquare_add_tailSquare (a j) M

/-- The finite inequality behind the uniform-integrability plus truncated-risk step. -/
theorem empirical_square_le_huber_add_deleted_tail
    {Index : Type*} [Fintype Index] [Nonempty Index]
    {a b : Index -> Real} {e M : Real} (he : 0 <= e)
    (hM : 1 <= M) (heM : 2 * e <= M)
    (hab : forall j, |a j| <= |b j| + e) :
    empiricalAverage (fun j => (a j) ^ 2) <=
      2 * M * empiricalHuber a +
      2 * empiricalAverage (fun j => tailSquare (b j) (M / 2)) + 2 * e ^ 2 := by
  rw [empirical_square_decomposition a M]
  have htrunc := empirical_truncatedSquare_le a hM
  have htail := empirical_tailSquare_transfer he heM hab
  linarith

/-- Averaging the pointwise L1-Huber estimate, before the separate Jensen step. -/
theorem empirical_abs_le_sqrt_huber_add_huber {Index : Type*} [Fintype Index]
    (a : Index -> Real) :
    empiricalAverage (fun j => |a j|) <=
      empiricalAverage (fun j => Real.sqrt (2 * huber (a j))) + 2 * empiricalHuber a := by
  calc
    empiricalAverage (fun j => |a j|) <=
        empiricalAverage (fun j => Real.sqrt (2 * huber (a j)) + 2 * huber (a j)) :=
      empiricalAverage_mono (fun j => abs_le_sqrt_two_huber_add_two_huber (a j))
    _ = empiricalAverage (fun j => Real.sqrt (2 * huber (a j))) + 2 * empiricalHuber a := by
      rw [empiricalAverage_add, empiricalAverage_mul]
      rfl


/-- Finite Cauchy-Schwarz, normalized by the actual sample cardinality. -/
theorem empiricalAverage_sq_le_average_sq {Index : Type*}
    [Fintype Index] [Nonempty Index] (f : Index -> Real) :
    (empiricalAverage f) ^ 2 <= empiricalAverage (fun j => (f j) ^ 2) := by
  have hn : (0 : Real) < (Fintype.card Index : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Index)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : Real))
  have hsum : (Finset.univ.sum f) ^ 2 <=
      (Fintype.card Index : Real) * Finset.univ.sum (fun j => (f j) ^ 2) := by
    simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_comm] using hCS
  unfold empiricalAverage
  calc
    (Finset.univ.sum f / (Fintype.card Index : Real)) ^ 2
        = (Finset.univ.sum f) ^ 2 / (Fintype.card Index : Real) ^ 2 := by ring
    _ <= ((Fintype.card Index : Real) * Finset.univ.sum (fun j => (f j) ^ 2)) /
        (Fintype.card Index : Real) ^ 2 :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = Finset.univ.sum (fun j => (f j) ^ 2) / (Fintype.card Index : Real) := by
      field_simp [ne_of_gt hn]

/-- Finite Jensen for the square root, derived here from Cauchy-Schwarz. -/
theorem empiricalAverage_sqrt_le_sqrt_average {Index : Type*}
    [Fintype Index] [Nonempty Index] {f : Index -> Real}
    (hf : forall j, 0 <= f j) :
    empiricalAverage (fun j => Real.sqrt (f j)) <= Real.sqrt (empiricalAverage f) := by
  apply Real.le_sqrt_of_sq_le
  have hCS := empiricalAverage_sq_le_average_sq (fun j => Real.sqrt (f j))
  have heq : (fun j => (Real.sqrt (f j)) ^ 2) = f := by
    funext j
    exact Real.sq_sqrt (hf j)
  rw [heq] at hCS
  exact hCS

/-- The exact finite empirical absolute-residual estimate used in Section 4. -/
theorem empirical_abs_le_sqrt_two_risk_add_two_risk {Index : Type*}
    [Fintype Index] [Nonempty Index] (a : Index -> Real) :
    empiricalAverage (fun j => |a j|) <=
      Real.sqrt (2 * empiricalHuber a) + 2 * empiricalHuber a := by
  have hJ := empiricalAverage_sqrt_le_sqrt_average
    (fun j => mul_nonneg (show (0 : Real) <= 2 by norm_num) (huber_nonneg (a j)))
  rw [empiricalAverage_mul] at hJ
  change empiricalAverage (fun j => Real.sqrt (2 * huber (a j))) <=
    Real.sqrt (2 * empiricalHuber a) at hJ
  have hpoint := empirical_abs_le_sqrt_huber_add_huber a
  linarith

/-- Substituting a pathwise risk upper bound into the empirical L1 estimate. -/
theorem empirical_abs_le_of_huber_le {Index : Type*}
    [Fintype Index] [Nonempty Index] {a : Index -> Real} {r : Real}
    (hr : empiricalHuber a <= r) :
    empiricalAverage (fun j => |a j|) <= Real.sqrt (2 * r) + 2 * r := by
  have hroot := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hr (show (0 : Real) <= 2 by norm_num))
  have habs := empirical_abs_le_sqrt_two_risk_add_two_risk a
  linarith

/-- The full finite-sample robust objective for an arbitrary parameter space. -/
def robustObjective {Index State : Type*} [Fintype Index]
    (res : State -> Index -> Real) (penalty : State -> Real) (S : State) : Real :=
  empiricalHuber (res S) + penalty S

/-- Delete exactly one observation and use the paper's denominator n-1. -/
def deletedRobustObjective {Index State : Type*} [Fintype Index] [DecidableEq Index]
    (res : State -> Index -> Real) (penalty : State -> Real) (j : Index) (S : State) : Real :=
  ((Finset.univ.erase j).sum (fun i => huber (res S i))) /
    ((Fintype.card Index : Real) - 1) + penalty S

/-- Explicit finite-sample bridge: paired minimizer comparisons imply the
paper's single-observation loss-plus-ridge comparison. -/
theorem full_deleted_finite_comparison
    {Index State : Type*} [Fintype Index] [DecidableEq Index]
    (res : State -> Index -> Real) (penalty : State -> Real)
    {Sstar Sdeleted : State} (j : Index) (hn : 1 < Fintype.card Index)
    (hfull : robustObjective res penalty Sstar <= robustObjective res penalty Sdeleted)
    (hdeleted : deletedRobustObjective res penalty j Sdeleted <=
      deletedRobustObjective res penalty j Sstar) :
    huber (res Sstar j) + penalty Sstar <= huber (res Sdeleted j) + penalty Sdeleted := by
  have hnR : (1 : Real) < (Fintype.card Index : Real) := by exact_mod_cast hn
  have hsplitS := Finset.sum_erase_add Finset.univ
    (fun i => huber (res Sstar i)) (Finset.mem_univ j)
  have hsplitD := Finset.sum_erase_add Finset.univ
    (fun i => huber (res Sdeleted i)) (Finset.mem_univ j)
  unfold robustObjective empiricalHuber empiricalAverage at hfull
  rw [hsplitS.symm, hsplitD.symm] at hfull
  unfold deletedRobustObjective at hdeleted
  exact full_deleted_loss_comparison hnR hfull hdeleted


/-- The Huber empirical risk is bounded by the empirical absolute residual. -/
theorem empiricalHuber_le_empirical_abs {Index : Type*} [Fintype Index]
    (a : Index -> Real) : empiricalHuber a <= empiricalAverage (fun j => |a j|) := by
  exact empiricalAverage_mono (fun j => huber_le_abs (a j))

/-- Pathwise comparison with an approximate fit; the probability limit is separate. -/
theorem robust_risk_le_comparator_absolute_risk
    {Index State : Type*} [Fintype Index]
    (res : State -> Index -> Real) (penalty : State -> Real)
    {Sstar Scomparator : State}
    (hoptimal : robustObjective res penalty Sstar <= robustObjective res penalty Scomparator)
    (hpenalty : 0 <= penalty Sstar) :
    empiricalHuber (res Sstar) <=
      empiricalAverage (fun j => |res Scomparator j|) + penalty Scomparator := by
  have hcomp := empiricalHuber_le_empirical_abs (res Scomparator)
  unfold robustObjective at hoptimal
  linarith

/-- Removing one nonnegative Huber loss costs precisely n/(n-1).
The comparator may depend on the full sample: the argument is pathwise. -/
theorem deleted_objective_le_full_comparator
    {Index State : Type*} [Fintype Index] [DecidableEq Index]
    (res : State -> Index -> Real) (penalty : State -> Real)
    {Sdeleted Scomparator : State} (j : Index) (hn : 1 < Fintype.card Index)
    (hoptimal : deletedRobustObjective res penalty j Sdeleted <=
      deletedRobustObjective res penalty j Scomparator) :
    deletedRobustObjective res penalty j Sdeleted <=
      (Fintype.card Index : Real) / ((Fintype.card Index : Real) - 1) *
        empiricalHuber (res Scomparator) + penalty Scomparator := by
  have hnR : (1 : Real) < (Fintype.card Index : Real) := by exact_mod_cast hn
  have hn0 : (0 : Real) < (Fintype.card Index : Real) := by linarith
  have hnm1 : 0 < (Fintype.card Index : Real) - 1 := by linarith
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun i => huber (res Scomparator i)) (Finset.mem_univ j)
  have hhead : (Finset.univ.erase j).sum (fun i => huber (res Scomparator i)) <=
      Finset.univ.sum (fun i => huber (res Scomparator i)) := by
    linarith [huber_nonneg (res Scomparator j)]
  have hdiv := div_le_div_of_nonneg_right hhead hnm1.le
  have hscale :
      (Finset.univ.sum (fun i => huber (res Scomparator i))) /
        ((Fintype.card Index : Real) - 1) =
      (Fintype.card Index : Real) / ((Fintype.card Index : Real) - 1) *
        empiricalHuber (res Scomparator) := by
    unfold empiricalHuber empiricalAverage
    field_simp [ne_of_gt hn0, ne_of_gt hnm1]
  rw [hscale] at hdiv
  unfold deletedRobustObjective at hoptimal
  change ((Finset.univ.erase j).sum (fun i => huber (res Sdeleted i))) /
      ((Fintype.card Index : Real) - 1) + penalty Sdeleted <= _
  linarith


/-- Finite-type averages agree exactly with the paper's n-indexed sums. -/
theorem empiricalAverage_fin {n : Nat} (f : Fin n -> Real) :
    empiricalAverage f = (Finset.univ.sum f) / (n : Real) := by
  simp only [empiricalAverage, Fintype.card_fin]

/-- The paper's H_d(S) after substituting its residual vector. -/
theorem empiricalHuber_fin {n : Nat} (a : Fin n -> Real) :
    empiricalHuber a = (Finset.univ.sum (fun j => huber (a j))) / (n : Real) := by
  simp only [empiricalHuber, empiricalAverage, Fintype.card_fin]

end GaussianEllipsoid
