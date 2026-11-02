/-
Kernel-checked deterministic finite-sum, support-count, and scalar effective-support estimates.
These do not assert the random multiscale lower bound or existence of the record algorithm.
-/
import GaussianEllipsoid.Dyadic

noncomputable section

namespace GaussianEllipsoid
namespace Dyadic

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The repaired retained support lies in the union over its depth many offsets. -/
theorem retained_subset_offsets (bins : Nat -> Finset I) {group : Set Nat}
    {start depth : Nat} (hstart : forall t, t ∈ group -> start <= t) :
    retainedCoords bins group start depth ⊆
      (Finset.range depth).biUnion (fun j => bins (start + j)) := by
  classical
  intro i hi
  have hw := (mem_levelCoords _ _ _).mp hi
  let t := hw.choose
  have ht := hw.choose_spec
  have hlow := hstart t ht.1.1
  have hcut := ht.1.2
  have hoff : t - start ∈ Finset.range depth := Finset.mem_range.mpr (by omega)
  have heq : start + (t - start) = t := by omega
  exact Finset.mem_biUnion.mpr (Exists.intro (t - start)
    (And.intro hoff (by simpa only [heq] using ht.2)))

/-- Cardinality bound with a real cap, suitable for q times a record support size. -/
theorem retained_card_le (bins : Nat -> Finset I) {group : Set Nat}
    {start depth : Nat} {cap : Real}
    (hstart : forall t, t ∈ group -> start <= t)
    (hcap : forall j, j ∈ Finset.range depth -> ((bins (start + j)).card : Real) <= cap) :
    ((retainedCoords bins group start depth).card : Real) <= (depth : Real) * cap := by
  classical
  have hsub := Finset.card_le_card (retained_subset_offsets bins (start := start) (depth := depth) hstart)
  have hsum : ((Finset.range depth).biUnion (fun j => bins (start + j))).card <=
      (Finset.range depth).sum (fun j => (bins (start + j)).card) :=
    Finset.card_biUnion_le
  have hcast : ((retainedCoords bins group start depth).card : Real) <=
      (Finset.range depth).sum (fun j => ((bins (start + j)).card : Real)) := by
    exact_mod_cast (le_trans hsub hsum)
  calc
    ((retainedCoords bins group start depth).card : Real) <=
        (Finset.range depth).sum (fun j => ((bins (start + j)).card : Real)) := hcast
    _ <= (Finset.range depth).sum (fun _ => cap) := Finset.sum_le_sum hcap
    _ = (depth : Real) * cap := by simp

/-- Each offset bin is first tested for membership in the record's level group. -/
def offsetBin (bins : Nat -> Finset I) (group : Set Nat) (start j : Nat) : Finset I := by
  classical
  exact if start + j ∈ group then bins (start + j) else Finset.empty

/-- Exact finite-union representation, including the last possibly infinite level group. -/
theorem retained_eq_offset_union (bins : Nat -> Finset I) {group : Set Nat}
    {start depth : Nat} (hstart : forall t, t ∈ group -> start <= t) :
    retainedCoords bins group start depth =
      (Finset.range depth).biUnion (offsetBin bins group start) := by
  classical
  ext i
  constructor
  next =>
    intro hi
    obtain ⟨t, ht, hit⟩ := (mem_levelCoords _ _ _).mp hi
    have hlow := hstart t ht.1
    have heq : start + (t - start) = t := by omega
    refine Finset.mem_biUnion.mpr (Exists.intro (t - start) (And.intro ?_ ?_))
    next => exact Finset.mem_range.mpr (by have := ht.2; omega)
    next => simpa [offsetBin, heq, ht.1] using hit
  next =>
    intro hi
    obtain ⟨j, hj, hit⟩ := Finset.mem_biUnion.mp hi
    have hsmall := Finset.mem_range.mp hj
    by_cases hg : start + j ∈ group
    next =>
      have hit' : i ∈ bins (start + j) := by simpa [offsetBin, hg] using hit
      exact (mem_levelCoords _ _ _).mpr
        (Exists.intro (start + j) (And.intro (And.intro hg (by omega)) hit'))
    next =>
      have hempty : i ∈ (Finset.empty : Finset I) := by
        simpa [offsetBin, hg] using hit
      exact False.elim (Finset.notMem_empty i hempty)

/-- Exact support cap requiring a bin bound only for levels inside the selected group. -/
theorem retained_card_le_in_group (bins : Nat -> Finset I) {group : Set Nat}
    {start depth : Nat} {cap : Real} (hcap0 : 0 <= cap)
    (hstart : forall t, t ∈ group -> start <= t)
    (hcap : forall j, j ∈ Finset.range depth -> start + j ∈ group ->
      ((bins (start + j)).card : Real) <= cap) :
    ((retainedCoords bins group start depth).card : Real) <= (depth : Real) * cap := by
  classical
  rw [retained_eq_offset_union bins hstart]
  have hcard : ((Finset.range depth).biUnion (offsetBin bins group start)).card <=
      (Finset.range depth).sum (fun j => (offsetBin bins group start j).card) :=
    Finset.card_biUnion_le
  have hreal : (((Finset.range depth).biUnion (offsetBin bins group start)).card : Real) <=
      (Finset.range depth).sum (fun j => ((offsetBin bins group start j).card : Real)) := by
    exact_mod_cast hcard
  calc
    (((Finset.range depth).biUnion (offsetBin bins group start)).card : Real) <=
        (Finset.range depth).sum (fun j => ((offsetBin bins group start j).card : Real)) := hreal
    _ <= (Finset.range depth).sum (fun _ => cap) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hg : start + j ∈ group
      next => simpa [offsetBin, hg] using hcap j hj hg
      next =>
        have hempty : offsetBin bins group start j = ∅ := by
          unfold offsetBin
          exact ite_eq_right hg
        rw [hempty]
        simpa using hcap0
    _ = (depth : Real) * cap := by simp

/-- The nonempty base support provides the lower cardinality bound in the paper. -/
theorem base_card_le_retained_support {bins : Nat -> Finset I} (u : I -> Real)
    {group : Set Nat} {start depth : Nat} (hstart : start ∈ group) (hdepth : 0 < depth)
    (hnz : forall i, i ∈ bins start -> Not (u i = 0)) :
    (bins start).card <= (support (restrict u (retainedCoords bins group start depth))).card :=
  Finset.card_le_card (base_bin_subset_support u hstart hdepth hnz)

omit [Fintype I] [DecidableEq I] in
theorem mass_mono (u : I -> Real) {A B : Finset I} (hAB : A ⊆ B) :
    mass u A <= mass u B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => abs_nonneg (u i))

omit [Fintype I] [DecidableEq I] in
theorem energy_mono (u : I -> Real) {A B : Finset I} (hAB : A ⊆ B) :
    energy u A <= energy u B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => sq_nonneg (u i))

omit [Fintype I] [DecidableEq I] in
theorem mass_lower_from_base (u : I -> Real) {A B : Finset I} {lambda : Real}
    (hAB : A ⊆ B) (hlo : forall i, i ∈ A -> lambda <= |u i|) :
    lambda * (A.card : Real) <= mass u B := by
  have hsum := Finset.sum_le_sum hlo
  have hbase : lambda * (A.card : Real) <= mass u A := by
    simpa [mass, mul_comm] using hsum
  exact le_trans hbase (mass_mono u hAB)

omit [Fintype I] [DecidableEq I] in
theorem energy_lower_from_base (u : I -> Real) {A B : Finset I} {lambda : Real}
    (hlambda : 0 <= lambda) (hAB : A ⊆ B)
    (hlo : forall i, i ∈ A -> lambda <= |u i|) :
    lambda ^ 2 * (A.card : Real) <= energy u B := by
  have hsquare : forall i, i ∈ A -> lambda ^ 2 <= (u i) ^ 2 := by
    intro i hi
    have hp := mul_nonneg (sub_nonneg.mpr (hlo i hi))
      (add_nonneg (abs_nonneg (u i)) hlambda)
    nlinarith [sq_abs (u i)]
  have hsum := Finset.sum_le_sum hsquare
  have hbase : lambda ^ 2 * (A.card : Real) <= energy u A := by
    simpa [energy, mul_comm] using hsum
  exact le_trans hbase (energy_mono u hAB)

/-- Base-bin amplitude scale used in the manuscript. -/
def baseScale (scale : Real) (start : Nat) : Real :=
  scale / (2 : Real) ^ (start + 1)

theorem baseScale_twice (scale : Real) (start : Nat) :
    scale / (2 : Real) ^ start = 2 * baseScale scale start := by
  unfold baseScale
  rw [pow_succ]
  field_simp

omit [DecidableEq I] in
/-- The base bin has precisely the paper's half-open magnitude interval. -/
theorem base_bin_amplitude {u : I -> Real} {scale : Real} {start : Nat} {i : I}
    (hi : i ∈ bin u scale start) :
    baseScale scale start < |u i| /\ |u i| <= 2 * baseScale scale start := by
  have h := (mem_bin _ _ _ _).mp hi
  exact And.intro h.1 (by simpa only [baseScale_twice] using h.2)

omit [DecidableEq I] in
/-- Later level amplitudes have the exact dyadic attenuation from the base scale. -/
theorem later_bin_amplitude {u : I -> Real} {scale : Real} {start j : Nat} {i : I}
    (hi : i ∈ bin u scale (start + j)) :
    |u i| <= 2 * baseScale scale start * (1 / 2 : Real) ^ j := by
  have h := (mem_bin _ _ _ _).mp hi
  have heq : scale / (2 : Real) ^ (start + j) =
      2 * baseScale scale start * (1 / 2 : Real) ^ j := by
    unfold baseScale
    rw [pow_add, pow_succ]
    simp only [div_pow, one_pow]
    field_simp
  simpa only [heq] using h.2

omit [DecidableEq I] in
/-- Every coefficient retained from a group is bounded by twice its base scale. -/
theorem retained_abs_bound {u : I -> Real} {scale : Real} (hscale : 0 <= scale)
    {group : Set Nat} {start depth : Nat}
    (hstart : forall t, t ∈ group -> start <= t) {i : I}
    (hi : i ∈ retainedCoords (bin u scale) group start depth) :
    |u i| <= 2 * baseScale scale start := by
  have hw := (mem_levelCoords _ _ _).mp hi
  let t := hw.choose
  have ht := hw.choose_spec
  have hcoeff := (mem_bin _ _ _ _).mp ht.2
  have hpow : (2 : Real) ^ start <= (2 : Real) ^ t :=
    pow_le_pow_right₀ (by norm_num) (hstart t ht.1.1)
  calc
    |u i| <= scale / (2 : Real) ^ t := hcoeff.2
    _ <= scale / (2 : Real) ^ start :=
      div_le_div_of_nonneg_left hscale (by positivity) hpow
    _ = 2 * baseScale scale start := baseScale_twice scale start

/-- Literal sup-norm cap for the repaired retained coefficient vector. -/
theorem retained_norm_bound {u : I -> Real} {scale : Real} (hscale : 0 <= scale)
    {group : Set Nat} {start depth : Nat}
    (hstart : forall t, t ∈ group -> start <= t) :
    norm (restrict u (retainedCoords (bin u scale) group start depth)) <=
      2 * baseScale scale start := by
  have hc : 0 <= 2 * baseScale scale start := by unfold baseScale; positivity
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  by_cases hi : i ∈ retainedCoords (bin u scale) group start depth
  next =>
    simpa only [restrict, ite_eq_left hi, Real.norm_eq_abs] using retained_abs_bound hscale hstart hi
  next => simp only [restrict, ite_eq_right hi, norm_zero]; exact hc

/-- A finite geometric series identity, with no infinite-series interchange. -/
theorem half_sum_identity (N : Nat) :
    (Finset.range N).sum (fun j => (1 / 2 : Real) ^ j) =
      2 * (1 - (1 / 2 : Real) ^ N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem half_sum_le_two (N : Nat) :
    (Finset.range N).sum (fun j => (1 / 2 : Real) ^ j) <= 2 := by
  rw [half_sum_identity]
  have h : 0 <= (1 / 2 : Real) ^ N := by positivity
  linarith

theorem quarter_sum_identity (N : Nat) :
    (Finset.range N).sum (fun j => (1 / 4 : Real) ^ j) =
      (4 / 3) * (1 - (1 / 4 : Real) ^ N) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem quarter_sum_le (N : Nat) :
    (Finset.range N).sum (fun j => (1 / 4 : Real) ^ j) <= 4 / 3 := by
  rw [quarter_sum_identity]
  have h : 0 <= (1 / 4 : Real) ^ N := by positivity
  linarith

/-- Finite tails are uniformly bounded by the paper's dyadic tail value. -/
theorem half_tail_le (T N : Nat) :
    (Finset.range N).sum (fun j => (1 / 2 : Real) ^ (T + j)) <=
      2 * (1 / 2 : Real) ^ T := by
  calc
    (Finset.range N).sum (fun j => (1 / 2 : Real) ^ (T + j)) =
        (1 / 2 : Real) ^ T * (Finset.range N).sum (fun j => (1 / 2 : Real) ^ j) := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ <= (1 / 2 : Real) ^ T * 2 :=
      mul_le_mul_of_nonneg_left (half_sum_le_two N) (by positivity)
    _ = 2 * (1 / 2 : Real) ^ T := by ring

/-- The retained-bin mass budget collapses to the manuscript's 4q bound. -/
theorem mass_budget (q lambda S : Real) (N : Nat)
    (hq : 1 <= q) (hlambda : 0 <= lambda) (hS : 0 <= S) :
    2 * lambda * S + 2 * q * lambda * S *
      (Finset.range N).sum (fun j => (1 / 2 : Real) ^ (j + 1)) <=
      4 * q * lambda * S := by
  have hseries : (Finset.range N).sum (fun j => (1 / 2 : Real) ^ (j + 1)) <= 1 := by
    calc
      (Finset.range N).sum (fun j => (1 / 2 : Real) ^ (j + 1)) =
          (1 / 2 : Real) * (Finset.range N).sum (fun j => (1 / 2 : Real) ^ j) := by
        simp_rw [pow_succ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ <= (1 / 2 : Real) * 2 := mul_le_mul_of_nonneg_left (half_sum_le_two N) (by norm_num)
      _ = 1 := by norm_num
  have hq0 : 0 <= q := le_trans (by norm_num) hq
  have hprod : 0 <= lambda * S := mul_nonneg hlambda hS
  have hqprod := mul_le_mul_of_nonneg_right hq hprod
  have hscale := mul_le_mul_of_nonneg_left hseries
    (by positivity : 0 <= 2 * q * lambda * S)
  nlinarith

/-- The retained-bin energy budget collapses to the manuscript's 16q/3 bound. -/
theorem energy_budget (q lambda S : Real) (N : Nat)
    (hq : 1 <= q) (hS : 0 <= S) :
    4 * lambda ^ 2 * S + 4 * q * lambda ^ 2 * S *
      (Finset.range N).sum (fun j => (1 / 4 : Real) ^ (j + 1)) <=
      (16 * q / 3) * lambda ^ 2 * S := by
  have hseries : (Finset.range N).sum (fun j => (1 / 4 : Real) ^ (j + 1)) <= 1 / 3 := by
    calc
      (Finset.range N).sum (fun j => (1 / 4 : Real) ^ (j + 1)) =
          (1 / 4 : Real) * (Finset.range N).sum (fun j => (1 / 4 : Real) ^ j) := by
        simp_rw [pow_succ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ <= (1 / 4 : Real) * (4 / 3) := mul_le_mul_of_nonneg_left (quarter_sum_le N) (by norm_num)
      _ = 1 / 3 := by norm_num
  have hq0 : 0 <= q := le_trans (by norm_num) hq
  have hprod : 0 <= lambda ^ 2 * S := mul_nonneg (sq_nonneg lambda) hS
  have hqprod := mul_le_mul_of_nonneg_right hq hprod
  have hscale := mul_le_mul_of_nonneg_left hseries
    (by positivity : 0 <= 4 * q * lambda ^ 2 * S)
  nlinarith

/-- Finite omitted-level budgets give the same uniform truncation factor as the paper. -/
theorem omitted_mass_budget {q lambda S m : Real} (hq : 0 <= q)
    (hlambda : 0 <= lambda) (hS : 0 <= S) (hm : lambda * S <= m)
    (w : Nat -> Real) (T N : Nat)
    (hw : forall j, j ∈ Finset.range N ->
      w j <= 2 * q * lambda * S * (1 / 2 : Real) ^ (T + j)) :
    (Finset.range N).sum w <= 4 * q * (1 / 2 : Real) ^ T * m := by
  calc
    (Finset.range N).sum w <= (Finset.range N).sum
        (fun j => 2 * q * lambda * S * (1 / 2 : Real) ^ (T + j)) := Finset.sum_le_sum hw
    _ = 2 * q * lambda * S * (Finset.range N).sum
        (fun j => (1 / 2 : Real) ^ (T + j)) := (Finset.mul_sum _ _ _).symm
    _ <= 2 * q * lambda * S * (2 * (1 / 2 : Real) ^ T) :=
      mul_le_mul_of_nonneg_left (half_tail_le T N) (by positivity)
    _ = 4 * q * (1 / 2 : Real) ^ T * (lambda * S) := by ring
    _ <= 4 * q * (1 / 2 : Real) ^ T * m :=
      mul_le_mul_of_nonneg_left hm (by positivity)

/-- ASCII-named division helper, proved only by monotonicity and field algebra. -/
theorem div_le_from_le_mul {a b c : Real} (hc : 0 < c) (h : a <= b * c) : a / c <= b := by
  calc
    a / c <= (b * c) / c := div_le_div_of_nonneg_right h hc.le
    _ = b := by field_simp [ne_of_gt hc]

theorem le_div_from_mul_le {a b c : Real} (hc : 0 < c) (h : a * c <= b) : a <= b / c := by
  calc
    a = (a * c) / c := by field_simp [ne_of_gt hc]
    _ <= b / c := div_le_div_of_nonneg_right h hc.le

/-- The effective-support estimate follows algebraically from the already stated mass budgets. -/
theorem effective_support_bounds {q lambda S m Q : Real}
    (hq : 0 < q) (hlambda : 0 < lambda) (hS : 0 < S)
    (hmlo : lambda * S <= m) (hmhi : m <= 4 * q * lambda * S)
    (hQlo : lambda ^ 2 * S <= Q) (hQhi : Q <= (16 * q / 3) * lambda ^ 2 * S) :
    (3 / (16 * q)) * S <= m ^ 2 / Q /\ m ^ 2 / Q <= 16 * q ^ 2 * S := by
  have hm : 0 < m := lt_of_lt_of_le (mul_pos hlambda hS) hmlo
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hlambda) hS) hQlo
  have hloProd := mul_nonneg (sub_nonneg.mpr hmlo)
    (by positivity : 0 <= m + lambda * S)
  have hhiProd := mul_nonneg (sub_nonneg.mpr hmhi)
    (by positivity : 0 <= 4 * q * lambda * S + m)
  have hslo : lambda ^ 2 * S ^ 2 <= m ^ 2 := by nlinarith
  have hshi : m ^ 2 <= 16 * q ^ 2 * lambda ^ 2 * S ^ 2 := by nlinarith
  constructor
  next =>
    apply le_div_from_mul_le hQ
    have h1 := mul_le_mul_of_nonneg_left hQhi (by positivity : 0 <= 3 * S)
    have h2 := mul_le_mul_of_nonneg_left hslo (by positivity : 0 <= 16 * q)
    have hraw : 3 * S * Q <= m ^ 2 * (16 * q) := by nlinarith
    have hdiv := div_le_from_le_mul (by positivity : 0 < 16 * q) hraw
    calc
      (3 / (16 * q)) * S * Q = (3 * S * Q) / (16 * q) := by ring
      _ <= m ^ 2 := hdiv
  next =>
    apply div_le_from_le_mul hQ
    have hmul := mul_le_mul_of_nonneg_left hQlo
      (by positivity : 0 <= 16 * q ^ 2 * S)
    nlinarith

/-- The coordinate cap conversion uses only the positive mass and energy budgets. -/
theorem coordinate_cap_ratio {q lambda S m Q : Real}
    (hq : 0 < q) (hlambda : 0 < lambda) (_hS : 0 < S)
    (hm : 0 < m) (hmhi : m <= 4 * q * lambda * S)
    (hQlo : lambda ^ 2 * S <= Q) : 2 * lambda <= 8 * q * (Q / m) := by
  have h1 := mul_le_mul_of_nonneg_left hmhi (by positivity : 0 <= 2 * lambda)
  have h2 := mul_le_mul_of_nonneg_left hQlo (by positivity : 0 <= 8 * q)
  have hraw : (2 * lambda) * m <= 8 * q * Q := by nlinarith
  have hdiv := le_div_from_mul_le hm hraw
  simpa only [mul_div_assoc] using hdiv

/-- Exact square-root representation bridge for the effective support R=m^2/Q. -/
theorem energy_mass_ratio {m Q : Real} (hm : 0 < m) (hQ : 0 < Q) :
    Q / m = Real.sqrt Q / Real.sqrt (m ^ 2 / Q) := by
  rw [Real.sqrt_div (sq_nonneg m) Q, Real.sqrt_sq hm.le]
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsquare : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ.le
  field_simp [ne_of_gt hm, ne_of_gt hsqrt]
  nlinarith

/-- Geometrically increasing record supports have a bounded prefix sum. -/
theorem record_prefix_bound {q : Real} (hq : 1 < q) (S : Nat -> Real)
    (hzero : 0 <= S 0) (hg : forall k, q * S k <= S (k + 1)) (r : Nat) :
    (Finset.range r).sum S <= S r / (q - 1) := by
  have hstep : forall r : Nat,
      (q - 1) * (Finset.range r).sum S <= S r - S 0 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ]
      have hnext := hg r
      nlinarith
  have hraw : (Finset.range r).sum S * (q - 1) <= S r := by
    have h := hstep r
    nlinarith
  exact le_div_from_mul_le (sub_pos.mpr hq) hraw

/-- The retained-cardinality prefix estimate follows from the support-record estimate. -/
theorem retained_prefix_bound {q C : Real} (hq : 1 < q) (hC : 0 <= C)
    (S k : Nat -> Real) (hzero : 0 <= S 0)
    (hg : forall j, q * S j <= S (j + 1))
    (hk : forall j, k j <= C * S j) (r : Nat) :
    (Finset.range r).sum k <= C * S r / (q - 1) := by
  calc
    (Finset.range r).sum k <= (Finset.range r).sum (fun j => C * S j) :=
      Finset.sum_le_sum (fun j _ => hk j)
    _ = C * (Finset.range r).sum S := (Finset.mul_sum _ _ _).symm
    _ <= C * (S r / (q - 1)) :=
      mul_le_mul_of_nonneg_left (record_prefix_bound hq S hzero hg r) hC
    _ = C * S r / (q - 1) := by ring

end Dyadic
end GaussianEllipsoid
