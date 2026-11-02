/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.

Kernel-checked finite Gibbs algebra and domination proofs.
No differentiation formula or probabilistic comparison theorem is postulated.
Source: paper.tex, lines 3890-4024.
-/
import GaussianEllipsoid.FreeEnergy
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace GaussianEllipsoid
namespace FiniteGibbs

open FiniteFreeEnergy

/-- A finite probability law, with its normalization included in the structure. -/
structure Law (I : Type*) [Fintype I] where
  weight : I -> Real
  nonneg : forall u, 0 <= weight u
  total : Finset.univ.sum weight = 1

variable {I : Type*} [Fintype I]

def expectation (nu : Law I) (f : I -> Real) : Real :=
  Finset.univ.sum (fun u => nu.weight u * f u)

theorem expectation_const (nu : Law I) (c : Real) :
    expectation nu (fun _ => c) = c := by
  unfold expectation
  rw [<- Finset.sum_mul, nu.total, one_mul]

theorem expectation_mono (nu : Law I) {f g : I -> Real}
    (h : forall u, f u <= g u) : expectation nu f <= expectation nu g := by
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (h u) (nu.nonneg u))

theorem expectation_nonneg (nu : Law I) {f : I -> Real} (h : forall u, 0 <= f u) :
    0 <= expectation nu f := by
  exact Finset.sum_nonneg (fun u _ => mul_nonneg (nu.nonneg u) (h u))

theorem exists_weight_pos (nu : Law I) : exists u, 0 < nu.weight u := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hsum : Finset.univ.sum nu.weight <= 0 := Finset.sum_nonpos (fun u _ => h u)
  rw [nu.total] at hsum
  norm_num at hsum

/-- The normalizer for a one-row bounded or unbounded exponential tilt. -/
def tiltNormalizer (nu : Law I) (beta : Real) (h : I -> Real) : Real :=
  expectation nu (fun u => Real.exp (-beta * h u))

theorem tiltNormalizer_pos (nu : Law I) (beta : Real) (h : I -> Real) :
    0 < tiltNormalizer nu beta h := by
  let u : I := Classical.choose (exists_weight_pos nu)
  have hu : 0 < nu.weight u := Classical.choose_spec (exists_weight_pos nu)
  exact Finset.sum_pos'
    (fun v _ => mul_nonneg (nu.nonneg v) (Real.exp_nonneg _))
    (Exists.intro u (And.intro (Finset.mem_univ u) (mul_pos hu (Real.exp_pos _))))

def tiltDensity (nu : Law I) (beta : Real) (h : I -> Real) (u : I) : Real :=
  Real.exp (-beta * h u) / tiltNormalizer nu beta h

theorem tiltDensity_pos (nu : Law I) (beta : Real) (h : I -> Real) (u : I) :
    0 < tiltDensity nu beta h u :=
  div_pos (Real.exp_pos _) (tiltNormalizer_pos nu beta h)

/-- The tilted probability law is constructed from its actual finite weights. -/
def tiltedLaw (nu : Law I) (beta : Real) (h : I -> Real) : Law I where
  weight u := nu.weight u * Real.exp (-beta * h u) / tiltNormalizer nu beta h
  nonneg u := div_nonneg (mul_nonneg (nu.nonneg u) (Real.exp_nonneg _))
    (tiltNormalizer_pos nu beta h).le
  total := by
    rw [<- Finset.sum_div]
    change tiltNormalizer nu beta h / tiltNormalizer nu beta h = 1
    exact div_self (ne_of_gt (tiltNormalizer_pos nu beta h))

theorem tilted_weight_eq_density (nu : Law I) (beta : Real) (h : I -> Real) (u : I) :
    (tiltedLaw nu beta h).weight u = nu.weight u * tiltDensity nu beta h u := by
  unfold tiltedLaw tiltDensity
  ring

theorem exp_loss_bounds (beta : Real) (hbeta : 0 <= beta) (t : Real)
    (ht : 0 <= t /\ t <= 1) :
    Real.exp (-beta) <= Real.exp (-beta * t) /\ Real.exp (-beta * t) <= 1 := by
  constructor
  case left =>
    apply Real.exp_le_exp.mpr
    nlinarith [ht.2]
  case right =>
    rw [<- Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1]

theorem tiltNormalizer_bounds (nu : Law I) (beta : Real) (hbeta : 0 <= beta)
    (h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1) :
    Real.exp (-beta) <= tiltNormalizer nu beta h /\ tiltNormalizer nu beta h <= 1 := by
  have hlo := expectation_mono nu (fun u => (exp_loss_bounds beta hbeta (h u) (hh u)).1)
  have hup := expectation_mono nu (fun u => (exp_loss_bounds beta hbeta (h u) (hh u)).2)
  rw [expectation_const] at hlo hup
  exact And.intro hlo hup

/-- The actual Radon-Nikodym density lies between exp(-beta) and exp(beta). -/
theorem tiltDensity_bounds (nu : Law I) (beta : Real) (hbeta : 0 <= beta)
    (h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1) (u : I) :
    Real.exp (-beta) <= tiltDensity nu beta h u /\
      tiltDensity nu beta h u <= Real.exp beta := by
  have hz := tiltNormalizer_pos nu beta h
  have hzlo := (tiltNormalizer_bounds nu beta hbeta h hh).1
  have hzhi := (tiltNormalizer_bounds nu beta hbeta h hh).2
  have hnumlo := (exp_loss_bounds beta hbeta (h u) (hh u)).1
  have hnumhi := (exp_loss_bounds beta hbeta (h u) (hh u)).2
  constructor
  case left =>
    apply le_divide_of_mul_le hz
    have hmul := mul_le_mul_of_nonneg_left hzhi (Real.exp_nonneg (-beta))
    nlinarith
  case right =>
    apply divide_le_of_le_mul hz
    have hmul := mul_le_mul_of_nonneg_left hzlo (Real.exp_nonneg beta)
    have hid : Real.exp beta * Real.exp (-beta) = 1 := by
      rw [<- Real.exp_add]
      simp
    rw [hid] at hmul
    exact hnumhi.trans hmul

def productDensity (nu : Law I) (beta : Real) (h : I -> Real)
    (k : Nat) (u : Fin k -> I) : Real :=
  Finset.univ.prod (fun j => tiltDensity nu beta h (u j))

/-- Product bounds hold for every k, including the paper's k=1,2,3. -/
theorem productDensity_bounds (nu : Law I) (beta : Real) (hbeta : 0 <= beta)
    (h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1)
    (k : Nat) (u : Fin k -> I) :
    Real.exp (-(k : Real) * beta) <= productDensity nu beta h k u /\
      productDensity nu beta h k u <= Real.exp ((k : Real) * beta) := by
  have hlo : Finset.univ.prod (fun _ : Fin k => Real.exp (-beta)) <=
      productDensity nu beta h k u :=
    Finset.prod_le_prod (fun _ _ => Real.exp_nonneg _)
      (fun j _ => (tiltDensity_bounds nu beta hbeta h hh (u j)).1)
  have hup : productDensity nu beta h k u <=
      Finset.univ.prod (fun _ : Fin k => Real.exp beta) :=
    Finset.prod_le_prod (fun j _ => (tiltDensity_pos nu beta h (u j)).le)
      (fun j _ => (tiltDensity_bounds nu beta hbeta h hh (u j)).2)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hlo hup
  rw [<- Real.exp_nat_mul] at hlo hup
  have hneg : (k : Real) * (-beta) = -(k : Real) * beta := by ring
  rw [hneg] at hlo
  exact And.intro hlo hup

theorem product_weight_density_identity (nu : Law I) (beta : Real) (h : I -> Real)
    (k : Nat) (u : Fin k -> I) :
    Finset.univ.prod (fun j => (tiltedLaw nu beta h).weight (u j)) =
      Finset.univ.prod (fun j => nu.weight (u j)) * productDensity nu beta h k u := by
  simp_rw [tilted_weight_eq_density]
  exact Finset.prod_mul_distrib

/-- The genuine normalized law of k independent draws from a finite law. -/
def independentProduct (nu : Law I) (k : Nat) : Law (Fin k -> I) where
  weight u := Finset.univ.prod (fun j => nu.weight (u j))
  nonneg u := Finset.prod_nonneg (fun j _ => nu.nonneg (u j))
  total := by
    rw [<- Fintype.sum_pow, nu.total, one_pow]

/-- Products of finite expectations equal expectation over independent draws. -/
theorem independentProduct_expectation (nu : Law I) (k : Nat) (f : Fin k -> I -> Real) :
    expectation (independentProduct nu k)
      (fun u => Finset.univ.prod (fun j => f j (u j))) =
      Finset.univ.prod (fun j => expectation nu (f j)) := by
  unfold expectation independentProduct
  simp_rw [<- Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j u => nu.weight u * f j u)).symm

/-- Nonnegative-observable domination for every finite number of independent draws. -/
theorem product_tilt_expectation_bounds (nu : Law I) (beta : Real) (hbeta : 0 <= beta)
    (h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1)
    (k : Nat) (f : (Fin k -> I) -> Real) (hf : forall u, 0 <= f u) :
    Real.exp (-(k : Real) * beta) * expectation (independentProduct nu k) f <=
      expectation (independentProduct (tiltedLaw nu beta h) k) f /\
    expectation (independentProduct (tiltedLaw nu beta h) k) f <=
      Real.exp ((k : Real) * beta) * expectation (independentProduct nu k) f := by
  constructor
  case left =>
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    change Real.exp (-(k : Real) * beta) *
        (Finset.univ.prod (fun j => nu.weight (u j)) * f u) <=
      Finset.univ.prod (fun j => (tiltedLaw nu beta h).weight (u j)) * f u
    rw [product_weight_density_identity]
    have hd := (productDensity_bounds nu beta hbeta h hh k u).1
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg ((independentProduct nu k).nonneg u) (hf u))
    change (Finset.univ.prod (fun j => nu.weight (u j)) * f u) *
        Real.exp (-(k : Real) * beta) <=
      (Finset.univ.prod (fun j => nu.weight (u j)) * f u) *
        productDensity nu beta h k u at hm
    nlinarith
  case right =>
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    change Finset.univ.prod (fun j => (tiltedLaw nu beta h).weight (u j)) * f u <=
      Real.exp ((k : Real) * beta) *
        (Finset.univ.prod (fun j => nu.weight (u j)) * f u)
    rw [product_weight_density_identity]
    have hd := (productDensity_bounds nu beta hbeta h hh k u).2
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg ((independentProduct nu k).nonneg u) (hf u))
    change (Finset.univ.prod (fun j => nu.weight (u j)) * f u) *
        productDensity nu beta h k u <=
      (Finset.univ.prod (fun j => nu.weight (u j)) * f u) *
        Real.exp ((k : Real) * beta) at hm
    nlinarith

theorem tilted_expectation_le (nu : Law I) (beta : Real) (hbeta : 0 <= beta)
    (h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1)
    (f : I -> Real) (hf : forall u, 0 <= f u) :
    expectation (tiltedLaw nu beta h) f <= Real.exp beta * expectation nu f := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [tilted_weight_eq_density]
  have hb := (tiltDensity_bounds nu beta hbeta h hh u).2
  have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg (nu.nonneg u) (hf u))
  nlinarith

variable [Nonempty I]

def gibbsWeight (beta : Real) (H : I -> Real) (u : I) : Real :=
  Real.exp (-beta * H u) / partitionSum beta H

theorem gibbsWeight_pos (beta : Real) (H : I -> Real) (u : I) :
    0 < gibbsWeight beta H u :=
  div_pos (Real.exp_pos _) (partitionSum_pos beta H)

/-- A Gibbs law with no normalization assumption hidden in its interface. -/
def gibbsLaw (beta : Real) (H : I -> Real) : Law I where
  weight := gibbsWeight beta H
  nonneg u := (gibbsWeight_pos beta H u).le
  total := by
    unfold gibbsWeight
    rw [<- Finset.sum_div]
    change partitionSum beta H / partitionSum beta H = 1
    exact div_self (ne_of_gt (partitionSum_pos beta H))

theorem gibbsLaw_weight (beta : Real) (H : I -> Real) (u : I) :
    (gibbsLaw beta H).weight u = gibbsWeight beta H u := rfl

/-- Exact factorization of the full partition sum by the row-deleted one. -/
theorem partitionSum_add (beta : Real) (R h : I -> Real) :
    partitionSum beta (fun u => R u + h u) =
      partitionSum beta R * tiltNormalizer (gibbsLaw beta R) beta h := by
  have hz : Not (partitionSum beta R = 0) := ne_of_gt (partitionSum_pos beta R)
  unfold tiltNormalizer expectation
  rw [Finset.mul_sum]
  unfold partitionSum
  apply Finset.sum_congr rfl
  intro u _
  change Real.exp (-beta * (R u + h u)) =
    (Finset.univ.sum fun v => Real.exp (-beta * R v)) *
      (gibbsWeight beta R u * Real.exp (-beta * h u))
  rw [show -beta * (R u + h u) = -beta * R u + -beta * h u by ring,
    Real.exp_add]
  change Real.exp (-beta * R u) * Real.exp (-beta * h u) =
    partitionSum beta R *
      (Real.exp (-beta * R u) / partitionSum beta R * Real.exp (-beta * h u))
  field_simp [hz]

/-- The posterior Gibbs law is exactly the tilt of the row-deleted Gibbs law. -/
theorem gibbsWeight_add_eq_tilted (beta : Real) (R h : I -> Real) (u : I) :
    gibbsWeight beta (fun v => R v + h v) u =
      (tiltedLaw (gibbsLaw beta R) beta h).weight u := by
  have hz : Not (partitionSum beta R = 0) := ne_of_gt (partitionSum_pos beta R)
  have ht : Not (tiltNormalizer (gibbsLaw beta R) beta h = 0) :=
    ne_of_gt (tiltNormalizer_pos (gibbsLaw beta R) beta h)
  unfold gibbsWeight
  rw [partitionSum_add]
  rw [show -beta * (R u + h u) = -beta * R u + -beta * h u by ring, Real.exp_add]
  change Real.exp (-beta * R u) * Real.exp (-beta * h u) /
    (partitionSum beta R * tiltNormalizer (gibbsLaw beta R) beta h) =
      (Real.exp (-beta * R u) / partitionSum beta R * Real.exp (-beta * h u)) /
        tiltNormalizer (gibbsLaw beta R) beta h
  field_simp [hz, ht]

theorem gibbsWeight_ratio_eq_tiltDensity (beta : Real) (R h : I -> Real) (u : I) :
    gibbsWeight beta (fun v => R v + h v) u / gibbsWeight beta R u =
      tiltDensity (gibbsLaw beta R) beta h u := by
  rw [gibbsWeight_add_eq_tilted, tilted_weight_eq_density, gibbsLaw_weight]
  have hw := ne_of_gt (gibbsWeight_pos beta R u)
  field_simp [hw]

theorem gibbsWeight_ratio_bounds (beta : Real) (hbeta : 0 <= beta)
    (R h : I -> Real) (hh : forall u, 0 <= h u /\ h u <= 1) (u : I) :
    Real.exp (-beta) <=
      gibbsWeight beta (fun v => R v + h v) u / gibbsWeight beta R u /\
    gibbsWeight beta (fun v => R v + h v) u / gibbsWeight beta R u <=
      Real.exp beta := by
  rw [gibbsWeight_ratio_eq_tiltDensity]
  exact tiltDensity_bounds (gibbsLaw beta R) beta hbeta h hh u

theorem partitionAverage_add (beta : Real) (R h : I -> Real) :
    partitionAverage beta (fun u => R u + h u) =
      partitionAverage beta R * tiltNormalizer (gibbsLaw beta R) beta h := by
  unfold partitionAverage
  rw [partitionSum_add]
  ring

/-- The current-row free-energy contribution associated with a fixed cavity law. -/
def cavityContribution (nu : Law I) (beta : Real) (n : Nat) (h : I -> Real) : Real :=
  -Real.log (tiltNormalizer nu beta h) / (beta * (n : Real))

theorem freeEnergy_cavity_decomposition (beta : Real) (n : Nat) (R h : I -> Real) :
    freeEnergy beta n (fun u => R u + h u) = freeEnergy beta n R +
      cavityContribution (gibbsLaw beta R) beta n h := by
  unfold freeEnergy cavityContribution
  rw [partitionAverage_add, Real.log_mul
    (ne_of_gt (partitionAverage_pos beta R))
    (ne_of_gt (tiltNormalizer_pos (gibbsLaw beta R) beta h))]
  ring

theorem cavity_difference (beta : Real) (n : Nat) (R h h' : I -> Real) :
    freeEnergy beta n (fun u => R u + h u) -
      freeEnergy beta n (fun u => R u + h' u) =
      cavityContribution (gibbsLaw beta R) beta n h -
      cavityContribution (gibbsLaw beta R) beta n h' := by
  rw [freeEnergy_cavity_decomposition, freeEnergy_cavity_decomposition]
  ring

/-- The cavity decomposition for actual row deletion in the manuscript. -/
theorem freeEnergy_deleted_row (beta : Real) (n : Nat) (loss : Fin n -> I -> Real)
    (m : Fin n) :
    freeEnergy beta n (totalLoss loss) = freeEnergy beta n (deletedLoss loss m) +
      cavityContribution (gibbsLaw beta (deletedLoss loss m)) beta n (loss m) := by
  have he : totalLoss loss = fun u => deletedLoss loss m u + loss m u :=
    funext (totalLoss_eq_deleted_add loss m)
  rw [he]
  exact freeEnergy_cavity_decomposition beta n (deletedLoss loss m) (loss m)

theorem partitionSum_deleted_row (beta : Real) (n : Nat) (loss : Fin n -> I -> Real)
    (m : Fin n) :
    partitionSum beta (totalLoss loss) = partitionSum beta (deletedLoss loss m) *
      tiltNormalizer (gibbsLaw beta (deletedLoss loss m)) beta (loss m) := by
  have he : totalLoss loss = fun u => deletedLoss loss m u + loss m u :=
    funext (totalLoss_eq_deleted_add loss m)
  rw [he]
  exact partitionSum_add beta (deletedLoss loss m) (loss m)

omit [Nonempty I] in
theorem abs_expectation_le (nu : Law I) (f : I -> Real) (M : Real)
    (hf : forall u, abs (f u) <= M) : abs (expectation nu f) <= M := by
  calc
    abs (expectation nu f) <= Finset.univ.sum (fun u => abs (nu.weight u * f u)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun u => nu.weight u * abs (f u)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [abs_mul, abs_of_nonneg (nu.nonneg u)]
    _ <= Finset.univ.sum (fun u => nu.weight u * M) :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hf u) (nu.nonneg u))
    _ = M := expectation_const nu M

def covariance (nu : Law I) (a b : I -> Real) : Real :=
  expectation nu (fun u => a u * b u) - expectation nu a * expectation nu b

def cumulant3 (nu : Law I) (a b c : I -> Real) : Real :=
  expectation nu (fun u => a u * b u * c u) -
    expectation nu (fun u => a u * b u) * expectation nu c -
    expectation nu (fun u => a u * c u) * expectation nu b -
    expectation nu (fun u => b u * c u) * expectation nu a +
    2 * expectation nu a * expectation nu b * expectation nu c

omit [Nonempty I] in
theorem abs_covariance_le (nu : Law I) (a b : I -> Real) (A B : Real)
    (hA : 0 <= A) (_hB : 0 <= B)
    (ha : forall u, abs (a u) <= A) (hb : forall u, abs (b u) <= B) :
    abs (covariance nu a b) <= 2 * A * B := by
  have hab : abs (expectation nu (fun u => a u * b u)) <= A * B := by
    apply abs_expectation_le
    intro u
    rw [abs_mul]
    exact mul_le_mul (ha u) (hb u) (abs_nonneg _) hA
  have hprod : abs (expectation nu a * expectation nu b) <= A * B := by
    rw [abs_mul]
    exact mul_le_mul (abs_expectation_le nu a A ha) (abs_expectation_le nu b B hb)
      (abs_nonneg _) hA
  have ht := abs_sub (expectation nu (fun u => a u * b u))
    (expectation nu a * expectation nu b)
  unfold covariance
  linarith

omit [Nonempty I] in
/-- The exact five-term cumulant expansion has total absolute coefficient mass six. -/
theorem abs_cumulant3_le (nu : Law I) (a b c : I -> Real) (A B C : Real)
    (hA : 0 <= A) (hB : 0 <= B) (hC : 0 <= C)
    (ha : forall u, abs (a u) <= A) (hb : forall u, abs (b u) <= B)
    (hc : forall u, abs (c u) <= C) :
    abs (cumulant3 nu a b c) <= 6 * A * B * C := by
  have ea := abs_expectation_le nu a A ha
  have eb := abs_expectation_le nu b B hb
  have ec := abs_expectation_le nu c C hc
  have eab : abs (expectation nu (fun u => a u * b u)) <= A * B := by
    apply abs_expectation_le
    intro u
    rw [abs_mul]
    exact mul_le_mul (ha u) (hb u) (abs_nonneg _) hA
  have eac : abs (expectation nu (fun u => a u * c u)) <= A * C := by
    apply abs_expectation_le
    intro u
    rw [abs_mul]
    exact mul_le_mul (ha u) (hc u) (abs_nonneg _) hA
  have ebc : abs (expectation nu (fun u => b u * c u)) <= B * C := by
    apply abs_expectation_le
    intro u
    rw [abs_mul]
    exact mul_le_mul (hb u) (hc u) (abs_nonneg _) hB
  have eabc : abs (expectation nu (fun u => a u * b u * c u)) <= A * B * C := by
    apply abs_expectation_le
    intro u
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (ha u) (hb u) (abs_nonneg _) hA) (hc u)
      (abs_nonneg _) (mul_nonneg hA hB)
  have t1 : abs (expectation nu (fun u => a u * b u) * expectation nu c) <= A * B * C := by
    rw [abs_mul]
    exact mul_le_mul eab ec (abs_nonneg _) (mul_nonneg hA hB)
  have t2 : abs (expectation nu (fun u => a u * c u) * expectation nu b) <= A * B * C := by
    rw [abs_mul]
    have hm := mul_le_mul eac eb (abs_nonneg (expectation nu b)) (mul_nonneg hA hC)
    nlinarith
  have t3 : abs (expectation nu (fun u => b u * c u) * expectation nu a) <= A * B * C := by
    rw [abs_mul]
    have hm := mul_le_mul ebc ea (abs_nonneg (expectation nu a)) (mul_nonneg hB hC)
    nlinarith
  have t4 : abs (2 * expectation nu a * expectation nu b * expectation nu c) <=
      2 * A * B * C := by
    simp only [abs_mul, Nat.abs_ofNat]
    have hm := mul_le_mul (mul_le_mul ea eb (abs_nonneg _) hA) ec
      (abs_nonneg _) (mul_nonneg hA hB)
    nlinarith
  have hsub1 := abs_sub (expectation nu (fun u => a u * b u * c u))
    (expectation nu (fun u => a u * b u) * expectation nu c)
  have hsub2 := abs_sub
    (expectation nu (fun u => a u * b u * c u) -
      expectation nu (fun u => a u * b u) * expectation nu c)
    (expectation nu (fun u => a u * c u) * expectation nu b)
  have hsub3 := abs_sub
    (expectation nu (fun u => a u * b u * c u) -
      expectation nu (fun u => a u * b u) * expectation nu c -
      expectation nu (fun u => a u * c u) * expectation nu b)
    (expectation nu (fun u => b u * c u) * expectation nu a)
  have hadd := abs_add_le
    (expectation nu (fun u => a u * b u * c u) -
      expectation nu (fun u => a u * b u) * expectation nu c -
      expectation nu (fun u => a u * c u) * expectation nu b -
      expectation nu (fun u => b u * c u) * expectation nu a)
    (2 * expectation nu a * expectation nu b * expectation nu c)
  unfold cumulant3
  linarith

/-- Algebraic combination occurring after a third-derivative formula is proved.
This definition does not assert that it equals an actual derivative. -/
def scalarThirdExpression (nu : Law I) (beta : Real)
    (a1 a2 a3 b12 b23 b31 c123 : I -> Real) : Real :=
  expectation nu c123 - beta *
    (covariance nu b12 a3 + covariance nu b23 a1 + covariance nu b31 a2) +
      beta ^ 2 * cumulant3 nu a1 a2 a3

omit [Nonempty I] in
/-- Pure finite-law bound with the paper's coefficients 1, 6, and 6. -/
theorem abs_scalarThirdExpression_le (nu : Law I) (beta L1 L2 L3 : Real)
    (hbeta : 0 <= beta) (hL1 : 0 <= L1) (hL2 : 0 <= L2) (_hL3 : 0 <= L3)
    (a1 a2 a3 b12 b23 b31 c123 : I -> Real)
    (ha1 : forall u, abs (a1 u) <= L1) (ha2 : forall u, abs (a2 u) <= L1)
    (ha3 : forall u, abs (a3 u) <= L1) (hb12 : forall u, abs (b12 u) <= L2)
    (hb23 : forall u, abs (b23 u) <= L2) (hb31 : forall u, abs (b31 u) <= L2)
    (hc123 : forall u, abs (c123 u) <= L3) :
    abs (scalarThirdExpression nu beta a1 a2 a3 b12 b23 b31 c123) <=
      L3 + 6 * beta * L1 * L2 + 6 * beta ^ 2 * L1 ^ 3 := by
  have hc := abs_expectation_le nu c123 L3 hc123
  have h12 := abs_covariance_le nu b12 a3 L2 L1 hL2 hL1 hb12 ha3
  have h23 := abs_covariance_le nu b23 a1 L2 L1 hL2 hL1 hb23 ha1
  have h31 := abs_covariance_le nu b31 a2 L2 L1 hL2 hL1 hb31 ha2
  have ht1 := abs_add_le (covariance nu b12 a3) (covariance nu b23 a1)
  have ht2 := abs_add_le (covariance nu b12 a3 + covariance nu b23 a1)
    (covariance nu b31 a2)
  have hsum : abs (covariance nu b12 a3 + covariance nu b23 a1 +
      covariance nu b31 a2) <= 6 * L1 * L2 := by
    nlinarith
  have hcov : abs (beta * (covariance nu b12 a3 + covariance nu b23 a1 +
      covariance nu b31 a2)) <= 6 * beta * L1 * L2 := by
    rw [abs_mul, abs_of_nonneg hbeta]
    have hm := mul_le_mul_of_nonneg_left hsum hbeta
    nlinarith
  have hk := abs_cumulant3_le nu a1 a2 a3 L1 L1 L1 hL1 hL1 hL1 ha1 ha2 ha3
  have hcum : abs (beta ^ 2 * cumulant3 nu a1 a2 a3) <=
      6 * beta ^ 2 * L1 ^ 3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg beta)]
    have hm := mul_le_mul_of_nonneg_left hk (sq_nonneg beta)
    nlinarith
  have hf1 := abs_sub (expectation nu c123)
    (beta * (covariance nu b12 a3 + covariance nu b23 a1 + covariance nu b31 a2))
  have hf2 := abs_add_le
    (expectation nu c123 - beta *
      (covariance nu b12 a3 + covariance nu b23 a1 + covariance nu b31 a2))
    (beta ^ 2 * cumulant3 nu a1 a2 a3)
  unfold scalarThirdExpression
  linarith

end FiniteGibbs
end GaussianEllipsoid
