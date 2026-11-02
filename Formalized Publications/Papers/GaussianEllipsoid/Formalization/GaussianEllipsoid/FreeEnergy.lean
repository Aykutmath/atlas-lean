/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.

Kernel-checked finite free-energy identities, bounds, and hybrid telescoping.
Source: paper.tex, lines 3832-3931 and 4178-4190.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid
namespace FiniteFreeEnergy

theorem divide_le_of_le_mul {a b c : Real} (hb : 0 < b) (h : a <= c * b) :
    a / b <= c := by
  calc
    a / b <= (c * b) / b := div_le_div_of_nonneg_right h hb.le
    _ = c := by field_simp [ne_of_gt hb]

theorem le_divide_of_mul_le {a b c : Real} (hb : 0 < b) (h : a * b <= c) :
    a <= c / b := by
  calc
    a = (a * b) / b := by field_simp [ne_of_gt hb]
    _ <= c / b := div_le_div_of_nonneg_right h hb.le

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The unnormalized finite partition sum. -/
def partitionSum (beta : Real) (H : I -> Real) : Real :=
  Finset.univ.sum (fun u => Real.exp (-beta * H u))

/-- The partition function with the uniform candidate prior. -/
def partitionAverage (beta : Real) (H : I -> Real) : Real :=
  partitionSum beta H / (Fintype.card I : Real)

/-- The paper's normalized negative log partition function. -/
def freeEnergy (beta : Real) (n : Nat) (H : I -> Real) : Real :=
  -Real.log (partitionAverage beta H) / (beta * (n : Real))

theorem card_pos_real : 0 < (Fintype.card I : Real) := by
  exact_mod_cast Fintype.card_pos

theorem partitionSum_pos (beta : Real) (H : I -> Real) :
    0 < partitionSum beta H := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem partitionAverage_pos (beta : Real) (H : I -> Real) :
    0 < partitionAverage beta H := by
  exact div_pos (partitionSum_pos beta H) card_pos_real

theorem freeEnergy_log_sum (beta : Real) (n : Nat) (H : I -> Real) :
    freeEnergy beta n H = -Real.log (partitionSum beta H) / (beta * (n : Real)) +
      Real.log (Fintype.card I : Real) / (beta * (n : Real)) := by
  unfold freeEnergy partitionAverage
  rw [Real.log_div (ne_of_gt (partitionSum_pos beta H)) (ne_of_gt card_pos_real)]
  ring

/-- A minimizer is selected from the actual nonempty finite candidate family. -/
def minimizer (H : I -> Real) : I :=
  Classical.choose (Finset.exists_min_image Finset.univ H Finset.univ_nonempty)

def candidateMin (H : I -> Real) : Real := H (minimizer H)

theorem candidateMin_le (H : I -> Real) (u : I) : candidateMin H <= H u := by
  exact (Classical.choose_spec
    (Finset.exists_min_image Finset.univ H Finset.univ_nonempty)).2 u
      (Finset.mem_univ u)

theorem candidateMin_attained (H : I -> Real) : exists u, H u = candidateMin H :=
  Exists.intro (minimizer H) rfl

theorem partitionAverage_const (beta c : Real) :
    partitionAverage beta (fun _ : I => c) = Real.exp (-beta * c) := by
  have hcard : Not ((Fintype.card I : Real) = 0) := ne_of_gt card_pos_real
  simp only [partitionAverage, partitionSum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hcard]

theorem freeEnergy_const (beta : Real) (n : Nat) (hbeta : 0 < beta)
    (hn : 0 < n) (c : Real) :
    freeEnergy beta n (fun _ : I => c) = c / (n : Real) := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hn
  rw [freeEnergy, partitionAverage_const, Real.log_exp]
  field_simp [ne_of_gt hbeta, hnR]

theorem partitionAverage_antitone (beta : Real) (hbeta : 0 <= beta)
    {H K : I -> Real} (hHK : forall u, H u <= K u) :
    partitionAverage beta K <= partitionAverage beta H := by
  apply div_le_div_of_nonneg_right _ (le_of_lt card_pos_real)
  apply Finset.sum_le_sum
  intro u _
  apply Real.exp_le_exp.mpr
  nlinarith [hHK u]

theorem freeEnergy_mono (beta : Real) (n : Nat) (hbeta : 0 < beta)
    (hn : 0 < n) {H K : I -> Real} (hHK : forall u, H u <= K u) :
    freeEnergy beta n H <= freeEnergy beta n K := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hlog : Real.log (partitionAverage beta K) <=
      Real.log (partitionAverage beta H) :=
    Real.log_le_log (partitionAverage_pos beta K)
      (partitionAverage_antitone beta hbeta.le hHK)
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (mul_pos hbeta hnR).le

omit [Nonempty I] in
theorem partitionAverage_shift (beta c : Real) (H : I -> Real) :
    partitionAverage beta (fun u => H u + c) =
      Real.exp (-beta * c) * partitionAverage beta H := by
  unfold partitionAverage partitionSum
  have he : forall u, Real.exp (-beta * (H u + c)) =
      Real.exp (-beta * c) * Real.exp (-beta * H u) := by
    intro u
    rw [show -beta * (H u + c) = -beta * c + -beta * H u by ring,
      Real.exp_add]
  simp_rw [he]
  rw [<- Finset.mul_sum]
  ring

theorem freeEnergy_shift (beta : Real) (n : Nat) (hbeta : 0 < beta)
    (hn : 0 < n) (H : I -> Real) (c : Real) :
    freeEnergy beta n (fun u => H u + c) =
      freeEnergy beta n H + c / (n : Real) := by
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hn
  unfold freeEnergy
  rw [partitionAverage_shift, Real.log_mul (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (partitionAverage_pos beta H)), Real.log_exp]
  field_simp [ne_of_gt hbeta, hnR]
  ring

theorem min_div_le_freeEnergy (beta : Real) (n : Nat) (hbeta : 0 < beta)
    (hn : 0 < n) (H : I -> Real) :
    candidateMin H / (n : Real) <= freeEnergy beta n H := by
  rw [<- freeEnergy_const (I := I) beta n hbeta hn (candidateMin H)]
  exact freeEnergy_mono beta n hbeta hn (candidateMin_le H)

theorem min_term_le_partitionAverage (beta : Real) (H : I -> Real) :
    Real.exp (-beta * candidateMin H) / (Fintype.card I : Real) <=
      partitionAverage beta H := by
  apply div_le_div_of_nonneg_right _ (le_of_lt card_pos_real)
  unfold partitionSum candidateMin
  exact Finset.single_le_sum (f := fun u => Real.exp (-beta * H u))
    (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ (minimizer H))

theorem partitionAverage_min_bounds (beta : Real) (hbeta : 0 <= beta) (H : I -> Real) :
    Real.exp (-beta * candidateMin H) / (Fintype.card I : Real) <=
      partitionAverage beta H /\
    partitionAverage beta H <= Real.exp (-beta * candidateMin H) := by
  constructor
  case left =>
    exact min_term_le_partitionAverage beta H
  case right =>
    rw [<- partitionAverage_const (I := I) beta (candidateMin H)]
    exact partitionAverage_antitone beta hbeta (candidateMin_le H)

theorem freeEnergy_le_min_add_entropy (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (H : I -> Real) :
    freeEnergy beta n H <= candidateMin H / (n : Real) +
      Real.log (Fintype.card I : Real) / (beta * (n : Real)) := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hbN : 0 < beta * (n : Real) := mul_pos hbeta hnR
  have hlog := Real.log_le_log
    (div_pos (Real.exp_pos (-beta * candidateMin H)) card_pos_real)
    (min_term_le_partitionAverage beta H)
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt card_pos_real),
    Real.log_exp] at hlog
  unfold freeEnergy
  apply divide_le_of_le_mul hbN
  have halg : (candidateMin H / (n : Real) +
      Real.log (Fintype.card I : Real) / (beta * (n : Real))) *
      (beta * (n : Real)) =
      beta * candidateMin H + Real.log (Fintype.card I : Real) := by
    field_simp [ne_of_gt hbeta, ne_of_gt hnR]
  rw [halg]
  linarith

/-- Exact paper bounds, without an assumed minimum or an entropy approximation. -/
theorem freeEnergy_min_bounds (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (H : I -> Real) :
    candidateMin H / (n : Real) <= freeEnergy beta n H /\
    freeEnergy beta n H <= candidateMin H / (n : Real) +
      Real.log (Fintype.card I : Real) / (beta * (n : Real)) :=
  And.intro (min_div_le_freeEnergy beta n hbeta hn H)
    (freeEnergy_le_min_add_entropy beta n hbeta hn H)

/-- The usual entropy choice produces the requested deterministic error. -/
theorem freeEnergy_min_error (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (H : I -> Real) (err : Real)
    (hentropy : Real.log (Fintype.card I : Real) <= err * beta * (n : Real)) :
    freeEnergy beta n H <= candidateMin H / (n : Real) + err := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hq : Real.log (Fintype.card I : Real) / (beta * (n : Real)) <= err := by
    apply divide_le_of_le_mul (mul_pos hbeta hnR)
    nlinarith [hentropy]
  exact (freeEnergy_le_min_add_entropy beta n hbeta hn H).trans
    (add_le_add_right hq _)

/-- The manuscript's theta/16 specialization, using its inherited entropy bound. -/
theorem freeEnergy_theta_error (beta theta Rstar : Real) (n : Nat)
    (hbeta : 0 < beta) (htheta : 0 < theta) (hn : 0 < n) (H : I -> Real)
    (hentropy : Real.log (Fintype.card I : Real) / (n : Real) <= Rstar)
    (hchoice : 16 * Rstar / theta <= beta) :
    candidateMin H / (n : Real) <= freeEnergy beta n H /\
      freeEnergy beta n H <= candidateMin H / (n : Real) + theta / 16 := by
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hlog := mul_le_mul_of_nonneg_right hentropy hnR.le
  have hcancel : (Real.log (Fintype.card I : Real) / (n : Real)) * (n : Real) =
      Real.log (Fintype.card I : Real) := by field_simp [ne_of_gt hnR]
  rw [hcancel] at hlog
  have hR := mul_le_mul_of_nonneg_right hchoice htheta.le
  have hcancelR : (16 * Rstar / theta) * theta = 16 * Rstar := by
    field_simp [ne_of_gt htheta]
  rw [hcancelR] at hR
  have hR' : Rstar <= (theta / 16) * beta := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hR' hnR.le
  have hscaled : Real.log (Fintype.card I : Real) <=
      (theta / 16) * beta * (n : Real) := hlog.trans hprod
  exact And.intro (min_div_le_freeEnergy beta n hbeta hn H)
    (freeEnergy_min_error beta n hbeta hn H (theta / 16) hscaled)

theorem candidate_min_of_freeEnergy_margin (beta theta Rstar : Real) (n : Nat)
    (hbeta : 0 < beta) (htheta : 0 < theta) (hn : 0 < n) (H : I -> Real)
    (hentropy : Real.log (Fintype.card I : Real) / (n : Real) <= Rstar)
    (hchoice : 16 * Rstar / theta <= beta)
    (hmargin : 3 * theta / 4 <= freeEnergy beta n H) :
    11 * theta / 16 <= candidateMin H / (n : Real) := by
  have happrox := (freeEnergy_theta_error beta theta Rstar n hbeta htheta hn H
    hentropy hchoice).2
  linarith

theorem freeEnergy_uniform_perturbation (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (H K : I -> Real) (delta : Real)
    (hHK : forall u, abs (H u - K u) <= delta) :
    abs (freeEnergy beta n H - freeEnergy beta n K) <= delta / (n : Real) := by
  have hforward : freeEnergy beta n H <= freeEnergy beta n K + delta / (n : Real) := by
    rw [<- freeEnergy_shift beta n hbeta hn K delta]
    apply freeEnergy_mono beta n hbeta hn
    intro u
    have h := (abs_le.mp (hHK u)).2
    linarith
  have hback : freeEnergy beta n K <= freeEnergy beta n H + delta / (n : Real) := by
    rw [<- freeEnergy_shift beta n hbeta hn H delta]
    apply freeEnergy_mono beta n hbeta hn
    intro u
    have h := (abs_le.mp (hHK u)).1
    linarith
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

theorem freeEnergy_mem_unit_interval (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (H : I -> Real)
    (hH : forall u, 0 <= H u /\ H u <= (n : Real)) :
    0 <= freeEnergy beta n H /\ freeEnergy beta n H <= 1 := by
  have hlow := freeEnergy_mono beta n hbeta hn (fun u => (hH u).1)
  have hupp := freeEnergy_mono beta n hbeta hn (fun u => (hH u).2)
  rw [freeEnergy_const beta n hbeta hn 0] at hlow
  rw [freeEnergy_const beta n hbeta hn (n : Real)] at hupp
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hn
  simpa [hnR] using And.intro hlow hupp

/-- Total loss from an actual finite collection of rows. -/
def totalLoss {n : Nat} (loss : Fin n -> I -> Real) (u : I) : Real :=
  Finset.univ.sum (fun i => loss i u)

omit [Nonempty I] in
/-- Explicit equality to the manuscript's uniform-prior log-sum-exp formula. -/
theorem freeEnergy_eq_paperFormula (beta : Real) (n : Nat)
    (loss : Fin n -> I -> Real) :
    freeEnergy beta n (totalLoss loss) =
      -(1 / (beta * (n : Real))) *
        Real.log ((1 / (Fintype.card I : Real)) *
          Finset.univ.sum (fun u => Real.exp (-beta *
            Finset.univ.sum (fun i => loss i u)))) := by
  have harg : partitionAverage beta (totalLoss loss) =
      (1 / (Fintype.card I : Real)) *
        Finset.univ.sum (fun u => Real.exp (-beta *
          Finset.univ.sum (fun i => loss i u))) := by
    unfold partitionAverage partitionSum totalLoss
    ring
  rw [freeEnergy, harg]
  ring

/-- The retained loss after one row is deleted. -/
def deletedLoss {n : Nat} (loss : Fin n -> I -> Real) (m : Fin n) (u : I) : Real :=
  (Finset.univ.erase m).sum (fun i => loss i u)

omit [Fintype I] [Nonempty I] in
theorem totalLoss_eq_deleted_add {n : Nat} (loss : Fin n -> I -> Real)
    (m : Fin n) (u : I) :
    totalLoss loss u = deletedLoss loss m u + loss m u := by
  exact (Finset.sum_erase_add Finset.univ (fun i => loss i u) (Finset.mem_univ m)).symm

omit [Fintype I] [Nonempty I] in
theorem totalLoss_mem_interval {n : Nat} (loss : Fin n -> I -> Real)
    (h : forall i u, 0 <= loss i u /\ loss i u <= 1) (u : I) :
    0 <= totalLoss loss u /\ totalLoss loss u <= (n : Real) := by
  constructor
  case left =>
    exact Finset.sum_nonneg (fun i _ => (h i u).1)
  case right =>
    calc
      totalLoss loss u <= Finset.univ.sum (fun _ : Fin n => (1 : Real)) :=
        Finset.sum_le_sum (fun i _ => (h i u).2)
      _ = (n : Real) := by simp

theorem freeEnergy_of_bounded_rows_mem_unit_interval (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (loss : Fin n -> I -> Real)
    (h : forall i u, 0 <= loss i u /\ loss i u <= 1) :
    0 <= freeEnergy beta n (totalLoss loss) /\
      freeEnergy beta n (totalLoss loss) <= 1 :=
  freeEnergy_mem_unit_interval beta n hbeta hn _ (totalLoss_mem_interval loss h)

omit [Fintype I] [Nonempty I] in
theorem totalLoss_sub_of_one_row {n : Nat} (loss loss' : Fin n -> I -> Real)
    (m : Fin n) (hothers : forall i, Not (i = m) -> forall u, loss i u = loss' i u)
    (u : I) : totalLoss loss u - totalLoss loss' u = loss m u - loss' m u := by
  classical
  unfold totalLoss
  rw [<- Finset.sum_sub_distrib]
  exact Finset.sum_eq_single m
    (fun i _ him => by rw [hothers i him u, sub_self])
    (fun h => False.elim (h (Finset.mem_univ m)))

theorem freeEnergy_row_replacement (beta : Real) (n : Nat)
    (hbeta : 0 < beta) (hn : 0 < n) (loss loss' : Fin n -> I -> Real)
    (m : Fin n) (hothers : forall i, Not (i = m) -> forall u, loss i u = loss' i u)
    (hcurrent : forall u, 0 <= loss m u /\ loss m u <= 1)
    (hcurrent' : forall u, 0 <= loss' m u /\ loss' m u <= 1) :
    abs (freeEnergy beta n (totalLoss loss) - freeEnergy beta n (totalLoss loss'))
      <= 1 / (n : Real) := by
  apply freeEnergy_uniform_perturbation beta n hbeta hn _ _ 1
  intro u
  rw [totalLoss_sub_of_one_row loss loss' m hothers u]
  have h0 := (hcurrent u).1
  have h1 := (hcurrent u).2
  have h0' := (hcurrent' u).1
  have h1' := (hcurrent' u).2
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

/-- Exact finite hybrid telescoping before any expectation is taken. -/
theorem hybrid_telescope {X : Type*} (F : X -> Real) (hybrid : Nat -> X) (n : Nat) :
    F (hybrid n) - F (hybrid 0) =
      (Finset.range n).sum (fun m => F (hybrid (m + 1)) - F (hybrid m)) := by
  simpa using (Finset.sum_range_sub (fun m => F (hybrid m)) n).symm

/-- The literal row-by-row hybrid, with the first m rows taken from Z. -/
def hybridRows {X : Type*} {n : Nat} (Z G : Fin n -> X) (m : Nat) (i : Fin n) : X :=
  if i.val < m then Z i else G i

theorem hybridRows_zero {X : Type*} {n : Nat} (Z G : Fin n -> X) :
    hybridRows Z G 0 = G := by
  funext i
  simp [hybridRows]

theorem hybridRows_full {X : Type*} {n : Nat} (Z G : Fin n -> X) :
    hybridRows Z G n = Z := by
  funext i
  simp [hybridRows, i.isLt]

theorem hybridRows_current {X : Type*} {n : Nat} (Z G : Fin n -> X) (m : Fin n) :
    hybridRows Z G m.val m = G m /\ hybridRows Z G (m.val + 1) m = Z m := by
  simp [hybridRows]

theorem hybridRows_other {X : Type*} {n : Nat} (Z G : Fin n -> X)
    (m i : Fin n) (him : Not (i = m)) :
    hybridRows Z G (m.val + 1) i = hybridRows Z G m.val i := by
  have hval : Not (i.val = m.val) := fun he => him (Fin.ext he)
  by_cases hi : i.val < m.val
  case pos =>
    have hi' : i.val < m.val + 1 := by omega
    simp [hybridRows, hi, hi']
  case neg =>
    have hi' : Not (i.val < m.val + 1) := by omega
    simp [hybridRows, hi, hi']

theorem row_hybrid_telescope {X : Type*} {n : Nat}
    (F : (Fin n -> X) -> Real) (Z G : Fin n -> X) :
    F Z - F G = (Finset.range n).sum (fun m =>
      F (hybridRows Z G (m + 1)) - F (hybridRows Z G m)) := by
  simpa [hybridRows_zero, hybridRows_full] using
    hybrid_telescope F (hybridRows Z G) n

end FiniteFreeEnergy
end GaussianEllipsoid
