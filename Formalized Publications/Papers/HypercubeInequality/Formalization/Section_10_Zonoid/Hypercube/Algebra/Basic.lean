import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Hypercube.Algebra

/- Source: hypercube_readable.tex, Lemma Weighted binary cocycle inequality.
These scalar facts are the discrete and variance steps of that lemma.
The finite-subset wedge norm bound is a separate proof obligation. -/

theorem integer_abs_le_square (z : Int) :
    |(z : Real)| <= (z : Real) ^ 2 := by
  by_cases hz : z = 0
  case pos =>
    subst z
    norm_num
  case neg =>
    have hzabs : (1 : Int) <= |z| := by
      have hpos : 0 < |z| := abs_pos.mpr hz
      omega
    have habs : (1 : Real) <= |(z : Real)| := by
      exact_mod_cast hzabs
    nlinarith [sq_abs (z : Real)]

theorem signed_unit_square (h : Real)
    (hh : Or (h = -1) (Or (h = 0) (h = 1))) :
    h ^ 2 = |h| := by
  rcases hh with hh | hh | hh
  all_goals subst h; norm_num

theorem binary_square (f : Real) (hf : Or (f = 0) (f = 1)) :
    f ^ 2 = f := by
  rcases hf with hf | hf
  all_goals subst f; norm_num

theorem weighted_binary_variance {Index : Type*} [Fintype Index]
    (q f : Index -> Real)
    (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    Finset.sum Finset.univ (fun i => q i * (f i - p) ^ 2) =
      p * (1 - p) := by
  dsimp only
  let p := Finset.sum Finset.univ (fun i => q i * f i)
  change Finset.sum Finset.univ (fun i => q i * (f i - p) ^ 2) =
    p * (1 - p)
  have hpoint (i : Index) :
      q i * (f i - p) ^ 2 =
        q i * f i - (2 * p) * (q i * f i) + p ^ 2 * q i := by
    have hf := binary_square (f i) (hbinary i)
    calc
      q i * (f i - p) ^ 2 =
          q i * f i ^ 2 - (2 * p) * (q i * f i) + p ^ 2 * q i := by ring
      _ = q i * f i - (2 * p) * (q i * f i) + p ^ 2 * q i := by rw [hf]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [<- Finset.mul_sum, <- Finset.mul_sum]
  change p - (2 * p) * p + p ^ 2 * Finset.sum Finset.univ q =
    p * (1 - p)
  rw [hqsum]
  ring

theorem weighted_binary_mean_bounds {Index : Type*} [Fintype Index]
    (q f : Index -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    And (0 <= p) (p <= 1) := by
  dsimp only
  constructor
  case left =>
    apply Finset.sum_nonneg
    intro i _
    rcases hbinary i with hf | hf
    all_goals rw [hf]; nlinarith [hq i]
  case right =>
    rw [<- hqsum]
    apply Finset.sum_le_sum
    intro i _
    rcases hbinary i with hf | hf
    all_goals rw [hf]; nlinarith [hq i]

theorem weighted_integer_rounding {Index : Type*} [Fintype Index]
    (weight : Index -> Real) (s : Index -> Int)
    (hweight : forall i, 0 <= weight i) :
    Finset.sum Finset.univ (fun i => weight i * |(s i : Real)|) <=
      Finset.sum Finset.univ (fun i => weight i * (s i : Real) ^ 2) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (integer_abs_le_square (s i)) (hweight i)

theorem square_root_weighted_binary_variance {Index : Type*} [Fintype Index]
    (q f : Index -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    Finset.sum Finset.univ
      (fun i => (Real.sqrt (q i) * (f i - p)) ^ 2) = p * (1 - p) := by
  dsimp only
  let p := Finset.sum Finset.univ (fun i => q i * f i)
  change Finset.sum Finset.univ
    (fun i => (Real.sqrt (q i) * (f i - p)) ^ 2) = p * (1 - p)
  calc
    Finset.sum Finset.univ
        (fun i => (Real.sqrt (q i) * (f i - p)) ^ 2) =
        Finset.sum Finset.univ (fun i => q i * (f i - p) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, Real.sq_sqrt (hq i)]
    _ = p * (1 - p) := weighted_binary_variance q f hqsum hbinary

theorem square_root_product_square {Index : Type*}
    (q : Index -> Real) (hq : forall i, 0 <= q i) (I : Finset Index) :
    (Finset.prod I (fun i => Real.sqrt (q i))) ^ 2 = Finset.prod I q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_pow,
        Real.sq_sqrt (hq i), ih]

end Hypercube.Algebra
