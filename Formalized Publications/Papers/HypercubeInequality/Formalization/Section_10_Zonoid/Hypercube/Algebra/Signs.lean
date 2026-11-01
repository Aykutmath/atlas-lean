import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Hypercube.BinaryCocycle

variable {Index : Type*} [LinearOrder Index] [DecidableEq Index]

def toggle (i : Index) (S : Finset Index) : Finset Index :=
  if Membership.mem S i then S.erase i else insert i S

def sign (i : Index) (S : Finset Index) : Real :=
  Finset.prod S (fun j => if j < i then (-1 : Real) else 1)

theorem sign_sq (i : Index) (S : Finset Index) : (sign i S) ^ 2 = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [sign]
  | @insert j S hj ih =>
      simp only [sign, Finset.prod_insert hj, mul_pow] at *
      by_cases hji : j < i
      all_goals simp [hji, ih]

theorem sign_insert (i j : Index) (S : Finset Index)
    (hj : Not (Membership.mem S j)) :
    sign i (insert j S) = sign i S * (if j < i then (-1 : Real) else 1) := by
  simp only [sign, Finset.prod_insert hj]
  ring

omit [LinearOrder Index] in
theorem toggle_self (i : Index) (S : Finset Index) :
    toggle i (toggle i S) = S := by
  by_cases hi : Membership.mem S i
  all_goals simp [toggle, hi]

theorem sign_toggle (i j : Index) (S : Finset Index) :
    sign i (toggle j S) = sign i S * (if j < i then (-1 : Real) else 1) := by
  by_cases hj : Membership.mem S j
  case pos =>
    have hnot : Not (Membership.mem (S.erase j) j) := by simp
    have hins := sign_insert i j (S.erase j) hnot
    rw [Finset.insert_erase hj] at hins
    simp only [toggle, ite_eq_left hj]
    by_cases hji : j < i
    case pos =>
      simp only [ite_eq_left hji] at *
      nlinarith
    case neg =>
      simp only [ite_eq_right hji, mul_one] at *
      exact hins.symm
  case neg =>
    simp only [toggle, ite_eq_right hj]
    exact sign_insert i j S hj

theorem sign_toggle_self (i : Index) (S : Finset Index) :
    sign i (toggle i S) = sign i S := by
  simpa using sign_toggle i i S

omit [LinearOrder Index] in
theorem mem_toggle (i j : Index) (S : Finset Index) :
    Membership.mem (toggle i S) j <->
      if j = i then Not (Membership.mem S i) else Membership.mem S j := by
  by_cases hi : Membership.mem S i
  all_goals by_cases hji : j = i
  all_goals simp [toggle, hi, hji]

omit [LinearOrder Index] in
theorem toggle_comm (i j : Index) (S : Finset Index) :
    toggle i (toggle j S) = toggle j (toggle i S) := by
  apply Finset.ext
  intro a
  by_cases hai : a = i
  all_goals by_cases haj : a = j
  all_goals by_cases hij : i = j
  all_goals simp [mem_toggle, hai, haj, hij, eq_comm]

def toggleEquiv (i : Index) : Equiv (Finset Index) (Finset Index) where
  toFun := toggle i
  invFun := toggle i
  left_inv := toggle_self i
  right_inv := toggle_self i

theorem sign_rank (i : Index) (S : Finset Index) :
    sign i S = (-1 : Real) ^ (S.filter (fun j => j < i)).card := by
  induction S using Finset.induction_on with
  | empty => simp [sign]
  | @insert j S hj ih =>
      rw [sign_insert i j S hj]
      by_cases hji : j < i
      case pos =>
        have hnot : Not (Membership.mem (S.filter (fun a => a < i)) j) := by
          intro hm
          exact hj (Finset.mem_filter.mp hm).1
        simp only [Finset.filter_insert, ite_eq_left hji,
          Finset.card_insert_of_notMem hnot, pow_succ, ih]
      case neg =>
        simp only [Finset.filter_insert, ite_eq_right hji, mul_one, ih]

omit [LinearOrder Index] in
theorem card_toggle_of_mem (i : Index) (S : Finset Index)
    (hi : Membership.mem S i) : (toggle i S).card + 1 = S.card := by
  simp only [toggle, ite_eq_left hi]
  exact Finset.card_erase_add_one hi

omit [LinearOrder Index] in
theorem card_toggle_of_not_mem (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) : (toggle i S).card = S.card + 1 := by
  simp only [toggle, ite_eq_right hi]
  exact Finset.card_insert_of_notMem hi

theorem sign_erase_self (i : Index) (S : Finset Index) :
    sign i (S.erase i) = sign i S := by
  by_cases hi : Membership.mem S i
  case pos => simpa [toggle, hi] using sign_toggle_self i S
  case neg => simp [Finset.erase_eq_of_notMem hi]

omit [DecidableEq Index] in
theorem card_filter_lt_orderEmbOfFin (S : Finset Index) (r : Fin S.card) :
    (S.filter (fun j => j < S.orderEmbOfFin rfl r)).card = r.val := by
  let e := S.orderEmbOfFin rfl
  have hfilter : S.filter (fun j => j < e r) = (Finset.Iio r).map e.toEmbedding := by
    apply Finset.ext
    intro a
    constructor
    case mp =>
      intro ha
      have ha' := Finset.mem_filter.mp ha
      have hpre : Exists (fun l : Fin S.card => e l = a) := by
        have hmem : Membership.mem (Set.range e) a := by
          change Membership.mem (Set.range (S.orderEmbOfFin rfl)) a
          rw [Finset.range_orderEmbOfFin]
          exact ha'.1
        exact hmem
      let l := Classical.choose hpre
      have hl : e l = a := Classical.choose_spec hpre
      have hlr : l < r := e.lt_iff_lt.mp (by rw [hl]; exact ha'.2)
      exact Finset.mem_map.mpr
        (Exists.intro l (And.intro (Finset.mem_Iio.mpr hlr) hl))
    case mpr =>
      intro ha
      have hpre := Finset.mem_map.mp ha
      cases hpre with
      | intro l hl =>
          apply Finset.mem_filter.mpr
          rw [<- hl.2]
          exact And.intro (S.orderEmbOfFin_mem rfl l)
            (e.strictMono (Finset.mem_Iio.mp hl.1))
  change (S.filter (fun j => j < e r)).card = r.val
  rw [hfilter, Finset.card_map]
  exact Fin.card_Iio r

theorem sign_at_increasing_index (S : Finset Index) (r : Fin S.card) :
    sign (S.orderEmbOfFin rfl r) (S.erase (S.orderEmbOfFin rfl r)) =
      (-1 : Real) ^ r.val := by
  rw [sign_erase_self, sign_rank, card_filter_lt_orderEmbOfFin]

end Hypercube.BinaryCocycle
