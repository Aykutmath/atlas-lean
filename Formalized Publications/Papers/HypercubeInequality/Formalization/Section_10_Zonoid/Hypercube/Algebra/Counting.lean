import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Sum

namespace Hypercube.Counting

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

def rangeFinset {n : Nat} (f : Function.Embedding (Fin n) Index) : Finset Index :=
  Finset.univ.map f

omit [Fintype Index] [DecidableEq Index] in
theorem range_card {n : Nat} (f : Function.Embedding (Fin n) Index) :
    (rangeFinset f).card = n := by
  simp [rangeFinset]

omit [Fintype Index] [DecidableEq Index] in
theorem mem_range {n : Nat} (f : Function.Embedding (Fin n) Index) (x : Index) :
    Membership.mem (rangeFinset f) x <-> Exists (fun i => f i = x) := by
  simp [rangeFinset]

abbrev RangeFiber (n : Nat) (S : Finset Index) : Type _ :=
  {f : Function.Embedding (Fin n) Index // rangeFinset f = S}

noncomputable def fiberEquiv (n : Nat) (S : Finset Index) :
    Equiv (RangeFiber n S) (Equiv (Fin n) S) where
  toFun f := Equiv.ofBijective
    (fun i => Subtype.mk (f.val i) (by
      have hm := (mem_range f.val (f.val i)).mpr (Exists.intro i rfl)
      exact Eq.mp
        (congrArg (fun T : Finset Index => Membership.mem T (f.val i)) f.property) hm))
    (by
      constructor
      case left =>
        intro i j hij
        exact f.val.injective (congrArg Subtype.val hij)
      case right =>
        intro x
        have hx : Membership.mem (rangeFinset f.val) x.val := by
          rw [f.property]
          exact x.property
        obtain h := (mem_range f.val x.val).mp hx
        cases h with
        | intro i hi => exact Exists.intro i (Subtype.ext hi))
  invFun e := Subtype.mk
    { toFun := fun i => (e i).val
      inj' := by
        intro i j hij
        exact e.injective (Subtype.ext hij) }
    (by
      apply Finset.ext
      intro x
      rw [mem_range]
      constructor
      case mp =>
        intro hx
        cases hx with
        | intro i hi =>
            rw [<- hi]
            exact (e i).property
      case mpr =>
        intro hx
        obtain h := e.surjective (Subtype.mk x hx)
        cases h with
        | intro i hi => exact Exists.intro i (congrArg Subtype.val hi))
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

theorem card_fiber (n : Nat) (S : Finset Index) (hS : S.card = n) :
    Fintype.card (RangeFiber n S) = n.factorial := by
  classical
  let e : Equiv (Fin n) S := Fintype.equivOfCardEq (by simp [hS])
  rw [Fintype.card_congr (fiberEquiv n S)]
  simpa using Fintype.card_equiv e

theorem card_fiber_of_wrong_card (n : Nat) (S : Finset Index)
    (hS : Not (S.card = n)) : Fintype.card (RangeFiber n S) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine IsEmpty.mk ?_
  intro f
  apply hS
  rw [<- f.property]
  exact range_card f.val

theorem sum_embeddings_by_range (n : Nat) (F : Finset Index -> Real) :
    Finset.sum Finset.univ
      (fun f : Function.Embedding (Fin n) Index => F (rangeFinset f)) =
      (n.factorial : Real) * Finset.sum
        (Finset.univ.filter (fun S : Finset Index => S.card = n)) F := by
  classical
  let E := Equiv.sigmaFiberEquiv
    (fun f : Function.Embedding (Fin n) Index => rangeFinset f)
  calc
    Finset.sum Finset.univ
        (fun f : Function.Embedding (Fin n) Index => F (rangeFinset f)) =
        Finset.sum Finset.univ
          (fun x : Sigma (RangeFiber n) => F x.fst) := by
      apply Fintype.sum_equiv E.symm
      intro f
      rfl
    _ = Finset.sum Finset.univ
        (fun S : Finset Index => Finset.sum Finset.univ
          (fun _ : RangeFiber n S => F S)) := Fintype.sum_sigma _
    _ = Finset.sum Finset.univ
        (fun S : Finset Index => (Fintype.card (RangeFiber n S) : Real) * F S) := by
      apply Finset.sum_congr rfl
      intro S _
      simp
    _ = Finset.sum Finset.univ
        (fun S : Finset Index => if S.card = n then (n.factorial : Real) * F S else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = n
      case pos => simp [hS, card_fiber n S hS]
      case neg => simp [hS, card_fiber_of_wrong_card n S hS]
    _ = (n.factorial : Real) * Finset.sum
        (Finset.univ.filter (fun S : Finset Index => S.card = n)) F := by
      rw [Finset.mul_sum, Finset.sum_filter]

theorem sum_tuples_vanishing_repeats (n : Nat)
    (H : (Fin n -> Index) -> Real) (F : Finset Index -> Real)
    (hgood : forall f : Function.Embedding (Fin n) Index,
      H f = F (rangeFinset f))
    (hrepeat : forall f : Fin n -> Index,
      Not (Function.Injective f) -> H f = 0) :
    Finset.sum Finset.univ H = (n.factorial : Real) * Finset.sum
      (Finset.univ.filter (fun S : Finset Index => S.card = n)) F := by
  classical
  have hz : Finset.sum Finset.univ
      (fun f : {f : Fin n -> Index // Not (Function.Injective f)} => H f.val) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    exact hrepeat f.val f.property
  calc
    Finset.sum Finset.univ H = Finset.sum Finset.univ
        (fun f : {f : Fin n -> Index // Function.Injective f} => H f.val) := by
      have hp := Fintype.sum_subtype_add_sum_subtype
        (fun f : Fin n -> Index => Function.Injective f) H
      rw [hz, add_zero] at hp
      exact hp.symm
    _ = Finset.sum Finset.univ
        (fun f : Function.Embedding (Fin n) Index => F (rangeFinset f)) := by
      apply Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin n) Index)
      intro f
      exact hgood (Equiv.subtypeInjectiveEquivEmbedding (Fin n) Index f)
    _ = (n.factorial : Real) * Finset.sum
        (Finset.univ.filter (fun S : Finset Index => S.card = n)) F :=
      sum_embeddings_by_range n F

omit [Fintype Index] [DecidableEq Index] in
theorem tuple_mass_range {n : Nat} (q : Index -> Real)
    (f : Function.Embedding (Fin n) Index) :
    Finset.prod Finset.univ (fun i => q (f i)) =
      Finset.prod (rangeFinset f) q := by
  simp [rangeFinset]

theorem weighted_tuples_vanishing_repeats (n : Nat)
    (q : Index -> Real) (G : (Fin n -> Index) -> Real) (A : Finset Index -> Real)
    (hgood : forall f : Function.Embedding (Fin n) Index,
      G f = A (rangeFinset f))
    (hrepeat : forall f : Fin n -> Index,
      Not (Function.Injective f) -> G f = 0) :
    Finset.sum Finset.univ
      (fun f : Fin n -> Index => Finset.prod Finset.univ (fun i => q (f i)) * G f) =
      (n.factorial : Real) * Finset.sum
        (Finset.univ.filter (fun S : Finset Index => S.card = n))
        (fun S => Finset.prod S q * A S) := by
  apply sum_tuples_vanishing_repeats
  case hgood =>
    intro f
    rw [hgood f, tuple_mass_range q f]
  case hrepeat =>
    intro f hf
    rw [hrepeat f hf, mul_zero]

omit [DecidableEq Index] in
theorem weighted_omission_sum (n : Nat) (q : Index -> Real)
    (hqsum : Finset.sum Finset.univ q = 1)
    (H : (Fin n -> Index) -> Real) (i : Fin (n + 1)) :
    Finset.sum Finset.univ
      (fun f : Fin (n + 1) -> Index =>
        Finset.prod Finset.univ (fun j => q (f j)) *
          H (fun j => f (i.succAbove j))) =
      Finset.sum Finset.univ
        (fun f : Fin n -> Index => Finset.prod Finset.univ (fun j => q (f j)) * H f) := by
  classical
  let E := Fin.insertNthEquiv (fun _ : Fin (n + 1) => Index) i
  have hsingle (x : Index) (f : Fin n -> Index) :
      Finset.prod Finset.univ (fun j => q (E (x, f) j)) *
          H (fun j => E (x, f) (i.succAbove j)) =
        q x * (Finset.prod Finset.univ (fun j => q (f j)) * H f) := by
    rw [Fin.prod_univ_succAbove _ i]
    simp only [E, Fin.insertNthEquiv_apply,
      Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact mul_assoc _ _ _
  calc
    Finset.sum Finset.univ
        (fun f : Fin (n + 1) -> Index =>
          Finset.prod Finset.univ (fun j => q (f j)) * H (fun j => f (i.succAbove j))) =
        Finset.sum Finset.univ
          (fun x : Prod Index (Fin n -> Index) =>
            q x.fst * (Finset.prod Finset.univ (fun j => q (x.snd j)) * H x.snd)) := by
      apply Fintype.sum_equiv E.symm
      intro f
      have h := hsingle (E.symm f).fst (E.symm f).snd
      simpa only [E.apply_symm_apply] using h
    _ = Finset.sum Finset.univ (fun x : Index =>
        Finset.sum Finset.univ (fun f : Fin n -> Index =>
          q x * (Finset.prod Finset.univ (fun j => q (f j)) * H f))) :=
      Fintype.sum_prod_type _
    _ = (Finset.sum Finset.univ q) * Finset.sum Finset.univ
        (fun f : Fin n -> Index => Finset.prod Finset.univ (fun j => q (f j)) * H f) := by
      simp_rw [<- Finset.mul_sum]
      rw [<- Finset.sum_mul]
    _ = _ := by rw [hqsum, one_mul]

end Hypercube.Counting
