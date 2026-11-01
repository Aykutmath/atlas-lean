import Section_10_Zonoid.Hypercube.Algebra.Counting
import Section_10_Zonoid.Hypercube.Geometry
import Section_10_Zonoid.Hypercube.Bernoulli
import Mathlib.Data.Finset.Sort

/-
Finite iid sample expectations are written as sums over complete atom labels.
The determinant sampler below proves the actual n! normalization, including
repeated atom labels and repeated geometric rows. The bridge from these finite
sums to a measure-theoretic expectation remains a separate declaration.
-/

noncomputable section

namespace Hypercube.Sampling

variable {Index : Type*} [Fintype Index] [LinearOrder Index] [DecidableEq Index]

def subsetRowDet {n : Nat} (R : Index -> Fin n -> Real) (S : Finset Index) : Real :=
  if hS : S.card = n then
    Matrix.det (fun i j => R (S.orderEmbOfFin hS i) j)
  else 0

omit [Fintype Index] [LinearOrder Index] [DecidableEq Index] in
theorem rowsDet_zero_of_noninjective {n : Nat}
    (R : Index -> Fin n -> Real) (f : Fin n -> Index)
    (hf : Not (Function.Injective f)) :
    Matrix.det (fun i j => R (f i) j) = 0 := by
  have h := Function.not_injective_iff.mp hf
  cases h with
  | intro i h =>
      cases h with
      | intro j h =>
          apply Matrix.det_zero_of_row_eq h.2
          funext k
          rw [h.1]

omit [Fintype Index] [DecidableEq Index] in
theorem rowsDet_abs_embedding {n : Nat}
    (R : Index -> Fin n -> Real) (f : Function.Embedding (Fin n) Index) :
    |Matrix.det (fun i j => R (f i) j)| = |subsetRowDet R (Counting.rangeFinset f)| := by
  let S := Counting.rangeFinset f
  have hS : S.card = n := Counting.range_card f
  let ef : Equiv (Fin n) S := Counting.fiberEquiv n S (Subtype.mk f rfl)
  let es : Equiv (Fin n) S := (S.orderIsoOfFin hS).toEquiv
  let p : Equiv.Perm (Fin n) := ef.trans es.symm
  have hrow (i : Fin n) : S.orderEmbOfFin hS (p i) = f i := by
    change (es (es.symm (ef i))).val = f i
    rw [es.apply_symm_apply]
    rfl
  let M : Matrix (Fin n) (Fin n) Real := fun i j => R (S.orderEmbOfFin hS i) j
  have hmatrix : (fun i j => R (f i) j) = M.submatrix p (Equiv.refl (Fin n)) := by
    funext i j
    simp only [M, Matrix.submatrix, Equiv.refl_apply, hrow]
    rfl
  change |Matrix.det (fun i j => R (f i) j)| = |subsetRowDet R S|
  rw [hmatrix, Matrix.abs_det_submatrix_equiv_equiv]
  simp only [subsetRowDet, dite_eq_left hS, M]

theorem finite_absdet_normalization (n : Nat) (q : Index -> Real)
    (R : Index -> Fin n -> Real) :
    Finset.sum Finset.univ
      (fun f : Fin n -> Index =>
        Finset.prod Finset.univ (fun i => q (f i)) *
          |Matrix.det (fun i j => R (f i) j)|) =
      (n.factorial : Real) * Finset.sum
        (Finset.univ.filter (fun S : Finset Index => S.card = n))
        (fun S => Finset.prod S q * |subsetRowDet R S|) := by
  apply Counting.weighted_tuples_vanishing_repeats
  case hgood =>
    intro f
    exact rowsDet_abs_embedding R f
  case hrepeat =>
    intro f hf
    rw [rowsDet_zero_of_noninjective R f hf, abs_zero]

omit [Fintype Index] in
theorem orderEmb_erase_succAbove {n : Nat}
    (J : Finset Index) (hJ : J.card = n + 1) (r : Fin (n + 1))
    (hI : (J.erase (J.orderEmbOfFin hJ r)).card = n) (j : Fin n) :
    (J.erase (J.orderEmbOfFin hJ r)).orderEmbOfFin hI j =
      J.orderEmbOfFin hJ (r.succAbove j) := by
  let e := J.orderEmbOfFin hJ
  have he : (r.succAboveOrderEmb.trans e) =
      (J.erase (e r)).orderEmbOfFin hI := by
    apply Finset.orderEmbOfFin_unique' hI
    intro a
    apply Finset.mem_erase.mpr
    constructor
    case left =>
      intro h
      exact Fin.succAbove_ne r a (e.injective h)
    case right => exact J.orderEmbOfFin_mem hJ (r.succAbove a)
  exact congrArg (fun f => f j) he.symm

def finiteExpectation {N n : Nat} (q : Fin N -> Real)
    (F : (Fin n -> Fin N) -> Real) : Real :=
  Finset.sum Finset.univ
    (fun f : Fin n -> Fin N => Finset.prod Finset.univ (fun i => q (f i)) * F f)

theorem subsetRowDet_affine {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) :
    subsetRowDet (fun x => Fin.lastCases 1 (w x)) I = Bernoulli.subsetAffineDet w I := rfl

theorem finite_affineDet_normalization {N m : Nat}
    (q : Fin N -> Real) (w : Fin N -> Geometry.Point m) :
    finiteExpectation q
      (fun f : Fin (m + 1) -> Fin N => |Geometry.affineDet (fun i => w (f i))|) =
      ((m + 1).factorial : Real) * Bernoulli.finiteD q (Bernoulli.subsetAffineDet w) m := by
  have h := finite_absdet_normalization (m + 1) q (fun x => Fin.lastCases 1 (w x))
  change Finset.sum Finset.univ
    (fun f : Fin (m + 1) -> Fin N => Finset.prod Finset.univ (fun i => q (f i)) *
      |Matrix.det (fun i j => Fin.lastCases 1 (w (f i)) j)|) = _
  simpa only [Bernoulli.finiteD, Finset.univ_filter_card_eq, subsetRowDet_affine] using h

theorem finite_cofactor_omission {N m : Nat}
    (q : Fin N -> Real) (hqsum : Finset.sum Finset.univ q = 1)
    (w : Fin N -> Geometry.Point m) (i : Fin (m + 2)) :
    finiteExpectation q
      (fun f : Fin (m + 2) -> Fin N => |Geometry.cofactor (fun j => w (f j)) i|) =
      finiteExpectation q
        (fun f : Fin (m + 1) -> Fin N => |Geometry.affineDet (fun j => w (f j))|) := by
  have h := Counting.weighted_omission_sum (m + 1) q hqsum
    (fun f : Fin (m + 1) -> Fin N => |Geometry.affineDet (fun j => w (f j))|) i
  simpa only [finiteExpectation, Geometry.cofactor, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul] using h

theorem finite_radonMass_normalization {N m : Nat}
    (q : Fin N -> Real) (hqsum : Finset.sum Finset.univ q = 1)
    (w : Fin N -> Geometry.Point m) :
    finiteExpectation q
      (fun f : Fin (m + 2) -> Fin N => Geometry.radonMass (fun j => w (f j))) =
      ((m + 2).factorial : Real) / 2 *
        Bernoulli.finiteD q (Bernoulli.subsetAffineDet w) m := by
  let E := finiteExpectation q
    (fun f : Fin (m + 1) -> Fin N => |Geometry.affineDet (fun j => w (f j))|)
  have hpoint (f : Fin (m + 2) -> Fin N) :
      Finset.prod Finset.univ (fun i => q (f i)) *
          Geometry.radonMass (fun j => w (f j)) =
        (1 / 2 : Real) * Finset.sum Finset.univ
          (fun i => Finset.prod Finset.univ (fun j => q (f j)) *
            |Geometry.cofactor (fun j => w (f j)) i|) := by
    unfold Geometry.radonMass
    rw [<- Finset.mul_sum]
    ring
  unfold finiteExpectation
  simp_rw [hpoint]
  rw [<- Finset.mul_sum, Finset.sum_comm]
  have hcofactor (i : Fin (m + 2)) :
      Finset.sum Finset.univ
        (fun f : Fin (m + 2) -> Fin N => Finset.prod Finset.univ (fun j => q (f j)) *
          |Geometry.cofactor (fun j => w (f j)) i|) = E :=
    finite_cofactor_omission q hqsum w i
  simp_rw [hcofactor]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [E]
  rw [finite_affineDet_normalization]
  have hfac : ((m + 2).factorial : Real) =
      ((m + 2 : Nat) : Real) * ((m + 1).factorial : Real) := by
    exact_mod_cast Nat.factorial_succ (m + 1)
  rw [hfac]
  ring

theorem subsetAffineDet_erase {N m : Nat} (w : Fin N -> Geometry.Point m)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) (r : Fin (m + 2)) :
    Bernoulli.subsetAffineDet w (J.erase (J.orderEmbOfFin hJ r)) =
      Geometry.affineDet (fun j => w (J.orderEmbOfFin hJ (r.succAbove j))) := by
  have hmem := J.orderEmbOfFin_mem hJ r
  have hI : (J.erase (J.orderEmbOfFin hJ r)).card = m + 1 := by
    have hcard := Finset.card_erase_add_one hmem
    rw [hJ] at hcard
    omega
  rw [Bernoulli.subsetAffineDet_of_card w _ hI]
  congr 1
  funext j
  rw [orderEmb_erase_succAbove J hJ r hI j]

theorem increasing_sum_eq_cofactor_sum {N m : Nat}
    (w : Fin N -> Geometry.Point m) (X : Fin N -> Real)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) :
    BinaryCocycle.increasingAlternatingSum X (Bernoulli.subsetAffineDet w) J =
      Finset.sum Finset.univ (fun i : Fin (m + 2) =>
        Geometry.cofactor (fun r => w (J.orderEmbOfFin hJ r)) i *
          X (J.orderEmbOfFin hJ i)) := by
  unfold BinaryCocycle.increasingAlternatingSum
  apply Fintype.sum_equiv (Fin.castOrderIso hJ).toEquiv
  intro r
  let i := (Fin.castOrderIso hJ).toEquiv r
  have he : J.orderEmbOfFin rfl r = J.orderEmbOfFin hJ i := by
    apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
    rfl
  change (-1 : Real) ^ r.val * X (J.orderEmbOfFin rfl r) *
      Bernoulli.subsetAffineDet w (J.erase (J.orderEmbOfFin rfl r)) =
    Geometry.cofactor (fun a => w (J.orderEmbOfFin hJ a)) i * X (J.orderEmbOfFin hJ i)
  rw [he, subsetAffineDet_erase w J hJ i]
  unfold Geometry.cofactor
  have hi : i.val = r.val := rfl
  rw [hi]
  ring

theorem finite_height_normalization {N m : Nat}
    (q X : Fin N -> Real) (w : Fin N -> Geometry.Point m) :
    finiteExpectation q (fun f : Fin (m + 2) -> Fin N =>
      |Finset.sum Finset.univ (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) =
      ((m + 2).factorial : Real) *
        Bernoulli.finiteL q X (Bernoulli.subsetAffineDet w) m := by
  let R : Fin N -> Fin (m + 2) -> Real :=
    fun x => Fin.lastCases 1 (Fin.lastCases (X x) (w x))
  have h := finite_absdet_normalization (m + 2) q R
  have hleft (f : Fin (m + 2) -> Fin N) :
      |Matrix.det (fun i j => R (f i) j)| =
        |Finset.sum Finset.univ
          (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))| := by
    exact Geometry.paper_height_absolute_determinant (fun i => w (f i)) (fun i => X (f i))
  unfold finiteExpectation
  simp_rw [hleft] at h
  rw [h]
  unfold Bernoulli.finiteL
  rw [Finset.univ_filter_card_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJmem
  have hJ : J.card = m + 2 := Finset.mem_powersetCard_univ.mp hJmem
  congr 1
  unfold subsetRowDet
  rw [dite_eq_left hJ]
  change |Geometry.affineDet (fun i => Geometry.liftedPoint
    (w (J.orderEmbOfFin hJ i)) (X (J.orderEmbOfFin hJ i)))| = _
  rw [Geometry.paper_height_absolute_determinant,
    <- increasing_sum_eq_cofactor_sum w X J hJ]

end Hypercube.Sampling
