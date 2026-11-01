import Section_10_Zonoid.Hypercube.Geometry
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Section_10_Zonoid.Hypercube.Geometry.FiberStep

/-!
Signed-simplex cocycle foundations, source lines 235-268.
The pointwise cocycle is proved outside the hulls of pairs of omitted vertices.
The volume-null exceptional-set bridge is kept in the separate CocycleAE module.
The results below do not assume a cocycle or a barycentric-fiber lemma.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.Geometry.Cocycle

def omitted {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (i : Fin (m + 2)) : Fin (m + 1) -> Geometry.Point m :=
  fun j => w (i.succAbove j)

def signedCocycleSum {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (x : Geometry.Point m) : Real :=
  Finset.sum Finset.univ
    (fun i => (-1 : Real) ^ i.val * Geometry.signedSimplex (omitted w i) x)

theorem orientation_zero : Geometry.orientation 0 = 0 := by
  norm_num [Geometry.orientation]

theorem orientation_neg (a : Real) :
    Geometry.orientation (-a) = -Geometry.orientation a := by
  unfold Geometry.orientation
  split_ifs <;> simp_all
  linarith

theorem orientation_negOnePow_mul (r : Nat) (a : Real) :
    Geometry.orientation ((-1 : Real) ^ r * a) =
      (-1 : Real) ^ r * Geometry.orientation a := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ]
    have hprod : (-1 : Real) ^ r * -1 * a = -((-1 : Real) ^ r * a) := by ring
    rw [hprod, orientation_neg, ih]
    ring

theorem signed_cocycle_term {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (i : Fin (m + 2))
    (x : Geometry.Point m) :
    (-1 : Real) ^ i.val * Geometry.signedSimplex (omitted w i) x =
      (Geometry.simplexHull (omitted w i)).indicator
        (fun _ => Geometry.orientation (Geometry.cofactor w i)) x := by
  classical
  unfold Geometry.signedSimplex
  by_cases hx : Membership.mem (Geometry.simplexHull (omitted w i)) x
  case pos =>
    simp only [Set.indicator_apply, ite_eq_left hx]
    exact Eq.symm (orientation_negOnePow_mul i.val (Geometry.affineDet (omitted w i)))
  case neg =>
    simp only [Set.indicator_apply, ite_eq_right hx, mul_zero]

theorem omittedHull_subset_fullHull {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (i : Fin (m + 2)) :
    Geometry.simplexHull (omitted w i) <= convexHull Real (Set.range w) := by
  apply convexHull_mono
  intro x hx
  cases hx with
  | intro j hj =>
    exact Exists.intro (i.succAbove j) hj

theorem signedCocycleSum_outside_fullHull {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : Not (Membership.mem (convexHull Real (Set.range w)) x)) :
    signedCocycleSum w x = 0 := by
  classical
  unfold signedCocycleSum
  apply Finset.sum_eq_zero
  intro i _
  have hxi : Not (Membership.mem (Geometry.simplexHull (omitted w i)) x) :=
    fun hi => hx (omittedHull_subset_fullHull w i hi)
  simp only [Geometry.signedSimplex, Set.indicator_apply, ite_eq_right hxi, mul_zero]

theorem signedCocycleSum_of_all_omission_determinants_zero {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (hz : forall i, Geometry.affineDet (omitted w i) = 0) :
    forall x, signedCocycleSum w x = 0 := by
  intro x
  unfold signedCocycleSum
  apply Finset.sum_eq_zero
  intro i _
  rw [Geometry.signedSimplex_degenerate (omitted w i) (hz i)]
  simp

theorem omitted_range_eq_full_range_of_repetition {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (i j : Fin (m + 2))
    (hij : Not (i = j)) (hw : w i = w j) :
    Set.range (omitted w i) = Set.range w := by
  ext x
  constructor
  case mp =>
    intro hx
    cases hx with
    | intro a ha => exact Exists.intro (i.succAbove a) ha
  case mpr =>
    intro hx
    cases hx with
    | intro k hk =>
      by_cases hki : k = i
      case pos =>
        have hjrange : j ∈ Set.range i.succAbove := by
          rw [Fin.range_succAbove]
          change Not (j = i)
          exact Ne.symm hij
        cases hjrange with
        | intro a ha =>
          refine Exists.intro a ?_
          change w (i.succAbove a) = x
          rw [ha, Eq.symm hw, Eq.symm hki]
          exact hk
      case neg =>
        have hkrange : k ∈ Set.range i.succAbove := by
          rw [Fin.range_succAbove]
          change Not (k = i)
          exact hki
        cases hkrange with
        | intro a ha =>
          refine Exists.intro a ?_
          change w (i.succAbove a) = x
          rw [ha]
          exact hk

theorem cofactor_zero_away_from_repeated_pair {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (i j k : Fin (m + 2))
    (hij : Not (i = j)) (hw : w i = w j)
    (hki : Not (k = i)) (hkj : Not (k = j)) : Geometry.cofactor w k = 0 := by
  have hirange : i ∈ Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    change Not (i = k)
    exact Ne.symm hki
  have hjrange : j ∈ Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    change Not (j = k)
    exact Ne.symm hkj
  cases hirange with
  | intro a ha =>
    cases hjrange with
    | intro b hb =>
      have hab : Not (a = b) := by
        intro hab
        apply hij
        rw [Eq.symm ha, Eq.symm hb, hab]
      have hwab : omitted w k a = omitted w k b := by
        change w (k.succAbove a) = w (k.succAbove b)
        rw [ha, hb]
        exact hw
      have hdet := Geometry.affineDet_zero_of_repeated_point (omitted w k) hab hwab
      unfold Geometry.cofactor
      change (-1 : Real) ^ k.val * Geometry.affineDet (omitted w k) = 0
      rw [hdet, mul_zero]

theorem signedCocycleSum_of_repeated_point {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (i j : Fin (m + 2))
    (hij : Not (i = j)) (hw : w i = w j) :
    forall x, signedCocycleSum w x = 0 := by
  classical
  have hzero : forall k : Fin (m + 2), Not (k = i) -> Not (k = j) ->
      Geometry.cofactor w k = 0 :=
    fun k hki hkj => cofactor_zero_away_from_repeated_pair w i j k hij hw hki hkj
  have hsum : Finset.sum Finset.univ (Geometry.cofactor w) =
      Geometry.cofactor w i + Geometry.cofactor w j := by
    apply Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    intro k _ hpair
    exact hzero k hpair.1 hpair.2
  have hneg : Geometry.cofactor w j = -Geometry.cofactor w i := by
    have hz := Geometry.cofactor_sum_zero w
    rw [hsum] at hz
    linarith
  have hhi : Geometry.simplexHull (omitted w i) = convexHull Real (Set.range w) := by
    unfold Geometry.simplexHull
    rw [omitted_range_eq_full_range_of_repetition w i j hij hw]
  have hhj : Geometry.simplexHull (omitted w j) = convexHull Real (Set.range w) := by
    unfold Geometry.simplexHull
    rw [omitted_range_eq_full_range_of_repetition w j i (Ne.symm hij) (Eq.symm hw)]
  intro x
  unfold signedCocycleSum
  simp_rw [signed_cocycle_term]
  have hpairsum :
      Finset.sum Finset.univ (fun k =>
        (Geometry.simplexHull (omitted w k)).indicator
          (fun _ => Geometry.orientation (Geometry.cofactor w k)) x) =
      (Geometry.simplexHull (omitted w i)).indicator
        (fun _ => Geometry.orientation (Geometry.cofactor w i)) x +
      (Geometry.simplexHull (omitted w j)).indicator
        (fun _ => Geometry.orientation (Geometry.cofactor w j)) x := by
    apply Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    intro k _ hpair
    rw [hzero k hpair.1 hpair.2, orientation_zero]
    simp
  rw [hpairsum]
  rw [hhi, hhj, hneg, orientation_neg]
  by_cases hx : Membership.mem (convexHull Real (Set.range w)) x
  case pos => simp [hx]
  case neg => simp [hx]

theorem finite_common_exceptional_set {alpha : Type*} [Fintype alpha]
    {m : Nat} (P : alpha -> Geometry.Point m -> Prop)
    (h : forall a, Filter.Eventually (P a) (ae volume)) :
    Filter.Eventually (fun x => forall a, P a x) (ae volume) := by
  exact ae_all_iff.mpr h

/-- The homogeneous equations satisfied by differences of affine representations. -/
def affineKernel {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (v : Fin (m + 2) -> Real) : Prop :=
  And (Finset.sum Finset.univ v = 0)
    (forall j : Fin m, Finset.sum Finset.univ (fun i => v i * w i j) = 0)

theorem cofactor_in_affineKernel {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) : affineKernel w (Geometry.cofactor w) := by
  exact And.intro (Geometry.cofactor_sum_zero w) (Geometry.cofactor_affine_relation w)

theorem omitted_det_nonzero_of_cofactor_nonzero {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (p : Fin (m + 2))
    (hp : Not (Geometry.cofactor w p = 0)) :
    Not (Geometry.affineDet (omitted w p) = 0) := by
  intro hdet
  apply hp
  unfold Geometry.cofactor
  change (-1 : Real) ^ p.val * Geometry.affineDet (omitted w p) = 0
  rw [hdet, mul_zero]

/-- An invertible omission minor forces a homogeneous vector vanishing there to be zero. -/
theorem affineKernel_zero_of_omitted_coordinate_zero {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (p : Fin (m + 2))
    (v : Fin (m + 2) -> Real)
    (hdet : Not (Geometry.affineDet (omitted w p) = 0))
    (hv : affineKernel w v) (hvp : v p = 0) : v = 0 := by
  let A := Geometry.affineMatrix (omitted w p)
  let u : Fin (m + 1) -> Real := fun j => v (p.succAbove j)
  have homit_sum : Finset.sum Finset.univ u = 0 := by
    have hz := hv.1
    rw [Fin.sum_univ_succAbove v p, hvp, zero_add] at hz
    exact hz
  have homit_coord : forall j : Fin m,
      Finset.sum Finset.univ (fun i => u i * w (p.succAbove i) j) = 0 := by
    intro j
    have hz := hv.2 j
    rw [Fin.sum_univ_succAbove (fun i => v i * w i j) p,
      hvp, zero_mul, zero_add] at hz
    exact hz
  have hmul : Matrix.mulVec A.transpose u = 0 := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    next =>
      simpa [Matrix.mulVec, dotProduct, A, Geometry.affineMatrix] using homit_sum
    next =>
      simpa [Matrix.mulVec, dotProduct, A, Geometry.affineMatrix,
        omitted, mul_comm] using homit_coord j
  have hAdet : Not (A.transpose.det = 0) := by
    rw [Matrix.det_transpose]
    exact hdet
  have hu : u = 0 := Matrix.eq_zero_of_mulVec_eq_zero hAdet hmul
  funext i
  by_cases hip : i = p
  case pos => simpa [hip] using hvp
  case neg =>
    have hirange : i ∈ Set.range p.succAbove := by
      rw [Fin.range_succAbove]
      change Not (i = p)
      exact hip
    cases hirange with
    | intro j hj =>
      have hjzero := congrFun hu j
      change v (p.succAbove j) = 0 at hjzero
      rw [hj] at hjzero
      exact hjzero

theorem affineKernel_eq_scalar_cofactor {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (p : Fin (m + 2))
    (hp : Not (Geometry.cofactor w p = 0))
    (v : Fin (m + 2) -> Real) (hv : affineKernel w v) :
    forall i, v i = (v p / Geometry.cofactor w p) * Geometry.cofactor w i := by
  let a := v p / Geometry.cofactor w p
  let r : Fin (m + 2) -> Real := fun i => v i - a * Geometry.cofactor w i
  have hr : affineKernel w r := by
    unfold affineKernel
    constructor
    case left =>
      simp only [r, Finset.sum_sub_distrib, Eq.symm (Finset.mul_sum _ _ _),
        hv.1, Geometry.cofactor_sum_zero, mul_zero, sub_zero]
    case right =>
      intro j
      simp only [r, sub_mul, Finset.sum_sub_distrib, mul_assoc,
        Eq.symm (Finset.mul_sum _ _ _), hv.2 j,
        Geometry.cofactor_affine_relation w j, mul_zero, sub_zero]
  have hrp : r p = 0 := by
    dsimp [r, a]
    field_simp [hp]
    ring
  have hrzero := affineKernel_zero_of_omitted_coordinate_zero w p r
    (omitted_det_nonzero_of_cofactor_nonzero w p hp) hr hrp
  intro i
  have hi := congrFun hrzero i
  change v i - a * Geometry.cofactor w i = 0 at hi
  dsimp [a] at hi
  exact sub_eq_zero.mp hi

def affineRepresentation {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (a : Fin (m + 2) -> Real) (x : Geometry.Point m) : Prop :=
  And (Finset.sum Finset.univ a = 1)
    (forall j : Fin m, Finset.sum Finset.univ (fun i => a i * w i j) = x j)

theorem difference_of_affineRepresentations_in_kernel {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (a b : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha : affineRepresentation w a x) (hb : affineRepresentation w b x) :
    affineKernel w (fun i => a i - b i) := by
  constructor
  case left => simp only [Finset.sum_sub_distrib, ha.1, hb.1, sub_self]
  case right =>
    intro j
    simp only [sub_mul, Finset.sum_sub_distrib, ha.2 j, hb.2 j, sub_self]

theorem affineRepresentation_add_cofactor {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (a : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha : affineRepresentation w a x) (t : Real) :
    affineRepresentation w (fun i => a i + t * Geometry.cofactor w i) x := by
  constructor
  case left =>
    simp only [Finset.sum_add_distrib, Eq.symm (Finset.mul_sum _ _ _),
      ha.1, Geometry.cofactor_sum_zero, mul_zero, add_zero]
  case right =>
    intro j
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc,
      Eq.symm (Finset.mul_sum _ _ _), ha.2 j,
      Geometry.cofactor_affine_relation w j, mul_zero, add_zero]

/-- The paper's affine fiber is exactly a line, without a rank assumption. -/
theorem affineRepresentation_iff_cofactor_line {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (p : Fin (m + 2))
    (hp : Not (Geometry.cofactor w p = 0))
    (a0 : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha0 : affineRepresentation w a0 x) (a : Fin (m + 2) -> Real) :
    affineRepresentation w a x <->
      Exists (fun t : Real => forall i, a i = a0 i + t * Geometry.cofactor w i) := by
  constructor
  case mp =>
    intro ha
    let v : Fin (m + 2) -> Real := fun i => a i - a0 i
    have hv := difference_of_affineRepresentations_in_kernel w a a0 x ha ha0
    refine Exists.intro ((a p - a0 p) / Geometry.cofactor w p) ?_
    intro i
    have hi := affineKernel_eq_scalar_cofactor w p hp v hv i
    dsimp [v] at hi
    linarith
  case mpr =>
    intro h
    cases h with
    | intro t ht =>
      have ha : a = fun i => a0 i + t * Geometry.cofactor w i := funext ht
      rw [ha]
      exact affineRepresentation_add_cofactor w a0 x ha0 t

/-- Convex hull membership uses weights on the given labels, even for repetitions. -/
theorem mem_convexHull_range_iff_nonnegative_weights {n m : Nat}
    (w : Fin n -> Geometry.Point m) (x : Geometry.Point m) :
    Membership.mem (convexHull Real (Set.range w)) x <->
      Exists (fun a : Fin n -> Real =>
        And (forall i, 0 <= a i)
          (And (Finset.sum Finset.univ a = 1)
            (Finset.sum Finset.univ (fun i => HSMul.hSMul (a i) (w i)) = x))) := by
  classical
  constructor
  case mp =>
    intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    cases hx with
    | intro s hs =>
      cases hs with
      | intro b hb =>
        let a : Fin n -> Real := fun i => if Membership.mem s i then b i else 0
        refine Exists.intro a (And.intro ?_ (And.intro ?_ ?_))
        next =>
          intro i
          dsimp [a]
          split_ifs with hi
          next => exact hb.1 i hi
          next => exact le_refl 0
        next =>
          simpa only [a, Finset.sum_ite_mem, Finset.univ_inter] using hb.2.1
        next =>
          have hlin : Finset.sum s (fun i => HSMul.hSMul (b i) (w i)) = x := by
            rw [Eq.symm (Finset.affineCombination_eq_linear_combination s w b hb.2.1)]
            exact hb.2.2
          simpa only [a, ite_smul, zero_smul, Finset.sum_ite_mem,
            Finset.univ_inter] using hlin
  case mpr =>
    intro hx
    cases hx with
    | intro a ha =>
      exact mem_convexHull_of_exists_fintype a w ha.1 ha.2.1
        (fun i => Exists.intro i rfl) ha.2.2

theorem mem_convexHull_range_iff_nonnegative_affineRepresentation {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m) :
    Membership.mem (convexHull Real (Set.range w)) x <->
      Exists (fun a : Fin (m + 2) -> Real =>
        And (forall i, 0 <= a i) (affineRepresentation w a x)) := by
  rw [mem_convexHull_range_iff_nonnegative_weights]
  constructor
  case mp =>
    intro h
    cases h with
    | intro a ha =>
      refine Exists.intro a (And.intro ha.1 (And.intro ha.2.1 ?_))
      intro j
      have hj := congrFun ha.2.2 j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
  case mpr =>
    intro h
    cases h with
    | intro a ha =>
      refine Exists.intro a (And.intro ha.1 (And.intro ha.2.1 ?_))
      funext j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha.2.2 j

def pairHull {m : Nat} (w : Fin (m + 2) -> Geometry.Point m)
    (i j : Fin (m + 2)) : Set (Geometry.Point m) :=
  convexHull Real (w '' Set.ofPred (fun k => And (Not (k = i)) (Not (k = j))))

theorem mem_pairHull_of_two_zero_weights {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (a : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha : affineRepresentation w a x) (hapos : forall k, 0 <= a k)
    (i j : Fin (m + 2)) (hai : a i = 0) (haj : a j = 0) :
    Membership.mem (pairHull w i j) x := by
  classical
  let s := Finset.univ.filter (fun k => Not (a k = 0))
  have hsum : Finset.sum s a = 1 := by
    rw [Eq.symm ha.1]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    have hak : a k = 0 := by
      by_contra hn
      exact hk (Finset.mem_filter.mpr (And.intro (Finset.mem_univ k) hn))
    exact hak
  have hvec : Finset.sum Finset.univ (fun k => HSMul.hSMul (a k) (w k)) = x := by
    funext l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ha.2 l
  have hsvec : Finset.sum s (fun k => HSMul.hSMul (a k) (w k)) = x := by
    rw [Eq.symm hvec]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    have hak : a k = 0 := by
      by_contra hn
      exact hk (Finset.mem_filter.mpr (And.intro (Finset.mem_univ k) hn))
    rw [hak, zero_smul]
  rw [Eq.symm hsvec]
  apply (convex_convexHull Real _).sum_mem
    (fun k _ => hapos k) hsum
  intro k hk
  have hak : Not (a k = 0) := (Finset.mem_filter.mp hk).2
  apply subset_convexHull Real _
  refine Exists.intro k (And.intro (And.intro ?_ ?_) rfl)
  next => intro hki; apply hak; rw [hki, hai]
  next => intro hkj; apply hak; rw [hkj, haj]

theorem positive_weights_outside_pairHulls {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (a : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha : affineRepresentation w a x) (hapos : forall k, 0 <= a k)
    (i : Fin (m + 2)) (hai : a i = 0)
    (hx : forall j, Not (j = i) -> Not (Membership.mem (pairHull w i j) x)) :
    forall j, Not (j = i) -> 0 < a j := by
  intro j hji
  have haj : Not (a j = 0) := by
    intro hz
    exact hx j hji (mem_pairHull_of_two_zero_weights w a x ha hapos i j hai hz)
  exact lt_of_le_of_ne (hapos j) (Ne.symm haj)

theorem omittedHull_weights {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (i : Fin (m + 2)) (x : Geometry.Point m)
    (hx : Membership.mem (Geometry.simplexHull (omitted w i)) x) :
    Exists (fun a : Fin (m + 2) -> Real =>
      And (forall k, 0 <= a k)
        (And (affineRepresentation w a x) (a i = 0))) := by
  classical
  rw [Geometry.simplexHull, mem_convexHull_range_iff_nonnegative_weights] at hx
  cases hx with
  | intro b hb =>
    let a : Fin (m + 2) -> Real := @Fin.insertNth (m + 1) (fun _ => Real) i 0 b
    have hai : a i = 0 := @Fin.insertNth_apply_same (m + 1) (fun _ => Real) i 0 b
    have hab : forall k, a (i.succAbove k) = b k :=
      fun k => @Fin.insertNth_apply_succAbove (m + 1) (fun _ => Real) i 0 b k
    refine Exists.intro a (And.intro ?_ (And.intro ?_ hai))
    next =>
      intro k
      by_cases hki : k = i
      next => rw [hki, hai]
      next =>
        have hkr : k ∈ Set.range i.succAbove := by
          rw [Fin.range_succAbove]
          exact hki
        cases hkr with
        | intro j hj => rw [Eq.symm hj, hab]; exact hb.1 j
    next =>
      constructor
      next =>
        rw [Fin.sum_univ_succAbove a i, hai, zero_add]
        simpa only [hab] using hb.2.1
      next =>
        intro l
        have hl := congrFun hb.2.2 l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hl
        rw [Fin.sum_univ_succAbove (fun k => a k * w k l) i,
          hai, zero_mul, zero_add]
        simpa only [hab, omitted] using hl

theorem omittedHull_of_zero_weight {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m)
    (a : Fin (m + 2) -> Real) (x : Geometry.Point m)
    (ha : affineRepresentation w a x) (hapos : forall k, 0 <= a k)
    (i : Fin (m + 2)) (hai : a i = 0) :
    Membership.mem (Geometry.simplexHull (omitted w i)) x := by
  rw [Geometry.simplexHull, mem_convexHull_range_iff_nonnegative_weights]
  refine Exists.intro (fun k => a (i.succAbove k))
    (And.intro (fun k => hapos (i.succAbove k)) (And.intro ?_ ?_))
  next =>
    have hs := ha.1
    rw [Fin.sum_univ_succAbove a i, hai, zero_add] at hs
    exact hs
  next =>
    funext l
    have hs := ha.2 l
    rw [Fin.sum_univ_succAbove (fun k => a k * w k l) i,
      hai, zero_mul, zero_add] at hs
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, omitted] using hs

theorem opposite_omission_of_positive_cofactor {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x))
    (i : Fin (m + 2)) (hci : 0 < Geometry.cofactor w i)
    (hi : Membership.mem (Geometry.simplexHull (omitted w i)) x) :
    Exists (fun j => And (Geometry.cofactor w j < 0)
      (Membership.mem (Geometry.simplexHull (omitted w j)) x)) := by
  cases omittedHull_weights w i x hi with
  | intro a ha =>
    have hothers := positive_weights_outside_pairHulls w a x ha.2.1 ha.1 i ha.2.2
      (fun j hji => hx i j (Ne.symm hji))
    cases Hypercube.FiberStep.exists_forward_boundary a (Geometry.cofactor w) i
        (Geometry.cofactor_sum_zero w) hci ha.2.2 hothers with
    | intro t ht =>
      cases ht with
      | intro j hj =>
        refine Exists.intro j (And.intro hj.2.1 ?_)
        exact omittedHull_of_zero_weight w
          (fun k => a k + t * Geometry.cofactor w k) x
          (affineRepresentation_add_cofactor w a x ha.2.1 t) hj.2.2.2.2 j hj.2.2.1

theorem opposite_omission_of_negative_cofactor {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x))
    (i : Fin (m + 2)) (hci : Geometry.cofactor w i < 0)
    (hi : Membership.mem (Geometry.simplexHull (omitted w i)) x) :
    Exists (fun j => And (0 < Geometry.cofactor w j)
      (Membership.mem (Geometry.simplexHull (omitted w j)) x)) := by
  cases omittedHull_weights w i x hi with
  | intro a ha =>
    have hothers := positive_weights_outside_pairHulls w a x ha.2.1 ha.1 i ha.2.2
      (fun j hji => hx i j (Ne.symm hji))
    have hsum : Finset.sum Finset.univ (fun k => -Geometry.cofactor w k) = 0 := by
      rw [Finset.sum_neg_distrib, Geometry.cofactor_sum_zero, neg_zero]
    have hcneg : 0 < -Geometry.cofactor w i := by linarith
    cases Hypercube.FiberStep.exists_forward_boundary a (fun k => -Geometry.cofactor w k) i
        hsum hcneg ha.2.2 hothers with
    | intro t ht =>
      cases ht with
      | intro j hj =>
        have hcj : 0 < Geometry.cofactor w j := by linarith [hj.2.1]
        refine Exists.intro j (And.intro hcj ?_)
        have hrepr : affineRepresentation w
            (fun k => a k + t * -Geometry.cofactor w k) x := by
          have hre := affineRepresentation_add_cofactor w a x ha.2.1 (-t)
          convert hre using 1
          funext k
          ring
        exact omittedHull_of_zero_weight w
          (fun k => a k + t * -Geometry.cofactor w k) x
          hrepr hj.2.2.2.2 j hj.2.2.1

theorem same_sign_omissions_unique {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x))
    (i j : Fin (m + 2))
    (hsign : Or (And (0 < Geometry.cofactor w i) (0 < Geometry.cofactor w j))
      (And (Geometry.cofactor w i < 0) (Geometry.cofactor w j < 0)))
    (hi : Membership.mem (Geometry.simplexHull (omitted w i)) x)
    (hj : Membership.mem (Geometry.simplexHull (omitted w j)) x) : i = j := by
  by_contra hij
  cases omittedHull_weights w i x hi with
  | intro a ha =>
    cases omittedHull_weights w j x hj with
    | intro b hb =>
      have hap := positive_weights_outside_pairHulls w a x ha.2.1 ha.1 i ha.2.2
        (fun k hki => hx i k (Ne.symm hki))
      have hbp := positive_weights_outside_pairHulls w b x hb.2.1 hb.1 j hb.2.2
        (fun k hkj => hx j k (Ne.symm hkj))
      have hci : Not (Geometry.cofactor w i = 0) := by
        cases hsign with
        | inl hp => linarith [hp.1]
        | inr hn => linarith [hn.1]
      cases (affineRepresentation_iff_cofactor_line w i hci a x ha.2.1 b).mp hb.2.1 with
      | intro t ht =>
        have hti : 0 < t * Geometry.cofactor w i := by
          have hbi := hbp i hij
          have heq := ht i
          rw [ha.2.2] at heq
          linarith
        have htj : t * Geometry.cofactor w j < 0 := by
          have haj := hap j (Ne.symm hij)
          have heq := ht j
          rw [hb.2.2] at heq
          linarith
        cases hsign with
        | inl hp =>
          have htp : 0 < t := (mul_pos_iff_of_pos_right hp.1).mp hti
          have hprod := mul_pos htp hp.2
          linarith
        | inr hn =>
          have htn : t < 0 := by
            cases mul_pos_iff.mp hti with
            | inl hpos => linarith [hpos.2, hn.1]
            | inr hneg => exact hneg.1
          have hprod := mul_pos_of_neg_of_neg htn hn.2
          linarith

theorem signedCocycleSum_of_opposite_omissions {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x))
    (i j : Fin (m + 2)) (hci : 0 < Geometry.cofactor w i)
    (hcj : Geometry.cofactor w j < 0)
    (hi : Membership.mem (Geometry.simplexHull (omitted w i)) x)
    (hj : Membership.mem (Geometry.simplexHull (omitted w j)) x) :
    signedCocycleSum w x = 0 := by
  classical
  have hij : Not (i = j) := by intro heq; rw [heq] at hci; linarith
  have htermzero : forall k, And (Not (k = i)) (Not (k = j)) ->
      (-1 : Real) ^ k.val * Geometry.signedSimplex (omitted w k) x = 0 := by
    intro k hk
    rw [signed_cocycle_term]
    by_cases hkh : Membership.mem (Geometry.simplexHull (omitted w k)) x
    next =>
      have hck : Geometry.cofactor w k = 0 := by
        by_contra hn
        cases lt_or_gt_of_ne hn with
        | inl hneg =>
          exact hk.2 (same_sign_omissions_unique w x hx k j
            (Or.inr (And.intro hneg hcj)) hkh hj)
        | inr hpos =>
          exact hk.1 (same_sign_omissions_unique w x hx k i
            (Or.inl (And.intro hpos hci)) hkh hi)
      simp only [Set.indicator_apply, ite_eq_left hkh, hck, orientation_zero]
    next => simp only [Set.indicator_apply, ite_eq_right hkh]
  have hsum := Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j)
    hij (fun k _ hk => htermzero k hk)
  unfold signedCocycleSum
  rw [hsum, signed_cocycle_term, signed_cocycle_term]
  simp only [Set.indicator_apply, ite_eq_left hi, ite_eq_left hj]
  unfold Geometry.orientation
  simp only [ite_eq_left hci, ite_eq_right (not_lt_of_ge (le_of_lt hcj)), ite_eq_left hcj]
  norm_num

/-- Outside the at-most-m-vertex faces, the two signed omission cells cancel. -/
theorem signedCocycleSum_outside_pairHulls {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) (x : Geometry.Point m)
    (hx : forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x)) :
    signedCocycleSum w x = 0 := by
  classical
  by_cases hactive : Exists (fun i => And
    (Membership.mem (Geometry.simplexHull (omitted w i)) x)
    (Not (Geometry.cofactor w i = 0)))
  next =>
    cases hactive with
    | intro i hi =>
      cases lt_or_gt_of_ne hi.2 with
      | inl hneg =>
        cases opposite_omission_of_negative_cofactor w x hx i hneg hi.1 with
        | intro j hj =>
          exact signedCocycleSum_of_opposite_omissions w x hx j i hj.1 hneg hj.2 hi.1
      | inr hpos =>
        cases opposite_omission_of_positive_cofactor w x hx i hpos hi.1 with
        | intro j hj =>
          exact signedCocycleSum_of_opposite_omissions w x hx i j hpos hj.1 hi.1 hj.2
  next =>
    unfold signedCocycleSum
    apply Finset.sum_eq_zero
    intro i _
    rw [signed_cocycle_term]
    by_cases hi : Membership.mem (Geometry.simplexHull (omitted w i)) x
    next =>
      have hci : Geometry.cofactor w i = 0 := by
        by_contra hn
        exact hactive (Exists.intro i (And.intro hi hn))
      simp only [Set.indicator_apply, ite_eq_left hi, hci, orientation_zero]
    next => simp only [Set.indicator_apply, ite_eq_right hi]

end Hypercube.Geometry.Cocycle
