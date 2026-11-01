import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Section_10_Zonoid.Hypercube.Geometry.Cocycle
import Section_10_Zonoid.Hypercube.Geometry.NullFaces
import Section_10_Zonoid.Hypercube.Geometry.AffineRankBridge
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered

/-!
The literal finite-dimensional rank and interval claims in the paper's
barycentric-fiber argument. The matrix has columns (w_i,1), as in the source.
-/

noncomputable section

namespace Hypercube.Geometry.FiberStructure

def augmentedColumnMatrix {m : Nat} (w : Fin (m + 2) -> Point m) :
    Matrix (Fin (m + 1)) (Fin (m + 2)) Real :=
  fun j i => Fin.lastCases 1 (w i) j

theorem augmented_matrix_rank {m : Nat} (w : Fin (m + 2) -> Point m)
    (p : Fin (m + 2)) (hp : Not (cofactor w p = 0)) :
    (augmentedColumnMatrix w).rank = m + 1 := by
  have hd : Not (affineDet (fun j => w (p.succAbove j)) = 0) := by
    intro h
    apply hp
    unfold cofactor
    rw [h, mul_zero]
  have hminor : (augmentedColumnMatrix w).submatrix id p.succAbove =
      (affineMatrix (fun j => w (p.succAbove j))).transpose := by
    funext i j
    rfl
  have hdet : Not (((augmentedColumnMatrix w).submatrix id p.succAbove).det = 0) := by
    rw [hminor, Matrix.det_transpose]
    exact hd
  have hu : IsUnit ((augmentedColumnMatrix w).submatrix id p.succAbove) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrank := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at hrank
  have hlo := Matrix.rank_submatrix_le (augmentedColumnMatrix w) id p.succAbove
  rw [hrank] at hlo
  have hhi := Matrix.rank_le_card_height (augmentedColumnMatrix w)
  simp only [Fintype.card_fin] at hhi
  exact le_antisymm hhi hlo

def feasibleParameters {Index : Type*} (a c : Index -> Real) : Set Real :=
  Set.ofPred (fun t => forall i, 0 <= a i + t * c i)

theorem feasibleParameters_closed {Index : Type*} (a c : Index -> Real) :
    IsClosed (feasibleParameters a c) := by
  have hset : feasibleParameters a c =
      Set.iInter (fun i => Set.ofPred (fun t : Real => 0 <= a i + t * c i)) := by
    ext t
    simp [feasibleParameters]
  rw [hset]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const))

theorem feasibleParameters_convex {Index : Type*} (a c : Index -> Real) :
    Convex Real (feasibleParameters a c) := by
  intro t ht s hs alpha beta halpha hbeta hsum i
  change 0 <= a i + (alpha * t + beta * s) * c i
  have heq : alpha * (a i + t * c i) + beta * (a i + s * c i) =
      a i + (alpha * t + beta * s) * c i := by
    calc
      _ = (alpha + beta) * a i + (alpha * t + beta * s) * c i := by ring
      _ = _ := by rw [hsum, one_mul]
  rw [<- heq]
  exact add_nonneg (mul_nonneg halpha (ht i)) (mul_nonneg hbeta (hs i))

theorem zero_sum_nonzero_has_both_signs {Index : Type*} [Fintype Index]
    (c : Index -> Real) (hsum : Finset.sum Finset.univ c = 0)
    (p : Index) (hp : Not (c p = 0)) :
    And (Exists (fun i => 0 < c i)) (Exists (fun j => c j < 0)) := by
  classical
  constructor
  next =>
    by_contra h
    have hc : forall i, 0 <= -c i := by
      intro i
      have hi : c i <= 0 := le_of_not_gt (fun hi => h (Exists.intro i hi))
      linarith
    have hn : Finset.sum Finset.univ (fun i => -c i) = 0 := by
      rw [Finset.sum_neg_distrib, hsum, neg_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hn
    have hzp := hz p (Finset.mem_univ p)
    apply hp
    linarith
  next =>
    by_contra h
    have hc : forall i, 0 <= c i := by
      intro i
      exact le_of_not_gt (fun hi => h (Exists.intro i hi))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hsum
    exact hp (hz p (Finset.mem_univ p))

theorem feasibleParameters_compact {Index : Type*} [Fintype Index]
    (a c : Index -> Real) (hsum : Finset.sum Finset.univ c = 0)
    (p : Index) (hp : Not (c p = 0)) :
    IsCompact (feasibleParameters a c) := by
  cases zero_sum_nonzero_has_both_signs c hsum p hp with
  | intro hpos hneg =>
    cases hpos with
    | intro i hi =>
      cases hneg with
      | intro j hj =>
        let lo := -a i / c i
        let upper := a j / (-c j)
        have hlo : lo * c i = -a i := by
          dsimp only [lo]
          field_simp [ne_of_gt hi]
        have hupper : upper * (-c j) = a j := by
          dsimp only [upper]
          field_simp [ne_of_lt hj]
        have hbound : feasibleParameters a c <= Set.Icc lo upper := by
          intro t ht
          constructor
          next =>
            apply le_of_mul_le_mul_right (a := c i) _ hi
            rw [hlo]
            linarith [ht i]
          next =>
            apply le_of_mul_le_mul_right (a := -c j) _ (show 0 < -c j by linarith)
            rw [hupper]
            linarith [ht j]
        exact isCompact_Icc.of_isClosed_subset (feasibleParameters_closed a c) hbound

/-- Every feasible fiber is empty or a closed interval, allowing coincident endpoints. -/
theorem feasibleParameters_empty_or_interval {Index : Type*} [Fintype Index]
    (a c : Index -> Real) (hsum : Finset.sum Finset.univ c = 0)
    (p : Index) (hp : Not (c p = 0)) :
    Or (feasibleParameters a c = EmptyCollection.emptyCollection)
      (Exists (fun lo : Real => Exists (fun upper : Real =>
        And (lo <= upper) (feasibleParameters a c = Set.Icc lo upper)))) := by
  by_cases hne : (feasibleParameters a c).Nonempty
  next =>
    have hconn : IsConnected (feasibleParameters a c) :=
      And.intro hne (feasibleParameters_convex a c).isPreconnected
    have heq := eq_Icc_of_connected_compact hconn (feasibleParameters_compact a c hsum p hp)
    apply Or.inr
    refine Exists.intro (sInf (feasibleParameters a c))
      (Exists.intro (sSup (feasibleParameters a c)) (And.intro ?_ heq))
    cases hne with
    | intro t ht =>
      rw [heq] at ht
      exact ht.1.trans ht.2
  next => exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

def strictlyFeasibleParameters {Index : Type*} (a c : Index -> Real) : Set Real :=
  Set.ofPred (fun t => forall i, 0 < a i + t * c i)

theorem strictlyFeasibleParameters_open {Index : Type*} [Fintype Index]
    (a c : Index -> Real) : IsOpen (strictlyFeasibleParameters a c) := by
  have hset : strictlyFeasibleParameters a c =
      Set.iInter (fun i => Set.ofPred (fun t : Real => 0 < a i + t * c i)) := by
    ext t
    simp [strictlyFeasibleParameters]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const))

theorem feasible_noninterior_has_zero {Index : Type*} [Fintype Index]
    (a c : Index -> Real) (t : Real) (ht : Membership.mem (feasibleParameters a c) t)
    (hn : Not (Membership.mem (interior (feasibleParameters a c)) t)) :
    Exists (fun i => a i + t * c i = 0) := by
  by_contra h
  have hpositive : Membership.mem (strictlyFeasibleParameters a c) t := by
    intro i
    have hi : Not (a i + t * c i = 0) := fun hi => h (Exists.intro i hi)
    exact lt_of_le_of_ne (ht i) (Ne.symm hi)
  have hsub : strictlyFeasibleParameters a c <= feasibleParameters a c := by
    intro s hs i
    exact le_of_lt (hs i)
  exact hn (interior_maximal hsub (strictlyFeasibleParameters_open a c) hpositive)

theorem interval_endpoints_have_zero {Index : Type*} [Fintype Index]
    (a c : Index -> Real) (lo upper : Real) (horder : lo <= upper)
    (heq : feasibleParameters a c = Set.Icc lo upper) :
    And (Exists (fun i => a i + lo * c i = 0))
      (Exists (fun j => a j + upper * c j = 0)) := by
  constructor
  next =>
    apply feasible_noninterior_has_zero a c lo
    next => rw [heq]; exact And.intro (le_refl lo) horder
    next => simp [heq, interior_Icc]
  next =>
    apply feasible_noninterior_has_zero a c upper
    next => rw [heq]; exact And.intro horder (le_refl upper)
    next => simp [heq, interior_Icc]

def nonnegativeFiber {m : Nat} (w : Fin (m + 2) -> Point m) (x : Point m) :
    Set (Fin (m + 2) -> Real) :=
  Set.ofPred (fun a => And (forall i, 0 <= a i) (Cocycle.affineRepresentation w a x))

/-- Explicit bridge from the source's barycentric representations to the parameter interval. -/
theorem nonnegativeFiber_eq_image {m : Nat} (w : Fin (m + 2) -> Point m)
    (x : Point m) (p : Fin (m + 2)) (hp : Not (cofactor w p = 0))
    (a0 : Fin (m + 2) -> Real) (ha0 : Cocycle.affineRepresentation w a0 x) :
    nonnegativeFiber w x = (fun t i => a0 i + t * cofactor w i) ''
      feasibleParameters a0 (cofactor w) := by
  ext a
  constructor
  next =>
    intro ha
    cases (Cocycle.affineRepresentation_iff_cofactor_line w p hp a0 x ha0 a).mp ha.2 with
    | intro t ht =>
      have heq : (fun i => a0 i + t * cofactor w i) = a := (funext ht).symm
      refine Exists.intro t (And.intro ?_ heq)
      intro i
      rw [<- ht i]
      exact ha.1 i
  next =>
    intro ha
    cases ha with
    | intro t ht =>
      cases ht with
      | intro hnonneg heq =>
        subst a
        exact And.intro hnonneg (Cocycle.affineRepresentation_add_cofactor w a0 x ha0 t)

theorem nonnegativeFiber_compact {m : Nat} (w : Fin (m + 2) -> Point m)
    (x : Point m) (p : Fin (m + 2)) (hp : Not (cofactor w p = 0))
    (a0 : Fin (m + 2) -> Real) (ha0 : Cocycle.affineRepresentation w a0 x) :
    IsCompact (nonnegativeFiber w x) := by
  rw [nonnegativeFiber_eq_image w x p hp a0 ha0]
  apply (feasibleParameters_compact a0 (cofactor w) (cofactor_sum_zero w) p hp).image
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_id.mul continuous_const)

theorem cofactor_zero_of_not_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m)
    (hspan : Not (affineSpan Real (Set.range w) = Top.top)) :
    forall i, cofactor w i = 0 := by
  intro i
  have hsub : simplexHull (fun j => w (i.succAbove j)) <=
      (affineSpan Real (Set.range w) : Set (Point m)) := by
    apply Set.Subset.trans _ (convexHull_subset_affineSpan (Set.range w))
    apply convexHull_mono
    intro x hx
    cases hx with
    | intro j hj => exact Exists.intro (i.succAbove j) hj
  have hv : MeasureTheory.volume (simplexHull (fun j => w (i.succAbove j))) = 0 :=
    MeasureTheory.measure_mono_null hsub
      (MeasureTheory.Measure.addHaar_affineSubspace MeasureTheory.volume _ hspan)
  have hdet := simplex_volume_factorial (fun j => w (i.succAbove j))
  unfold simplexVolume at hdet
  rw [hv, ENNReal.toReal_zero, mul_zero] at hdet
  have hz := abs_eq_zero.mp hdet.symm
  unfold cofactor
  rw [hz, mul_zero]

theorem affineSpan_full_of_cofactor_nonzero {m : Nat}
    (w : Fin (m + 2) -> Point m) (p : Fin (m + 2))
    (hp : Not (cofactor w p = 0)) : affineSpan Real (Set.range w) = Top.top := by
  by_contra h
  exact hp (cofactor_zero_of_not_affineSpan_full w h p)

theorem generic_interval_endpoints {m : Nat} (w : Fin (m + 2) -> Point m)
    (x : Point m) (a : Fin (m + 2) -> Real)
    (ha : Cocycle.affineRepresentation w a x)
    (hxpair : forall i j, Not (i = j) -> Not (Membership.mem (Cocycle.pairHull w i j) x))
    (hxdeg : forall i, cofactor w i = 0 ->
      Not (Membership.mem (simplexHull (Cocycle.omitted w i)) x))
    (lo upper : Real) (horder : lo <= upper)
    (heq : feasibleParameters a (cofactor w) = Set.Icc lo upper) :
    Exists (fun i => Exists (fun j =>
      And (lo < upper) (And (0 < cofactor w i) (And (cofactor w j < 0)
        (And (a i + lo * cofactor w i = 0)
          (And (a j + upper * cofactor w j = 0)
            (And (forall k, Not (k = i) -> 0 < a k + lo * cofactor w k)
              (forall k, Not (k = j) -> 0 < a k + upper * cofactor w k)))))))) := by
  classical
  have hlo : forall k, 0 <= a k + lo * cofactor w k := by
    have hmem : Membership.mem (feasibleParameters a (cofactor w)) lo := by
      rw [heq]
      exact And.intro (le_refl lo) horder
    exact hmem
  have hupper : forall k, 0 <= a k + upper * cofactor w k := by
    have hmem : Membership.mem (feasibleParameters a (cofactor w)) upper := by
      rw [heq]
      exact And.intro horder (le_refl upper)
    exact hmem
  cases interval_endpoints_have_zero a (cofactor w) lo upper horder heq with
  | intro hlozero hupperzero =>
    cases hlozero with
    | intro i hli =>
      cases hupperzero with
      | intro j huj =>
        have hreprlo := Cocycle.affineRepresentation_add_cofactor w a x ha lo
        have hreprupper := Cocycle.affineRepresentation_add_cofactor w a x ha upper
        have hinsidei := Cocycle.omittedHull_of_zero_weight w _ x hreprlo hlo i hli
        have hinsidej := Cocycle.omittedHull_of_zero_weight w _ x hreprupper hupper j huj
        have hci : Not (cofactor w i = 0) := fun h => hxdeg i h hinsidei
        have hcj : Not (cofactor w j = 0) := fun h => hxdeg j h hinsidej
        have hotherslo := Cocycle.positive_weights_outside_pairHulls w _ x hreprlo hlo i hli
          (fun k hki => hxpair i k (Ne.symm hki))
        have hothersupper := Cocycle.positive_weights_outside_pairHulls w _ x hreprupper hupper j huj
          (fun k hkj => hxpair j k (Ne.symm hkj))
        have hcipos : 0 < cofactor w i := by
          cases lt_or_gt_of_ne hci with
          | inl hneg =>
            have hsumneg : Finset.sum Finset.univ (fun k => -cofactor w k) = 0 := by
              rw [Finset.sum_neg_distrib, cofactor_sum_zero, neg_zero]
            cases FiberStep.exists_forward_boundary (fun k => a k + lo * cofactor w k)
                (fun k => -cofactor w k) i hsumneg (by linarith) hli hotherslo with
            | intro t ht =>
              cases ht with
              | intro k hk =>
                have hnew : Membership.mem (feasibleParameters a (cofactor w)) (lo - t) := by
                  intro l
                  have hl := hk.2.2.2.2 l
                  have hlin : a l + (lo - t) * cofactor w l =
                      (a l + lo * cofactor w l) + t * -cofactor w l := by ring
                  rw [hlin]
                  exact hl
                rw [heq] at hnew
                linarith [hk.1, hnew.1]
          | inr hpos => exact hpos
        have hcjneg : cofactor w j < 0 := by
          cases lt_or_gt_of_ne hcj with
          | inl hneg => exact hneg
          | inr hpos =>
            cases FiberStep.exists_forward_boundary (fun k => a k + upper * cofactor w k)
                (cofactor w) j (cofactor_sum_zero w) hpos huj hothersupper with
            | intro t ht =>
              cases ht with
              | intro k hk =>
                have hnew : Membership.mem (feasibleParameters a (cofactor w)) (upper + t) := by
                  intro l
                  have hl := hk.2.2.2.2 l
                  have hlin : a l + (upper + t) * cofactor w l =
                      (a l + upper * cofactor w l) + t * cofactor w l := by ring
                  rw [hlin]
                  exact hl
                rw [heq] at hnew
                linarith [hk.1, hnew.2]
        have hlength : lo < upper := by
          cases FiberStep.exists_forward_boundary (fun k => a k + lo * cofactor w k)
              (cofactor w) i (cofactor_sum_zero w) hcipos hli hotherslo with
          | intro t ht =>
            cases ht with
            | intro k hk =>
              have hnew : Membership.mem (feasibleParameters a (cofactor w)) (lo + t) := by
                intro l
                have hl := hk.2.2.2.2 l
                have hlin : a l + (lo + t) * cofactor w l =
                    (a l + lo * cofactor w l) + t * cofactor w l := by ring
                rw [hlin]
                exact hl
              rw [heq] at hnew
              linarith [hk.1, hnew.2]
        exact Exists.intro i (Exists.intro j
          (And.intro hlength (And.intro hcipos (And.intro hcjneg
            (And.intro hli (And.intro huj (And.intro hotherslo hothersupper)))))))

def fiberLine {Index : Type*} (a c : Index -> Real) :
    AffineMap Real Real (Index -> Real) where
  toFun t := fun i => a i + t * c i
  linear := (LinearMap.id : LinearMap (RingHom.id Real) Real Real).smulRight c
  map_vadd' t s := by
    funext i
    change a i + (s + t) * c i = s * c i + (a i + t * c i)
    ring

/-- Actual coefficient fibers are empty, a singleton, or a genuine closed segment. -/
theorem nonnegativeFiber_empty_point_or_segment {m : Nat}
    (w : Fin (m + 2) -> Point m) (x : Point m) (p : Fin (m + 2))
    (hp : Not (cofactor w p = 0)) (a0 : Fin (m + 2) -> Real)
    (ha0 : Cocycle.affineRepresentation w a0 x) :
    Or (nonnegativeFiber w x = EmptyCollection.emptyCollection)
      (Or (Exists (fun b => nonnegativeFiber w x = Set.singleton b))
        (Exists (fun b => Exists (fun d =>
          And (Not (b = d)) (nonnegativeFiber w x = segment Real b d))))) := by
  cases feasibleParameters_empty_or_interval a0 (cofactor w) (cofactor_sum_zero w) p hp with
  | inl he =>
      apply Or.inl
      rw [nonnegativeFiber_eq_image w x p hp a0 ha0, he, Set.image_empty]
  | inr hi =>
      cases hi with
      | intro lo hlo =>
        cases hlo with
        | intro upper hupper =>
          have hf : nonnegativeFiber w x =
              segment Real (fiberLine a0 (cofactor w) lo) (fiberLine a0 (cofactor w) upper) := by
            rw [nonnegativeFiber_eq_image w x p hp a0 ha0, hupper.2,
              <- segment_eq_Icc hupper.1]
            exact image_segment Real (fiberLine a0 (cofactor w)) lo upper
          by_cases he : lo = upper
          next =>
            apply Or.inr
            apply Or.inl
            refine Exists.intro (fiberLine a0 (cofactor w) upper) ?_
            rw [hf, he, segment_same]
            rfl
          next =>
            apply Or.inr
            apply Or.inr
            refine Exists.intro (fiberLine a0 (cofactor w) lo)
              (Exists.intro (fiberLine a0 (cofactor w) upper) (And.intro ?_ hf))
            intro hends
            have hcoord := congrFun hends p
            change a0 p + lo * cofactor w p = a0 p + upper * cofactor w p at hcoord
            have hmul : (lo - upper) * cofactor w p = 0 := by nlinarith
            have hdiff := (mul_eq_zero.mp hmul).resolve_right hp
            exact he (sub_eq_zero.mp hdiff)

theorem small_hull_volume_zero {m : Nat} (w : Fin (m + 2) -> Point m)
    (s : Finset (Fin (m + 2))) (hs : s.card <= m) :
    MeasureTheory.volume (convexHull Real (w '' (s : Set (Fin (m + 2))))) = 0 := by
  have hcard : (s : Set (Fin (m + 2))).encard <= Module.finrank Real (Point m) := by
    simp only [Set.encard_coe_eq_coe_finsetCard, Module.finrank_pi, Fintype.card_fin]
    exact_mod_cast hs
  have hproper := affineSpan_image_ne_top_of_encard_le_finrank Real s.finite_toSet hcard w
  exact MeasureTheory.measure_mono_null (convexHull_subset_affineSpan _)
    (MeasureTheory.Measure.addHaar_affineSubspace MeasureTheory.volume _ hproper)

theorem degenerate_omission_volume_zero {m : Nat} (w : Fin (m + 2) -> Point m)
    (i : Fin (m + 2)) (hi : cofactor w i = 0) :
    MeasureTheory.volume (simplexHull (Cocycle.omitted w i)) = 0 := by
  have hp : Not (((-1 : Real) ^ i.val) = 0) := pow_ne_zero _ (by norm_num)
  have hdet : affineDet (Cocycle.omitted w i) = 0 := by
    unfold cofactor at hi
    exact (mul_eq_zero.mp hi).resolve_left hp
  exact simplexHull_volume_zero_of_affineDet_zero _ hdet

theorem ae_avoids_source_exceptional_sets {m : Nat} (w : Fin (m + 2) -> Point m) :
    Filter.Eventually (fun x =>
      And (forall s : Finset (Fin (m + 2)), s.card <= m ->
        Not (Membership.mem (convexHull Real (w '' (s : Set (Fin (m + 2))))) x))
        (forall i, cofactor w i = 0 ->
          Not (Membership.mem (simplexHull (Cocycle.omitted w i)) x)))
      (MeasureTheory.ae MeasureTheory.volume) := by
  have hsmall : Filter.Eventually (fun x =>
      forall s : Finset (Fin (m + 2)), s.card <= m ->
        Not (Membership.mem (convexHull Real (w '' (s : Set (Fin (m + 2))))) x))
      (MeasureTheory.ae MeasureTheory.volume) := by
    apply MeasureTheory.ae_all_iff.mpr
    intro s
    by_cases hs : s.card <= m
    next =>
      exact (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (small_hull_volume_zero w s hs)).mono
        (fun _ hx _ => hx)
    next => exact Filter.Eventually.of_forall (fun _ h => False.elim (hs h))
  have hdeg : Filter.Eventually (fun x =>
      forall i, cofactor w i = 0 ->
        Not (Membership.mem (simplexHull (Cocycle.omitted w i)) x))
      (MeasureTheory.ae MeasureTheory.volume) := by
    apply MeasureTheory.ae_all_iff.mpr
    intro i
    by_cases hi : cofactor w i = 0
    next =>
      exact (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (degenerate_omission_volume_zero w i hi)).mono
        (fun _ hx _ => hx)
    next => exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  exact hsmall.and hdeg

theorem source_exceptional_sets_avoid_pairs {m : Nat}
    (w : Fin (m + 2) -> Point m) (x : Point m)
    (hx : forall s : Finset (Fin (m + 2)), s.card <= m ->
      Not (Membership.mem (convexHull Real (w '' (s : Set (Fin (m + 2))))) x)) :
    forall i j, Not (i = j) -> Not (Membership.mem (Cocycle.pairHull w i j) x) := by
  intro i j hij
  classical
  let s : Finset (Fin (m + 2)) := (Finset.univ.erase i).erase j
  have hji : Not (j = i) := Ne.symm hij
  have hjmem : Membership.mem (Finset.univ.erase i : Finset (Fin (m + 2))) j := by
    simp [hji]
  have hcard : s.card = m := by
    dsimp only [s]
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hset : (s : Set (Fin (m + 2))) =
      Set.ofPred (fun k => And (Not (k = i)) (Not (k = j))) := by
    ext k
    simp only [s, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
      Set.mem_ofPred]
    exact and_comm
  unfold Cocycle.pairHull
  rw [<- hset]
  exact hx s (by rw [hcard])

def annihilatorAffine {m : Nat} (v : Fin (m + 1) -> Real) :
    AffineMap Real (Point m) Real where
  toFun x := Finset.sum Finset.univ (fun j : Fin m => v j.castSucc * x j) + v (Fin.last m)
  linear := Finset.sum Finset.univ
    (fun j : Fin m => HSMul.hSMul (v j.castSucc)
      (LinearMap.proj j : LinearMap (RingHom.id Real) (Point m) Real))
  map_vadd' x y := by
    simp only [vadd_eq_add, Pi.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    change Finset.sum Finset.univ (fun j => v j.castSucc * (y j + x j)) + v (Fin.last m) =
      Finset.sum Finset.univ (fun j => v j.castSucc * y j) +
        (Finset.sum Finset.univ (fun j => v j.castSucc * x j) + v (Fin.last m))
    simp only [mul_add, Finset.sum_add_distrib, add_assoc]

theorem augmented_matrix_rank_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top) :
    (augmentedColumnMatrix w).rank = m + 1 := by
  have hz : forall v : Fin (m + 1) -> Real,
      Matrix.mulVec (augmentedColumnMatrix w).transpose v = 0 -> v = 0 := by
    intro v hv
    have hagree : (Set.range w).EqOn (annihilatorAffine v) (AffineMap.const Real (Point m) 0) := by
      intro x hx
      cases hx with
      | intro i hi =>
        rw [<- hi]
        have h := congrFun hv i
        change Finset.sum Finset.univ (fun j => Fin.lastCases 1 (w i) j * v j) = 0 at h
        rw [Fin.sum_univ_castSucc] at h
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_mul] at h
        change Finset.sum Finset.univ (fun j : Fin m => v j.castSucc * w i j) + v (Fin.last m) = 0
        convert h using 1
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
    have hmaps := AffineMap.ext_on hspan hagree
    have hlast : v (Fin.last m) = 0 := by
      have h := congrArg (fun f : AffineMap Real (Point m) Real => f 0) hmaps
      simpa [annihilatorAffine, AffineMap.const_apply] using h
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    next => exact hlast
    next j =>
      have h := congrArg (fun f : AffineMap Real (Point m) Real => f (Pi.single j 1)) hmaps
      simpa [annihilatorAffine, AffineMap.const_apply, hlast, Pi.single_apply] using h
  have hinj : Function.Injective (Matrix.mulVecLin (augmentedColumnMatrix w).transpose) := by
    apply LinearMap.ker_eq_bot.mp
    exact LinearMap.ker_eq_bot'.mpr hz
  have hrank : (augmentedColumnMatrix w).transpose.rank = m + 1 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]
  rw [Matrix.rank_transpose] at hrank
  exact hrank

theorem endpoint_omissions_exact {m : Nat} (w : Fin (m + 2) -> Point m)
    (x : Point m) (a : Fin (m + 2) -> Real)
    (ha : Cocycle.affineRepresentation w a x)
    (hxpair : forall i j, Not (i = j) -> Not (Membership.mem (Cocycle.pairHull w i j) x))
    (hxdeg : forall i, cofactor w i = 0 ->
      Not (Membership.mem (simplexHull (Cocycle.omitted w i)) x))
    (lo upper : Real) (horder : lo <= upper)
    (heq : feasibleParameters a (cofactor w) = Set.Icc lo upper) :
    Exists (fun i => Exists (fun j =>
      And (lo < upper) (And (0 < cofactor w i) (And (cofactor w j < 0)
        (And (a i + lo * cofactor w i = 0)
          (And (a j + upper * cofactor w j = 0)
            (And (forall k, Not (k = i) -> 0 < a k + lo * cofactor w k)
              (And (forall k, Not (k = j) -> 0 < a k + upper * cofactor w k)
                (forall k, Membership.mem (simplexHull (Cocycle.omitted w k)) x <->
                  Or (k = i) (k = j)))))))))) := by
  obtain hi := generic_interval_endpoints w x a ha hxpair hxdeg lo upper horder heq
  let i := hi.choose
  let j := hi.choose_spec.choose
  have hend := hi.choose_spec.choose_spec
  have hlength := hend.1
  have hcipos := hend.2.1
  have hcjneg := hend.2.2.1
  have hli := hend.2.2.2.1
  have huj := hend.2.2.2.2.1
  have hloothers := hend.2.2.2.2.2.1
  have hupperothers := hend.2.2.2.2.2.2
  have hlo : forall k, 0 <= a k + lo * cofactor w k := by
    have hm : Membership.mem (feasibleParameters a (cofactor w)) lo := by
      rw [heq]
      exact And.intro (le_refl lo) horder
    exact hm
  have hupper : forall k, 0 <= a k + upper * cofactor w k := by
    have hm : Membership.mem (feasibleParameters a (cofactor w)) upper := by
      rw [heq]
      exact And.intro horder (le_refl upper)
    exact hm
  have hinsidei := Cocycle.omittedHull_of_zero_weight w _ x
    (Cocycle.affineRepresentation_add_cofactor w a x ha lo) hlo i hli
  have hinsidej := Cocycle.omittedHull_of_zero_weight w _ x
    (Cocycle.affineRepresentation_add_cofactor w a x ha upper) hupper j huj
  refine Exists.intro i (Exists.intro j
    (And.intro hlength (And.intro hcipos (And.intro hcjneg (And.intro hli
      (And.intro huj (And.intro hloothers (And.intro hupperothers ?_))))))))
  intro k
  constructor
  next =>
    intro hinside
    have hck : Not (cofactor w k = 0) := fun h => hxdeg k h hinside
    cases lt_or_gt_of_ne hck with
    | inl hneg =>
        exact Or.inr (Cocycle.same_sign_omissions_unique w x hxpair k j
          (Or.inr (And.intro hneg hcjneg)) hinside hinsidej)
    | inr hpos =>
        exact Or.inl (Cocycle.same_sign_omissions_unique w x hxpair k i
          (Or.inl (And.intro hpos hcipos)) hinside hinsidei)
  next =>
    intro he
    cases he with
    | inl h => simpa only [h] using hinsidei
    | inr h => simpa only [h] using hinsidej

theorem affineRepresentation_exists_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top)
    (x : Point m) : Exists (fun a => Cocycle.affineRepresentation w a x) := by
  have hrank := augmented_matrix_rank_of_affineSpan_full w hspan
  have hrange : (Matrix.mulVecLin (augmentedColumnMatrix w)).range = Top.top := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] using hrank
  have hsurj := LinearMap.range_eq_top.mp hrange
  cases hsurj (Fin.lastCases 1 x) with
  | intro a ha =>
      refine Exists.intro a (And.intro ?_ ?_)
      next =>
        have h := congrFun ha (Fin.last m)
        simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, augmentedColumnMatrix,
          Fin.lastCases_last, one_mul] using h
      next =>
        intro j
        have h := congrFun ha j.castSucc
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, augmentedColumnMatrix,
          Fin.lastCases_castSucc] at h
        convert h using 1
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _

theorem exists_cofactor_nonzero_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top) :
    Exists (fun p => Not (cofactor w p = 0)) := by
  have hminor := AffineRankBridge.exists_omission_det_ne_zero (augmentedColumnMatrix w)
    (augmented_matrix_rank_of_affineSpan_full w hspan)
  cases hminor with
  | intro p hp =>
      have hm : (augmentedColumnMatrix w).submatrix id p.succAbove =
          (affineMatrix (fun j => w (p.succAbove j))).transpose := by
        funext i j
        rfl
      rw [hm, Matrix.det_transpose] at hp
      refine Exists.intro p ?_
      unfold cofactor
      exact mul_ne_zero (pow_ne_zero p.val (by norm_num)) hp

theorem affineSpan_full_iff_exists_cofactor_nonzero {m : Nat}
    (w : Fin (m + 2) -> Point m) :
    affineSpan Real (Set.range w) = Top.top <-> Exists (fun p => Not (cofactor w p = 0)) := by
  constructor
  next => exact exists_cofactor_nonzero_of_affineSpan_full w
  next =>
    intro h
    cases h with
    | intro p hp => exact affineSpan_full_of_cofactor_nonzero w p hp

theorem affineKernel_eq_span_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top)
    (v : Fin (m + 2) -> Real) :
    Cocycle.affineKernel w v <-> Exists (fun t => forall i, v i = t * cofactor w i) := by
  constructor
  next =>
    intro hv
    cases exists_cofactor_nonzero_of_affineSpan_full w hspan with
    | intro p hp =>
        exact Exists.intro (v p / cofactor w p)
          (Cocycle.affineKernel_eq_scalar_cofactor w p hp v hv)
  next =>
    intro ht
    cases ht with
    | intro t ht =>
        unfold Cocycle.affineKernel
        constructor
        case left =>
          simp_rw [ht]
          rw [<- Finset.mul_sum, cofactor_sum_zero, mul_zero]
        case right =>
          intro j
          simp_rw [ht, mul_assoc]
          rw [<- Finset.mul_sum, cofactor_affine_relation, mul_zero]

theorem nonnegativeFiber_classification_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top)
    (x : Point m) :
    Or (nonnegativeFiber w x = EmptyCollection.emptyCollection)
      (Or (Exists (fun b => nonnegativeFiber w x = Set.singleton b))
        (Exists (fun b => Exists (fun d =>
          And (Not (b = d)) (nonnegativeFiber w x = segment Real b d))))) := by
  cases exists_cofactor_nonzero_of_affineSpan_full w hspan with
  | intro p hp =>
      cases affineRepresentation_exists_of_affineSpan_full w hspan x with
      | intro a ha =>
          exact nonnegativeFiber_empty_point_or_segment w x p hp a ha

theorem affineRepresentations_line_of_affineSpan_full {m : Nat}
    (w : Fin (m + 2) -> Point m) (hspan : affineSpan Real (Set.range w) = Top.top)
    (x : Point m) : Exists (fun a0 =>
      And (Cocycle.affineRepresentation w a0 x)
        (forall a, Cocycle.affineRepresentation w a x <->
          Exists (fun t => forall i, a i = a0 i + t * cofactor w i))) := by
  cases exists_cofactor_nonzero_of_affineSpan_full w hspan with
  | intro p hp =>
      cases affineRepresentation_exists_of_affineSpan_full w hspan x with
      | intro a0 ha0 =>
          refine Exists.intro a0 (And.intro ha0 ?_)
          intro a
          exact Cocycle.affineRepresentation_iff_cofactor_line w p hp a0 x ha0 a

end Hypercube.Geometry.FiberStructure
