import Section_10_Zonoid.Hypercube.Geometry
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.Block

/- Full-dimensional volume normalization development. All sets below use
ordinary coordinate Lebesgue measure. This file does not define volume by
determinants. Cube chambers are used to derive the factorial normalization. -/

noncomputable section

namespace Hypercube.Geometry

open MeasureTheory

def unitCube (m : Nat) : Set (Point m) := Set.Icc 0 1

def orderChamber (m : Nat) (p : Equiv.Perm (Fin m)) : Set (Point m) :=
  Set.ofPred (fun x => And (x ∈ unitCube m) (Monotone (fun i => x (p i))))

def coordinatePermutation {m : Nat} (p : Equiv.Perm (Fin m)) :
    MeasurableEquiv (Point m) (Point m) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin m => Real) p.symm

theorem coordinatePermutation_apply {m : Nat} (p : Equiv.Perm (Fin m))
    (x : Point m) (i : Fin m) : coordinatePermutation p x i = x (p i) := by
  have h := @MeasurableEquiv.piCongrLeft_apply_apply (Fin m) (Fin m)
    p.symm (fun _ => Real) _ x (p i)
  simpa [coordinatePermutation] using h

theorem unitCube_reindex {m : Nat} (p : Equiv.Perm (Fin m)) (x : Point m) :
    (coordinatePermutation p x) ∈ unitCube m <-> x ∈ unitCube m := by
  change And (forall i, 0 <= coordinatePermutation p x i)
      (forall i, coordinatePermutation p x i <= 1) <->
    And (forall i, 0 <= x i) (forall i, x i <= 1)
  simp_rw [coordinatePermutation_apply]
  constructor
  next =>
    intro h
    constructor
    next => intro i; simpa using h.1 (p.symm i)
    next => intro i; simpa using h.2 (p.symm i)
  next =>
    intro h
    exact And.intro (fun i => h.1 (p i)) (fun i => h.2 (p i))

theorem orderChamber_eq_preimage {m : Nat} (p : Equiv.Perm (Fin m)) :
    orderChamber m p = Set.preimage (coordinatePermutation p)
      (orderChamber m (Equiv.refl (Fin m))) := by
  ext x
  change And (x ∈ unitCube m) (Monotone (fun i => x (p i))) <->
    And ((coordinatePermutation p x) ∈ unitCube m)
      (Monotone (fun i => coordinatePermutation p x i))
  rw [unitCube_reindex]
  simp_rw [coordinatePermutation_apply]

theorem orderChamber_measurable (m : Nat) (p : Equiv.Perm (Fin m)) :
    MeasurableSet (orderChamber m p) := by
  have hcont : Continuous (fun x : Point m => fun i => x (p i)) := by
    exact continuous_pi (fun i => continuous_apply (p i))
  exact measurableSet_Icc.inter (isClosed_monotone.preimage hcont).measurableSet

theorem orderChamber_equal_volume (m : Nat) (p : Equiv.Perm (Fin m)) :
    volume (orderChamber m p) = volume (orderChamber m (Equiv.refl (Fin m))) := by
  rw [orderChamber_eq_preimage]
  have hp := volume_measurePreserving_piCongrLeft
    (fun _ : Fin m => Real) p.symm
  exact hp.measure_preimage (orderChamber_measurable m _).nullMeasurableSet

theorem orderChamber_union (m : Nat) :
    Set.iUnion (orderChamber m) = unitCube m := by
  ext x
  constructor
  next =>
    intro hx
    obtain h : Exists (fun p => x ∈ orderChamber m p) := Set.mem_iUnion.mp hx
    obtain hp := h.choose_spec
    exact hp.1
  next =>
    intro hx
    apply Set.mem_iUnion.mpr
    exact Exists.intro (Tuple.sort x) (And.intro hx (Tuple.monotone_sort x))

theorem coordinate_tie_volume_zero {m : Nat} {i j : Fin m} (hij : Not (i = j)) :
    volume (Set.ofPred (fun x : Point m => x i = x j)) = 0 := by
  let P : Fin m -> LinearMap (RingHom.id Real) (Point m) Real :=
    fun k => LinearMap.proj k
  let L := P i - P j
  have hker : Not (L.ker = (Top.top : Submodule Real (Point m))) := by
    intro h
    have hz := LinearMap.ker_eq_top.mp h
    have hv := LinearMap.congr_fun hz (Pi.single i (1 : Real))
    simp [L, P, Ne.symm hij] at hv
  have hset : Set.ofPred (fun x : Point m => x i = x j) =
      (L.ker : Set (Point m)) := by
    ext x
    simp [L, P, LinearMap.mem_ker, sub_eq_zero]
  rw [hset]
  exact Measure.addHaar_submodule volume _ hker

theorem orderChamber_pairwise_aedisjoint (m : Nat) :
    Pairwise (fun p q => AEDisjoint volume (orderChamber m p) (orderChamber m q)) := by
  intro p q hpq
  have hne : Not (forall i, p i = q i) := fun h => hpq (Equiv.ext h)
  obtain h : Exists (fun i => Not (p i = q i)) := not_forall.mp hne
  obtain hi := h.choose_spec
  unfold AEDisjoint
  apply measure_mono_null _ (coordinate_tie_volume_zero hi)
  intro x hx
  have heq := Tuple.unique_monotone hx.1.2 hx.2.2
  exact congrFun heq h.choose

theorem unitCube_volume (m : Nat) : volume (unitCube m) = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

theorem orderChamber_volume_factorial (m : Nat) :
    (m.factorial : Real) *
      (volume (orderChamber m (Equiv.refl (Fin m)))).toReal = 1 := by
  have hd := orderChamber_pairwise_aedisjoint m
  have hm : forall p, NullMeasurableSet (orderChamber m p) volume :=
    fun p => (orderChamber_measurable m p).nullMeasurableSet
  have hsum : volume (Set.iUnion (orderChamber m)) =
      tsum (fun p => volume (orderChamber m p)) := by
    exact?
  rw [orderChamber_union, unitCube_volume] at hsum
  simp_rw [orderChamber_equal_volume] at hsum
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin] at hsum
  have hr := congrArg ENNReal.toReal hsum
  simpa [nsmul_eq_mul, ENNReal.toReal_mul] using hr.symm

def chamberVertex (m : Nat) (r : Fin (m + 1)) : Point m :=
  fun i => if r.val <= i.val then 1 else 0

def extendedCoordinate {m : Nat} (x : Point m) (r : Fin (m + 2)) : Real :=
  if r.val = 0 then 0 else
    if h : r.val - 1 < m then x (Fin.mk (r.val - 1) h) else 1

theorem extendedCoordinate_zero {m : Nat} (x : Point m) :
    extendedCoordinate x 0 = 0 := by simp [extendedCoordinate]

theorem extendedCoordinate_last {m : Nat} (x : Point m) :
    extendedCoordinate x (Fin.last (m + 1)) = 1 := by
  simp [extendedCoordinate]

theorem extendedCoordinate_middle {m : Nat} (x : Point m) (i : Fin m) :
    extendedCoordinate x i.castSucc.succ = x i := by
  simp [extendedCoordinate, i.isLt]

theorem extendedCoordinate_monotone {m : Nat} (x : Point m)
    (hx : x ∈ orderChamber m (Equiv.refl (Fin m))) : Monotone (extendedCoordinate x) := by
  have hlow : forall i, 0 <= x i := hx.1.1
  have hupp : forall i, x i <= 1 := hx.1.2
  have hmono : Monotone x := hx.2
  intro a b hab
  have hv : a.val <= b.val := hab
  unfold extendedCoordinate
  split_ifs
  all_goals try norm_num
  all_goals first
    | exact hlow _
    | exact hupp _
    | (apply hmono; change a.val - 1 <= b.val - 1; omega)
    | omega

def chamberWeight {m : Nat} (x : Point m) (r : Fin (m + 1)) : Real :=
  extendedCoordinate x r.succ - extendedCoordinate x r.castSucc

theorem chamberWeight_nonneg {m : Nat} (x : Point m)
    (hx : x ∈ orderChamber m (Equiv.refl (Fin m))) (r : Fin (m + 1)) :
    0 <= chamberWeight x r := by
  exact sub_nonneg.mpr ((extendedCoordinate_monotone x hx) r.castSucc_le_succ)

theorem chamberWeight_sum {m : Nat} (x : Point m) :
    Finset.sum Finset.univ (chamberWeight x) = 1 := by
  have h := Fin.sum_Iic_sub (Fin.last m) (extendedCoordinate x)
  have hIic : Finset.Iic (Fin.last m) = Finset.univ := by
    ext r
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact r.le_last
  rw [hIic, show (Fin.last m).succ = Fin.last (m + 1) from rfl,
    extendedCoordinate_last, extendedCoordinate_zero, sub_zero] at h
  exact h

theorem chamberWeight_coordinate {m : Nat} (x : Point m) (i : Fin m) :
    Finset.sum Finset.univ (fun r => chamberWeight x r * chamberVertex m r i) = x i := by
  have h := Fin.sum_Iic_sub i.castSucc (extendedCoordinate x)
  have heq : Finset.sum Finset.univ
      (fun r => chamberWeight x r * chamberVertex m r i) =
      Finset.sum (Finset.Iic i.castSucc) (chamberWeight x) := by
    rw [<- Finset.sum_ite_mem_eq (Finset.Iic i.castSucc) (chamberWeight x)]
    apply Finset.sum_congr rfl
    intro r _
    simp [chamberVertex, Finset.mem_Iic, Fin.le_def]
  rw [heq]
  rw [extendedCoordinate_middle, extendedCoordinate_zero, sub_zero] at h
  exact h

theorem orderChamber_subset_vertex_hull (m : Nat) :
    Set.Subset (orderChamber m (Equiv.refl (Fin m))) (simplexHull (chamberVertex m)) := by
  intro x hx
  have hmem := affineCombination_mem_convexHull
    (v := chamberVertex m) (s := Finset.univ) (w := chamberWeight x)
    (fun r _ => chamberWeight_nonneg x hx r) (chamberWeight_sum x)
  have heq : Finset.affineCombination Real Finset.univ (chamberVertex m) (chamberWeight x) = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ (chamberWeight_sum x)]
    funext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using chamberWeight_coordinate x i
  rw [heq] at hmem
  exact hmem

theorem orderChamber_convex (m : Nat) :
    Convex Real (orderChamber m (Equiv.refl (Fin m))) := by
  intro x hx y hy a b ha hb hab
  change And
    (And (forall i, 0 <= a * x i + b * y i)
      (forall i, a * x i + b * y i <= 1))
    (Monotone (fun i => a * x i + b * y i))
  constructor
  next =>
    constructor
    next =>
      intro i
      exact add_nonneg (mul_nonneg ha (hx.1.1 i)) (mul_nonneg hb (hy.1.1 i))
    next =>
      intro i
      have h1 := mul_le_mul_of_nonneg_left (hx.1.2 i) ha
      have h2 := mul_le_mul_of_nonneg_left (hy.1.2 i) hb
      calc
        a * x i + b * y i <= a + b := by
          simpa only [Pi.one_apply, mul_one] using add_le_add h1 h2
        _ = 1 := hab
  next =>
    intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.2 hij) hb)

theorem chamberVertex_mem_orderChamber (m : Nat) (r : Fin (m + 1)) :
    (chamberVertex m r) ∈ orderChamber m (Equiv.refl (Fin m)) := by
  constructor
  next =>
    constructor
    next => intro i; unfold chamberVertex; split_ifs; all_goals norm_num
    next => intro i; unfold chamberVertex; split_ifs; all_goals norm_num
  next =>
    intro i j hij
    change (if r.val <= i.val then (1 : Real) else 0) <=
      (if r.val <= j.val then (1 : Real) else 0)
    have hv : i.val <= j.val := hij
    split_ifs
    all_goals try norm_num
    all_goals omega

theorem orderChamber_eq_vertex_hull (m : Nat) :
    orderChamber m (Equiv.refl (Fin m)) = simplexHull (chamberVertex m) := by
  apply Set.Subset.antisymm (orderChamber_subset_vertex_hull m)
  apply convexHull_min _ (orderChamber_convex m)
  intro x hx
  have h : Exists (fun r => chamberVertex m r = x) := hx
  rw [<- h.choose_spec]
  exact chamberVertex_mem_orderChamber m h.choose

/-- The full-dimensional reference simplex has the exact factorial volume. -/
theorem chamber_simplex_volume_factorial (m : Nat) :
    (m.factorial : Real) * simplexVolume (chamberVertex m) = 1 := by
  unfold simplexVolume
  rw [<- orderChamber_eq_vertex_hull]
  exact orderChamber_volume_factorial m

def chamberMatrix (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun i j => if i <= j then 1 else 0

theorem chamberMatrix_det (m : Nat) : (chamberMatrix m).det = 1 := by
  have htri : (chamberMatrix m).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [chamberMatrix, not_le.mpr hij]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [chamberMatrix]

theorem chamberVertex_affine_minor (m : Nat) :
    (affineMatrix (chamberVertex m)).submatrix
      (Fin.last m).succAbove (Fin.last m).succAbove = chamberMatrix m := by
  funext i j
  simp only [affineMatrix, Matrix.submatrix, Fin.succAbove_last,
    Fin.lastCases_castSucc, chamberVertex, Fin.val_castSucc, chamberMatrix]
  congr 1

theorem chamberVertex_affineDet (m : Nat) : affineDet (chamberVertex m) = 1 := by
  unfold affineDet
  rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
  have hzero : Finset.sum Finset.univ
      (fun j : Fin m => (-1 : Real) ^ ((Fin.last m).val + j.castSucc.val) *
        affineMatrix (chamberVertex m) (Fin.last m) j.castSucc *
        ((affineMatrix (chamberVertex m)).submatrix
          (Fin.last m).succAbove j.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : Not (m <= j.val) := not_le.mpr j.isLt
    simp [affineMatrix, chamberVertex, hj]
  rw [hzero, zero_add, chamberVertex_affine_minor, chamberMatrix_det]
  simp only [affineMatrix, Fin.lastCases_last, Fin.val_last, mul_one]
  rw [show m + m = 2 * m from by omega, pow_mul]
  norm_num

/-- The consecutive vertex differences send the reference simplex to the given one. -/
def edgeMatrix {m : Nat} (w : Fin (m + 1) -> Point m) :
    Matrix (Fin m) (Fin m) Real :=
  fun i j => w j.castSucc i - w j.succ i

theorem edgeMatrix_reference_image {m : Nat} (w : Fin (m + 1) -> Point m)
    (r : Fin (m + 1)) :
    (Matrix.toLin' (edgeMatrix w)) (chamberVertex m r) + w (Fin.last m) = w r := by
  cases m with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      refine Fin.lastCases ?_ (fun r => ?_) r
      next =>
        funext i
        change Finset.sum Finset.univ
          (fun j : Fin (n + 1) => edgeMatrix w i j * chamberVertex (n + 1) (Fin.last (n + 1)) j)
            + w (Fin.last (n + 1)) i = w (Fin.last (n + 1)) i
        have hzero : Finset.sum Finset.univ
            (fun j : Fin (n + 1) => edgeMatrix w i j * chamberVertex (n + 1) (Fin.last (n + 1)) j) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hj : Not (n + 1 <= j.val) := not_le.mpr j.isLt
          simp [chamberVertex, hj]
        rw [hzero, zero_add]
      next r =>
        funext i
        change Finset.sum Finset.univ
          (fun j : Fin (n + 1) => edgeMatrix w i j * chamberVertex (n + 1) r.castSucc j)
            + w (Fin.last (n + 1)) i = w r.castSucc i
        have htel := Fin.sum_Icc_sub (Fin.le_last r)
          (fun j : Fin (n + 2) => - w j i)
        have hsum : Finset.sum Finset.univ
            (fun j : Fin (n + 1) => edgeMatrix w i j * chamberVertex (n + 1) r.castSucc j) =
            Finset.sum (Finset.Icc r (Fin.last n))
              (fun j => - w j.succ i - - w j.castSucc i) := by
          rw [<- Finset.sum_ite_mem_eq (Finset.Icc r (Fin.last n))]
          apply Finset.sum_congr rfl
          intro j _
          have hjlast : j.val <= (Fin.last n).val := by
            exact Fin.le_last j
          simp only [edgeMatrix, chamberVertex, Fin.val_castSucc,
            Finset.mem_Icc, Fin.le_def, hjlast, and_true]
          split_ifs <;> ring
        rw [hsum, htel]
        change -w (Fin.last (n + 1)) i - -w r.castSucc i + w (Fin.last (n + 1)) i = w r.castSucc i
        ring

end Hypercube.Geometry
