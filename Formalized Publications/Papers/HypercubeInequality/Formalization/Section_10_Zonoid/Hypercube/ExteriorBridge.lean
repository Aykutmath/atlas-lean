import Section_10_Zonoid.Hypercube.Algebra.BinaryCocycle
import Section_10_Zonoid.Hypercube.Algebra.OrthogonalExterior
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
This file connects the paper's increasing exterior coordinates to Mathlib's
actual exterior algebra. The paper norm is explicitly the Euclidean norm of
these coordinates; no unprovided norm instance on the exterior algebra is used.
-/

noncomputable section

open Finset

namespace Hypercube.ExteriorBridge

variable {Index : Type*} [Fintype Index] [LinearOrder Index]

abbrev ExteriorSpace (Index : Type*) := ExteriorAlgebra Real (Index -> Real)

def exteriorBasis : Module.Basis (Finset Index) Real (ExteriorSpace Index) :=
  (Pi.basisFun Real Index).ExteriorAlgebra

def coordinates (x : ExteriorSpace Index) (S : Finset Index) : Real :=
  exteriorBasis.repr x S

def encode (B : Finset Index -> Real) : ExteriorSpace Index :=
  Finset.sum univ (fun S => HSMul.hSMul (B S) (exteriorBasis S))

def paperExteriorNorm (x : ExteriorSpace Index) : Real :=
  Real.sqrt (Finset.sum univ (fun S => coordinates x S ^ 2))

def paperVectorNorm (y : Index -> Real) : Real :=
  Real.sqrt (Finset.sum univ (fun i => y i ^ 2))

def oneVector (y : Index -> Real) : ExteriorSpace Index :=
  Finset.sum univ (fun i => HSMul.hSMul (y i) (exteriorBasis ({i} : Finset Index)))

theorem coordinates_encode (B : Finset Index -> Real) (S : Finset Index) :
    coordinates (encode B) S = B S := by
  simp [coordinates, encode, exteriorBasis, map_sum, Finsupp.single_apply]

theorem encode_coordinates (x : ExteriorSpace Index) :
    encode (coordinates x) = x := by
  unfold encode coordinates
  exact exteriorBasis.sum_repr x

theorem coordinates_basis (S T : Finset Index) :
    coordinates (exteriorBasis S) T = if S = T then 1 else 0 := by
  simp [coordinates, exteriorBasis, Finsupp.single_apply]

theorem norm_encode (B : Finset Index -> Real) :
    paperExteriorNorm (encode B) = Real.sqrt (BinaryCocycle.energy B) := by
  simp [paperExteriorNorm, coordinates_encode, BinaryCocycle.energy,
    BinaryCocycle.dot, pow_two]

theorem norm_squared (x : ExteriorSpace Index) :
    paperExteriorNorm x ^ 2 = Finset.sum univ (fun S => coordinates x S ^ 2) := by
  exact Real.sq_sqrt (Finset.sum_nonneg (fun S _ => sq_nonneg (coordinates x S)))

private def singletonSet (i : Index) : Set.powersetCard Index 1 :=
  Set.powersetCard.ofSingleton i

private def asCard (S : Finset Index) : Set.powersetCard Index S.card :=
  Set.powersetCard.ofCard rfl

omit [Fintype Index] [LinearOrder Index] in
private theorem singleton_disjoint (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) :
    Disjoint (singletonSet i).val (asCard S).val := by
  simpa [singletonSet, asCard, Set.powersetCard.ofSingleton,
    Set.powersetCard.ofCard] using Finset.disjoint_singleton_left.mpr hi

omit [Fintype Index] in
private theorem singleton_orderIso_value (i : Index) (a : Fin 1) :
    ((Set.powersetCard.orderIsoOfFin (singletonSet i)) a).val = i := by
  exact Finset.mem_singleton.mp ((Set.powersetCard.orderIsoOfFin (singletonSet i)) a).prop

set_option backward.isDefEq.respectTransparency false in
private theorem merge_zero_value (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) :
    ((Set.powersetCard.orderIsoOfFin
      (Set.powersetCard.disjUnion (singleton_disjoint i S hi)))
      (Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) 0)).val = i := by
  have hzero : finSumFinEquiv.symm (0 : Fin (1 + S.card)) = Sum.inl (0 : Fin 1) := by
    exact finSumFinEquiv_symm_apply_castAdd (n := S.card) (0 : Fin 1)
  simp +instances [Set.powersetCard.permOfDisjoint, Equiv.trans_apply, hzero,
    Set.powersetCard.disjUnion, Set.powersetCard.orderIsoOfFin]
  exact singleton_orderIso_value i 0

set_option backward.isDefEq.respectTransparency false in
private theorem merge_succ_value (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) (a : Fin S.card) :
    ((Set.powersetCard.orderIsoOfFin
      (Set.powersetCard.disjUnion (singleton_disjoint i S hi)))
      (Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi)
        (Fin.natAdd 1 a))).val = S.orderEmbOfFin rfl a := by
  simp only [Set.powersetCard.permOfDisjoint, Equiv.trans_apply]
  simp +instances [Set.powersetCard.disjUnion, Set.powersetCard.orderIsoOfFin]
  simp [asCard]

private theorem merge_lt (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) (a b : Fin (1 + S.card)) :
    Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) a <
      Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) b <->
    ((Set.powersetCard.orderIsoOfFin
        (Set.powersetCard.disjUnion (singleton_disjoint i S hi)))
        (Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) a)).val <
      ((Set.powersetCard.orderIsoOfFin
        (Set.powersetCard.disjUnion (singleton_disjoint i S hi)))
        (Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) b)).val := by
  exact (Set.powersetCard.orderIsoOfFin
    (Set.powersetCard.disjUnion (singleton_disjoint i S hi))).lt_iff_lt.symm

private theorem merge_zero_lt_succ (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) (a : Fin S.card) :
    Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) 0 <
      Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) (Fin.natAdd 1 a) <->
    i < S.orderEmbOfFin rfl a := by
  rw [merge_lt i S hi, merge_zero_value i S hi, merge_succ_value i S hi]

private theorem merge_succ_lt_succ (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) (a b : Fin S.card) :
    Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) (Fin.natAdd 1 a) <
      Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi) (Fin.natAdd 1 b) <->
    a < b := by
  rw [merge_lt i S hi, merge_succ_value i S hi, merge_succ_value i S hi]
  exact (S.orderEmbOfFin rfl).lt_iff_lt

private theorem positive_as_natAdd {n : Nat} (j : Fin (1 + n)) (hj : 0 < j) :
    exists a : Fin n, j = Fin.natAdd 1 a := by
  refine Exists.intro (Fin.mk (j.val - 1) (by have := j.isLt; have := hj; omega)) ?_
  apply Fin.ext
  simp only [Fin.val_natAdd]
  have := hj
  omega

private theorem singleton_merge_sign (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) :
    (((Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi)).sign : Int) : Real) =
      BinaryCocycle.sign i S := by
  let p := Set.powersetCard.permOfDisjoint (singleton_disjoint i S hi)
  have hp : (((p.sign : Int) : Real)) =
      Finset.prod univ (fun a => Finset.prod (Finset.Ioi a)
        (fun b => if p a < p b then (1 : Real) else -1)) := by
    have he := congrArg (fun z : Units Int => (z.val : Real)) p.sign_eq_prod_prod_Ioi
    rw [he]
    simp only [Units.coe_prod, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro a _
    apply Finset.prod_congr rfl
    intro b _
    by_cases hab : p a < p b <;> simp [hab]
  rw [hp]
  have hn (a : Fin (1 + S.card)) (ha : Not (a = 0)) :
      Finset.prod (Finset.Ioi a) (fun b => if p a < p b then (1 : Real) else -1) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    have hab : a < b := Finset.mem_Ioi.mp hb
    have hapos : 0 < a := Fin.pos_iff_ne_zero.mpr ha
    let a' := (positive_as_natAdd a hapos).choose
    have ha' := (positive_as_natAdd a hapos).choose_spec
    let b' := (positive_as_natAdd b (lt_trans hapos hab)).choose
    have hb' := (positive_as_natAdd b (lt_trans hapos hab)).choose_spec
    rw [ha', hb'] at hab
    rw [ha', hb']
    have hlt : a' < b' := by simpa only [Fin.natAdd_lt_natAdd_iff] using hab
    dsimp only [a', b'] at hlt
    simp only [p, merge_succ_lt_succ i S hi, ite_eq_left hlt]
  rw [Finset.prod_eq_single 0 (fun a _ ha => hn a ha) (by simp)]
  have hzero : Finset.prod (Finset.Ioi (0 : Fin (1 + S.card)))
      (fun b => if p 0 < p b then (1 : Real) else -1) =
      Finset.prod univ (fun a : Fin S.card =>
        if i < S.orderEmbOfFin rfl a then (1 : Real) else -1) := by
    symm
    apply Finset.prod_bij (fun a _ => Fin.natAdd 1 a)
    next =>
      intro a _
      simp only [Finset.mem_Ioi, Fin.lt_def, Fin.val_natAdd, Fin.val_zero]
      omega
    next =>
      intro a _ b _ hab
      exact Fin.natAdd_injective S.card 1 hab
    next =>
      intro b hb
      let a := (positive_as_natAdd b (Finset.mem_Ioi.mp hb)).choose
      have ha := (positive_as_natAdd b (Finset.mem_Ioi.mp hb)).choose_spec
      exact Exists.intro a (Exists.intro (Finset.mem_univ a) ha.symm)
    next =>
      intro a _
      simp only [p, merge_zero_lt_succ i S hi]
  rw [hzero]
  have hsign : Finset.prod univ (fun a : Fin S.card =>
      if i < S.orderEmbOfFin rfl a then (1 : Real) else -1) =
      Finset.prod S (fun j => if i < j then (1 : Real) else -1) := by
    apply Finset.prod_bij (fun a _ => S.orderEmbOfFin rfl a)
    next =>
      intro a _
      exact S.orderEmbOfFin_mem rfl a
    next =>
      intro a _ b _ hab
      exact (S.orderEmbOfFin rfl).injective hab
    next =>
      intro j hj
      have hmem : Membership.mem (Set.range (S.orderEmbOfFin rfl)) j := by
        simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hj
      exact Exists.intro hmem.choose (Exists.intro (Finset.mem_univ hmem.choose) hmem.choose_spec)
    next =>
      intro a _
      rfl
  rw [hsign]
  unfold BinaryCocycle.sign
  apply Finset.prod_congr rfl
  intro j hj
  have hij : Not (i = j) := by intro h; subst j; exact hi hj
  rcases lt_or_gt_of_ne hij with h | h
  next =>
    simp [h, not_lt_of_gt h]
  next =>
    simp [h, not_lt_of_gt h]

theorem singleton_basis_mul_of_mem (i : Index) (S : Finset Index)
    (hi : Membership.mem S i) :
    exteriorBasis ({i} : Finset Index) * exteriorBasis S = 0 := by
  have hn : Not (Disjoint (singletonSet i).val (asCard S).val) := by
    intro hd
    have hn : Not (Membership.mem S i) := by
      simpa [singletonSet, asCard, Set.powersetCard.ofSingleton,
        Set.powersetCard.ofCard] using hd
    exact hn hi
  exact ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun Real Index)
    (singletonSet i) (asCard S) hn

theorem singleton_basis_mul_of_not_mem (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) :
    exteriorBasis ({i} : Finset Index) * exteriorBasis S =
      HSMul.hSMul (BinaryCocycle.sign i S) (exteriorBasis (insert i S)) := by
  have he := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun Real Index)
    (singletonSet i) (asCard S) (singleton_disjoint i S hi)
  rw [Units.smul_def, <- Int.cast_smul_eq_zsmul Real, singleton_merge_sign i S hi] at he
  simpa [exteriorBasis, Set.powersetCard.disjUnion, singletonSet, asCard,
    Set.powersetCard.ofSingleton, Set.powersetCard.ofCard,
    Finset.disjUnion_eq_union] using he

theorem coordinates_smul (a : Real) (x : ExteriorSpace Index) (S : Finset Index) :
    coordinates (HSMul.hSMul a x) S = a * coordinates x S := by
  simp [coordinates]

theorem singleton_product_coordinates (i : Index) (S J : Finset Index) :
    coordinates (exteriorBasis ({i} : Finset Index) * exteriorBasis S) J =
      if Membership.mem S i then 0
      else if insert i S = J then BinaryCocycle.sign i S else 0 := by
  by_cases hi : Membership.mem S i
  next =>
    rw [singleton_basis_mul_of_mem i S hi]
    simp [coordinates, hi]
  next =>
    rw [singleton_basis_mul_of_not_mem i S hi, coordinates_smul, coordinates_basis]
    simp [hi]

theorem singleton_encode_coordinates (i : Index) (B : Finset Index -> Real)
    (J : Finset Index) :
    coordinates (exteriorBasis ({i} : Finset Index) * encode B) J =
      if Membership.mem J i then BinaryCocycle.sign i J * B (J.erase i) else 0 := by
  have hexpand : coordinates (exteriorBasis ({i} : Finset Index) * encode B) J =
      Finset.sum univ (fun S => B S *
        coordinates (exteriorBasis ({i} : Finset Index) * exteriorBasis S) J) := by
    simp [encode, Finset.mul_sum, coordinates, map_sum]
  rw [hexpand]
  by_cases hi : Membership.mem J i
  next =>
    rw [ite_eq_left hi, Finset.sum_eq_single (J.erase i)]
    next =>
      rw [singleton_product_coordinates]
      simp [Finset.insert_erase hi, BinaryCocycle.sign_erase_self]
      ring
    next =>
      intro S _ hS
      rw [singleton_product_coordinates]
      by_cases hm : Membership.mem S i
      next =>
        simp [hm]
      next =>
        have hne : Not (insert i S = J) := by
          intro he
          have := congrArg (fun K : Finset Index => K.erase i) he
          simp only [Finset.erase_insert hm] at this
          exact hS this
        simp [hm, hne]
    next =>
      simp
  next =>
    rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro S _
    rw [singleton_product_coordinates]
    by_cases hm : Membership.mem S i
    next =>
      simp [hm]
    next =>
      have hne : Not (insert i S = J) := by
        intro he
        apply hi
        rw [<- he]
        exact Finset.mem_insert_self i S
      simp [hm, hne]

/-- Literal exterior multiplication has precisely the paper's alternating
coefficient, with each deleted subset counted once and no factorial. -/
theorem oneVector_mul_coordinates (y : Index -> Real) (B : Finset Index -> Real)
    (J : Finset Index) :
    coordinates (oneVector y * encode B) J = BinaryCocycle.creation y B J := by
  have hexpand : coordinates (oneVector y * encode B) J =
      Finset.sum univ (fun i => y i *
        coordinates (exteriorBasis ({i} : Finset Index) * encode B) J) := by
    simp [oneVector, Finset.sum_mul, coordinates, map_sum]
  rw [hexpand]
  simp only [singleton_encode_coordinates]
  unfold BinaryCocycle.creation
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem oneVector_mul_encode (y : Index -> Real) (B : Finset Index -> Real) :
    oneVector y * encode B = encode (BinaryCocycle.creation y B) := by
  apply exteriorBasis.repr.injective
  apply Finsupp.ext
  intro J
  exact (oneVector_mul_coordinates y B J).trans (coordinates_encode _ _).symm

theorem creation_energy_grade (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0) :
    BinaryCocycle.energy (BinaryCocycle.creation y B) =
      Finset.sum (BinaryCocycle.grade (Index := Index) (k + 1))
        (fun J => BinaryCocycle.creation y B J ^ 2) := by
  unfold BinaryCocycle.energy BinaryCocycle.dot BinaryCocycle.grade
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : J.card = k + 1
  next =>
    simp [hJ, pow_two]
  next =>
    rw [BinaryCocycle.creation_degree k y B hdegree J hJ]
    simp [hJ]

/-- The source norm inequality on the actual exterior algebra, with constant one. -/
theorem exterior_mul_norm_le (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0) :
    paperExteriorNorm (oneVector y * encode B) <=
      paperVectorNorm y * paperExteriorNorm (encode B) := by
  rw [oneVector_mul_encode, norm_encode, creation_energy_grade k y B hdegree,
    norm_encode]
  exact BinaryCocycle.creation_norm_le k y B hdegree

/-- A subset basis element is the actual Mathlib exterior-power basis element,
embedded in the exterior algebra, with the same increasing orientation. -/
theorem exterior_basis_degree (S : Finset Index) :
    exteriorBasis S =
      ((Pi.basisFun Real Index).exteriorPower S.card (Set.powersetCard.ofCard rfl)).val := by
  exact ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun Real Index)
    (Set.powersetCard.ofCard (s := S) rfl)

theorem singleton_orientation (i : Index) (S : Finset Index)
    (hi : Not (Membership.mem S i)) :
    exteriorBasis ({i} : Finset Index) * exteriorBasis S =
      HSMul.hSMul ((-1 : Real) ^ (S.filter (fun j => j < i)).card)
        (exteriorBasis (insert i S)) := by
  rw [singleton_basis_mul_of_not_mem i S hi, BinaryCocycle.sign_rank]

omit [Fintype Index] [LinearOrder Index] in
theorem rootWeight_eq_sqrt (q : Index -> Real) (hq : forall i, 0 <= q i)
    (S : Finset Index) :
    BinaryCocycle.rootWeight q S = Real.sqrt (BinaryCocycle.weight q S) := by
  have hroot : 0 <= BinaryCocycle.rootWeight q S :=
    Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg (q i))
  rw [<- BinaryCocycle.rootWeight_sq q hq S, Real.sqrt_sq hroot]

/-- The manuscript's b, literally in the exterior algebra. -/
def paperExteriorB (q : Index -> Real) (h : Finset Index -> Real) (k : Nat) :
    ExteriorSpace Index :=
  encode (fun S => if S.card = k then Real.sqrt (BinaryCocycle.weight q S) * h S else 0)

theorem paperExteriorB_eq_weighted (q : Index -> Real) (hq : forall i, 0 <= q i)
    (h : Finset Index -> Real) (k : Nat) :
    paperExteriorB q h k = encode (BinaryCocycle.weightedCochain q h k) := by
  unfold paperExteriorB
  congr 1
  funext S
  simp only [BinaryCocycle.weightedCochain, rootWeight_eq_sqrt q hq S]

theorem paperExteriorB_eq_subset_sum (q : Index -> Real)
    (h : Finset Index -> Real) (k : Nat) :
    paperExteriorB q h k =
      Finset.sum (BinaryCocycle.grade (Index := Index) k) (fun S =>
        HSMul.hSMul (Real.sqrt (BinaryCocycle.weight q S) * h S) (exteriorBasis S)) := by
  unfold paperExteriorB encode BinaryCocycle.grade
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = k <;> simp [hS]

theorem paperExteriorB_coordinates (q : Index -> Real)
    (h : Finset Index -> Real) (k : Nat) (S : Finset Index) (hS : S.card = k) :
    coordinates (paperExteriorB q h k) S =
      Real.sqrt (BinaryCocycle.weight q S) * h S := by
  simp [paperExteriorB, coordinates_encode, hS]

/-- Source e wedge b = 0 on the actual exterior algebra. -/
theorem paper_cocycle_wedge_zero (q : Index -> Real) (hq : forall i, 0 <= q i)
    (h : Finset Index -> Real) (k : Nat)
    (hcycle : forall J, J.card = k + 1 ->
      BinaryCocycle.increasingAlternatingSum (fun _ => 1) h J = 0) :
    oneVector (fun i => Real.sqrt (q i)) * paperExteriorB q h k = 0 := by
  have hb : forall J, J.card = k + 1 -> BinaryCocycle.boundary (fun _ => 1) h J = 0 := by
    intro J hJ
    rw [BinaryCocycle.boundary_eq_alternatingSum,
      BinaryCocycle.alternatingSum_eq_increasingAlternatingSum]
    exact hcycle J hJ
  rw [paperExteriorB_eq_weighted q hq, oneVector_mul_encode,
    BinaryCocycle.weighted_cocycle_creation_zero q h k hb]
  simp [encode]

/-- The e_J coefficient is sqrt(q_J) s_J in the literal exterior product. -/
theorem paper_label_wedge_coefficient (q f : Index -> Real)
    (hq : forall i, 0 <= q i) (h : Finset Index -> Real)
    (k : Nat) (J : Finset Index) (hJ : J.card = k + 1) :
    coordinates (oneVector (fun i => Real.sqrt (q i) * f i) * paperExteriorB q h k) J =
      Real.sqrt (BinaryCocycle.weight q J) *
        BinaryCocycle.increasingAlternatingSum f h J := by
  rw [paperExteriorB_eq_weighted q hq, oneVector_mul_coordinates,
    BinaryCocycle.creation_weightedCochain q f h k J hJ,
    rootWeight_eq_sqrt q hq, BinaryCocycle.boundary_eq_alternatingSum,
    BinaryCocycle.alternatingSum_eq_increasingAlternatingSum]

theorem paperExteriorB_norm_squared (q : Index -> Real)
    (hq : forall i, 0 <= q i) (h : Finset Index -> Real) (k : Nat) :
    paperExteriorNorm (paperExteriorB q h k) ^ 2 =
      Finset.sum (BinaryCocycle.grade (Index := Index) k)
        (fun S => BinaryCocycle.weight q S * h S ^ 2) := by
  rw [paperExteriorB_eq_weighted q hq, norm_squared]
  simp only [coordinates_encode]
  simpa only [BinaryCocycle.energy, BinaryCocycle.dot, pow_two] using
    BinaryCocycle.weightedCochain_energy q hq h k

theorem paper_weighted_wedge_norm_le (q : Index -> Real)
    (hq : forall i, 0 <= q i) (h : Finset Index -> Real) (k : Nat)
    (y : Index -> Real) :
    paperExteriorNorm (oneVector y * paperExteriorB q h k) <=
      paperVectorNorm y * paperExteriorNorm (paperExteriorB q h k) := by
  rw [paperExteriorB_eq_weighted q hq]
  exact exterior_mul_norm_le k y _ (BinaryCocycle.weightedCochain_degree q h k)

omit [LinearOrder Index] in
theorem paper_centered_vector_norm_squared (q f : Index -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum univ (fun i => q i * f i)
    paperVectorNorm (fun i => Real.sqrt (q i) * (f i - p)) ^ 2 = p * (1 - p) := by
  dsimp only
  unfold paperVectorNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Hypercube.Algebra.square_root_weighted_binary_variance q f hq hqsum hbinary

omit [LinearOrder Index] in
theorem paper_reference_vector_norm_squared (q : Index -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum univ q = 1) :
    paperVectorNorm (fun i => Real.sqrt (q i)) ^ 2 = 1 := by
  unfold paperVectorNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simpa only [BinaryCocycle.energy, BinaryCocycle.dot, pow_two] using
    BinaryCocycle.weighted_reference_energy q hq hqsum

omit [LinearOrder Index] in
theorem paper_label_vector_norm_squared (q f : Index -> Real)
    (hq : forall i, 0 <= q i) (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    paperVectorNorm (fun i => Real.sqrt (q i) * f i) ^ 2 =
      Finset.sum univ (fun i => q i * f i) := by
  unfold paperVectorNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simpa only [BinaryCocycle.energy, BinaryCocycle.dot, pow_two] using
    BinaryCocycle.weighted_label_energy q f hq hbinary

/-- This linear inclusion sends each source coordinate basis vector to the
actual degree-one exterior basis vector, which characterizes the inclusion. -/
def vectorInclusion : LinearMap (RingHom.id Real) (Index -> Real) (ExteriorSpace Index) where
  toFun := oneVector
  map_add' y z := by simp [oneVector, add_smul, Finset.sum_add_distrib]
  map_smul' a y := by simp [oneVector, smul_smul, Finset.smul_sum, Pi.smul_apply]

theorem vectorInclusion_basis (i : Index) :
    vectorInclusion ((Pi.basisFun Real Index) i) = exteriorBasis ({i} : Finset Index) := by
  change oneVector ((Pi.basisFun Real Index) i) = _
  simp [oneVector, Pi.basisFun_apply, Pi.single_apply]

theorem vectorInclusion_unique
    (L : LinearMap (RingHom.id Real) (Index -> Real) (ExteriorSpace Index))
    (hL : forall i, L ((Pi.basisFun Real Index) i) = exteriorBasis ({i} : Finset Index)) :
    L = vectorInclusion := by
  apply (Pi.basisFun Real Index).ext
  intro i
  rw [hL, vectorInclusion_basis]

theorem norm_coe_exteriorPower (k : Nat)
    (x : OrthogonalExterior.Degree (Index -> Real) k) :
    paperExteriorNorm x.val = OrthogonalExterior.powerNorm k x := by
  exact OrthogonalExterior.fullNorm_coe_power k x

/-- Source wedge estimate for an arbitrary actual homogeneous exterior element. -/
theorem exteriorPower_mul_norm_le (k : Nat) (y : Index -> Real)
    (x : OrthogonalExterior.Degree (Index -> Real) k) :
    paperExteriorNorm (oneVector y * x.val) <=
      paperVectorNorm y * paperExteriorNorm x.val := by
  have hdegree : forall S, Not (S.card = k) -> coordinates x.val S = 0 := by
    intro S hS
    exact OrthogonalExterior.fullCoordinate_coe_of_wrong_card k x S hS
  have he := exterior_mul_norm_le k y (coordinates x.val) hdegree
  rw [encode_coordinates] at he
  exact he

/-- Orthogonal change of source coordinates preserves the actual induced
exterior norm; the proof uses the determinant-Gram form. -/
theorem orthogonal_exterior_norm (U : Module.End Real (Index -> Real))
    (hU : forall x y, Finset.sum univ (fun i => U x i * U y i) =
      Finset.sum univ (fun i => x i * y i))
    (k : Nat) (x : OrthogonalExterior.Degree (Index -> Real) k) :
    paperExteriorNorm (ExteriorAlgebra.map U x.val) = paperExteriorNorm x.val := by
  exact OrthogonalExterior.orthogonal_full_exterior_norm_of_degree U hU k x

end Hypercube.ExteriorBridge
