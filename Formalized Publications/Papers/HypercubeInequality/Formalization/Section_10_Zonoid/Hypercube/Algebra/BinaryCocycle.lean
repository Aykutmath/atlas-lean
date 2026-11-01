import Section_10_Zonoid.Hypercube.Algebra.Basic
import Section_10_Zonoid.Hypercube.Algebra.Signs

/-
Source: hypercube_readable.tex, Weighted binary cocycle inequality.
The auxiliary space consists of every finite subset of the label set, with
the ordinary sum-of-squares norm. Signed toggles prove the exterior creation
estimate with constant one; the final theorem restricts to one degree.
-/

noncomputable section

namespace Hypercube.BinaryCocycle

open Finset

def dot {State : Type*} [Fintype State] (B C : State -> Real) : Real :=
  Finset.sum univ (fun S => B S * C S)

def energy {State : Type*} [Fintype State] (B : State -> Real) : Real :=
  dot B B

theorem dot_comm {State : Type*} [Fintype State] (B C : State -> Real) :
    dot B C = dot C B := by
  simp only [dot, mul_comm]

theorem dot_neg_right {State : Type*} [Fintype State] (B C : State -> Real) :
    dot B (fun S => - C S) = - dot B C := by
  simp [dot]

theorem dot_weighted_sum_left {Index State : Type*} [Fintype Index] [Fintype State]
    (y : Index -> Real) (B : Index -> State -> Real) (C : State -> Real) :
    dot (fun S => Finset.sum univ (fun i => y i * B i S)) C =
      Finset.sum univ (fun i => y i * dot (B i) C) := by
  simp only [dot, sum_mul]
  rw [sum_comm]
  simp only [mul_assoc, mul_sum]

theorem dot_weighted_sum_right {Index State : Type*} [Fintype Index] [Fintype State]
    (y : Index -> Real) (B : Index -> State -> Real) (C : State -> Real) :
    dot C (fun S => Finset.sum univ (fun i => y i * B i S)) =
      Finset.sum univ (fun i => y i * dot C (B i)) := by
  rw [dot_comm, dot_weighted_sum_left]
  simp only [dot_comm]

/-- The standard CAR calculation, stated with every operator premise visible. -/
theorem clifford_energy_identity {Index State : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype State]
    (G : Index -> (State -> Real) -> State -> Real)
    (hsymmetric : forall i B C, dot (G i B) C = dot B (G i C))
    (hinvolution : forall i B, G i (G i B) = B)
    (hanticommute : forall i j, Not (i = j) -> forall B,
      G i (G j B) = fun S => - G j (G i B) S)
    (y : Index -> Real) (B : State -> Real) :
    energy (fun S => Finset.sum univ (fun i => y i * G i B S)) =
      (Finset.sum univ (fun i => y i ^ 2)) * energy B := by
  have horth (i j : Index) :
      dot (G i B) (G j B) = if i = j then energy B else 0 := by
    by_cases hij : i = j
    next =>
      subst j
      rw [ite_eq_left rfl, hsymmetric, hinvolution]
      rfl
    next =>
      rw [ite_eq_right hij]
      have heq : dot (G i B) (G j B) = - dot (G i B) (G j B) := by
        calc
          dot (G i B) (G j B) = dot B (G i (G j B)) := hsymmetric _ _ _
          _ = - dot B (G j (G i B)) := by
            rw [hanticommute i j hij B, dot_neg_right]
          _ = - dot (G j B) (G i B) := by rw [hsymmetric]
          _ = - dot (G i B) (G j B) := by rw [dot_comm]
      linarith
  unfold energy
  rw [dot_weighted_sum_left]
  simp_rw [dot_weighted_sum_right, horth]
  simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
  simp only [energy, pow_two, <- mul_assoc, <- sum_mul]

section SubsetCoordinates

variable {Index : Type*} [Fintype Index] [LinearOrder Index]

def gamma (i : Index) (B : Finset Index -> Real) (S : Finset Index) : Real :=
  sign i S * B (toggle i S)

theorem gamma_symmetric (i : Index) (B C : Finset Index -> Real) :
    dot (gamma i B) C = dot B (gamma i C) := by
  unfold dot gamma
  calc
    Finset.sum univ (fun S => sign i S * B (toggle i S) * C S) =
        Finset.sum univ (fun S => sign i (toggle i S) *
          B (toggle i (toggle i S)) * C (toggle i S)) := by
      exact ((toggleEquiv i).sum_comp
        (fun S => sign i S * B (toggle i S) * C S)).symm
    _ = Finset.sum univ (fun S => B S * (sign i S * C (toggle i S))) := by
      apply sum_congr rfl
      intro S _
      rw [sign_toggle, ite_eq_right (lt_irrefl i), mul_one, toggle_self]
      ring

omit [Fintype Index] in
theorem gamma_involution (i : Index) (B : Finset Index -> Real) :
    gamma i (gamma i B) = B := by
  funext S
  unfold gamma
  rw [sign_toggle, ite_eq_right (lt_irrefl i), mul_one, toggle_self]
  rw [<- mul_assoc, <- pow_two, sign_sq, one_mul]

omit [Fintype Index] in
theorem gamma_anticommute (i j : Index) (hij : Not (i = j))
    (B : Finset Index -> Real) :
    gamma i (gamma j B) = fun S => - gamma j (gamma i B) S := by
  funext S
  unfold gamma
  rw [sign_toggle, sign_toggle, toggle_comm]
  rcases lt_or_gt_of_ne hij with h | h
  next =>
    rw [ite_eq_left h, ite_eq_right (not_lt_of_ge (le_of_lt h))]
    ring
  next =>
    rw [ite_eq_left h, ite_eq_right (not_lt_of_ge (le_of_lt h))]
    ring

theorem gamma_energy_identity (y : Index -> Real) (B : Finset Index -> Real) :
    energy (fun S => Finset.sum univ (fun i => y i * gamma i B S)) =
      (Finset.sum univ (fun i => y i ^ 2)) * energy B :=
  clifford_energy_identity gamma gamma_symmetric gamma_involution
    gamma_anticommute y B

def grade (k : Nat) : Finset (Finset Index) :=
  univ.filter (fun S => S.card = k)

def creation (y : Index -> Real) (B : Finset Index -> Real)
    (J : Finset Index) : Real :=
  Finset.sum J (fun i => sign i J * y i * B (J.erase i))

theorem creation_eq_gamma (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0)
    (J : Finset Index) (hJ : J.card = k + 1) :
    creation y B J = Finset.sum univ (fun i => y i * gamma i B J) := by
  unfold creation gamma
  calc
    Finset.sum J (fun i => sign i J * y i * B (J.erase i)) =
        Finset.sum J (fun i => y i * (sign i J * B (toggle i J))) := by
      apply sum_congr rfl
      intro i hi
      rw [toggle, ite_eq_left hi]
      ring
    _ = Finset.sum univ (fun i => y i * (sign i J * B (toggle i J))) := by
      apply sum_subset (subset_univ J)
      intro i _ hi
      rw [toggle, ite_eq_right hi]
      have hcard : Not ((insert i J).card = k) := by
        rw [card_insert_of_notMem hi, hJ]
        omega
      rw [hdegree _ hcard]
      ring

omit [Fintype Index] in
theorem creation_degree (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0)
    (J : Finset Index) (hJ : Not (J.card = k + 1)) :
    creation y B J = 0 := by
  unfold creation
  apply sum_eq_zero
  intro i hi
  have hcard : Not ((J.erase i).card = k) := by
    intro he
    exact hJ (by simpa [he] using (card_erase_add_one hi).symm)
  rw [hdegree _ hcard]
  ring

/-- Sum-of-squares creation estimate with constant exactly one. -/
theorem creation_energy_le (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0) :
    Finset.sum (grade (Index := Index) (k + 1)) (fun J => creation y B J ^ 2) <=
      (Finset.sum univ (fun i => y i ^ 2)) * energy B := by
  calc
    Finset.sum (grade (Index := Index) (k + 1)) (fun J => creation y B J ^ 2) =
        Finset.sum (grade (Index := Index) (k + 1))
          (fun J => (Finset.sum univ (fun i => y i * gamma i B J)) ^ 2) := by
      apply sum_congr rfl
      intro J hJ
      rw [creation_eq_gamma k y B hdegree J (mem_filter.mp hJ).2]
    _ <= Finset.sum univ (fun J => (Finset.sum univ (fun i => y i * gamma i B J)) ^ 2) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro J _ _
      exact sq_nonneg _
    _ = (Finset.sum univ (fun i => y i ^ 2)) * energy B := by
      simpa [energy, dot, pow_two] using gamma_energy_identity y B

/-- The manuscript's exterior norm estimate in its orthonormal subset coordinates. -/
theorem creation_norm_le (k : Nat) (y : Index -> Real)
    (B : Finset Index -> Real)
    (hdegree : forall S, Not (S.card = k) -> B S = 0) :
    Real.sqrt (Finset.sum (grade (Index := Index) (k + 1))
        (fun J => creation y B J ^ 2)) <=
      Real.sqrt (Finset.sum univ (fun i => y i ^ 2)) * Real.sqrt (energy B) := by
  calc
    Real.sqrt (Finset.sum (grade (Index := Index) (k + 1))
        (fun J => creation y B J ^ 2)) <=
        Real.sqrt ((Finset.sum univ (fun i => y i ^ 2)) * energy B) :=
      Real.sqrt_le_sqrt (creation_energy_le k y B hdegree)
    _ = Real.sqrt (Finset.sum univ (fun i => y i ^ 2)) * Real.sqrt (energy B) :=
      Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (y i))) _

def weight (q : Index -> Real) (S : Finset Index) : Real := Finset.prod S q

def rootWeight (q : Index -> Real) (S : Finset Index) : Real :=
  Finset.prod S (fun i => Real.sqrt (q i))

omit [Fintype Index] [LinearOrder Index] in
theorem rootWeight_sq (q : Index -> Real) (hq : forall i, 0 <= q i)
    (S : Finset Index) : rootWeight q S ^ 2 = weight q S :=
  Hypercube.Algebra.square_root_product_square q hq S

def weightedCochain (q : Index -> Real) (h : Finset Index -> Real)
    (k : Nat) (S : Finset Index) : Real :=
  if S.card = k then rootWeight q S * h S else 0

def boundary (f : Index -> Real) (h : Finset Index -> Real)
    (J : Finset Index) : Real :=
  Finset.sum J (fun i => sign i J * f i * h (J.erase i))

omit [Fintype Index] [LinearOrder Index] in
theorem weightedCochain_degree (q : Index -> Real) (h : Finset Index -> Real)
    (k : Nat) (S : Finset Index) (hS : Not (S.card = k)) :
    weightedCochain q h k S = 0 := by simp [weightedCochain, hS]

omit [Fintype Index] in
theorem rootWeight_erase (q : Index -> Real) (J : Finset Index)
    (i : Index) (hi : Membership.mem J i) :
    Real.sqrt (q i) * rootWeight q (J.erase i) = rootWeight q J := by
  exact mul_prod_erase J (fun i => Real.sqrt (q i)) hi

omit [Fintype Index] in
theorem creation_weightedCochain (q f : Index -> Real) (h : Finset Index -> Real)
    (k : Nat) (J : Finset Index) (hJ : J.card = k + 1) :
    creation (fun i => Real.sqrt (q i) * f i) (weightedCochain q h k) J =
      rootWeight q J * boundary f h J := by
  unfold creation boundary
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hcard : (J.erase i).card = k := by
    have he := card_erase_of_mem hi
    omega
  rw [weightedCochain, ite_eq_left hcard]
  have hr := rootWeight_erase q J i hi
  calc
    sign i J * (Real.sqrt (q i) * f i) *
        (rootWeight q (J.erase i) * h (J.erase i)) =
        (Real.sqrt (q i) * rootWeight q (J.erase i)) *
          (sign i J * f i * h (J.erase i)) := by ring
    _ = rootWeight q J * (sign i J * f i * h (J.erase i)) := by rw [hr]

omit [Fintype Index] in
theorem weighted_cocycle_creation_zero (q : Index -> Real)
    (h : Finset Index -> Real) (k : Nat)
    (hcycle : forall J, J.card = k + 1 -> boundary (fun _ => 1) h J = 0) :
    creation (fun i => Real.sqrt (q i)) (weightedCochain q h k) = fun _ => 0 := by
  funext J
  by_cases hJ : J.card = k + 1
  next =>
    have he := creation_weightedCochain q (fun _ => 1) h k J hJ
    simp only [mul_one] at he
    rw [he, hcycle J hJ]
    ring
  next =>
    exact creation_degree k _ _ (weightedCochain_degree q h k) J hJ

omit [Fintype Index] in
theorem boundary_centering (f : Index -> Real) (h : Finset Index -> Real)
    (p : Real) (J : Finset Index)
    (hcycle : boundary (fun _ => 1) h J = 0) :
    boundary (fun i => f i - p) h J = boundary f h J := by
  have heq : boundary (fun i => f i - p) h J =
      boundary f h J - p * boundary (fun _ => 1) h J := by
    unfold boundary
    rw [mul_sum, <- sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq, hcycle]
  ring

omit [LinearOrder Index] in
theorem weightedCochain_energy (q : Index -> Real) (hq : forall i, 0 <= q i)
    (h : Finset Index -> Real) (k : Nat) :
    energy (weightedCochain q h k) =
      Finset.sum (grade (Index := Index) k) (fun I => weight q I * h I ^ 2) := by
  unfold energy dot weightedCochain grade
  rw [sum_filter]
  apply sum_congr rfl
  intro I _
  split_ifs
  next =>
    rw [<- pow_two, mul_pow]
    rw [rootWeight_sq q hq I]
  next =>
    ring

omit [LinearOrder Index] in
theorem weighted_reference_energy (q : Index -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum univ q = 1) :
    energy (fun i => Real.sqrt (q i)) = 1 := by
  unfold energy dot
  simp_rw [<- pow_two, Real.sq_sqrt (hq _)]
  exact hqsum

omit [LinearOrder Index] in
theorem weighted_label_energy (q f : Index -> Real)
    (hq : forall i, 0 <= q i)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    energy (fun i => Real.sqrt (q i) * f i) =
      Finset.sum univ (fun i => q i * f i) := by
  unfold energy dot
  simp_rw [<- pow_two, mul_pow, Real.sq_sqrt (hq _),
    Hypercube.Algebra.binary_square _ (hbinary _)]

omit [LinearOrder Index] in
theorem weighted_label_reference_dot (q f : Index -> Real)
    (hq : forall i, 0 <= q i) :
    dot (fun i => Real.sqrt (q i) * f i) (fun i => Real.sqrt (q i)) =
      Finset.sum univ (fun i => q i * f i) := by
  unfold dot
  apply sum_congr rfl
  intro i _
  have hs := Real.sq_sqrt (hq i)
  calc
    Real.sqrt (q i) * f i * Real.sqrt (q i) = Real.sqrt (q i) ^ 2 * f i := by ring
    _ = q i * f i := by rw [hs]

theorem weighted_cocycle_square_estimate (q f : Index -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (h : Finset Index -> Real) (k : Nat)
    (hcycle : forall J, J.card = k + 1 -> boundary (fun _ => 1) h J = 0) :
    let p := Finset.sum univ (fun i => q i * f i)
    Finset.sum (grade (Index := Index) (k + 1))
        (fun J => weight q J * boundary f h J ^ 2) <=
      p * (1 - p) * Finset.sum (grade (Index := Index) k)
        (fun I => weight q I * h I ^ 2) := by
  dsimp only
  let p := Finset.sum univ (fun i => q i * f i)
  let y := fun i => Real.sqrt (q i) * (f i - p)
  let B := weightedCochain q h k
  have hc (J : Finset Index) (hJ : J.card = k + 1) :
      creation y B J = rootWeight q J * boundary f h J := by
    dsimp [y, B]
    rw [creation_weightedCochain q (fun i => f i - p) h k J hJ,
      boundary_centering f h p J (hcycle J hJ)]
  have hb : forall S, Not (S.card = k) -> B S = 0 :=
    weightedCochain_degree q h k
  calc
    Finset.sum (grade (Index := Index) (k + 1))
        (fun J => weight q J * boundary f h J ^ 2) =
        Finset.sum (grade (Index := Index) (k + 1)) (fun J => creation y B J ^ 2) := by
      apply sum_congr rfl
      intro J hJ
      rw [hc J (mem_filter.mp hJ).2, mul_pow, rootWeight_sq q hq J]
    _ <= (Finset.sum univ (fun i => y i ^ 2)) * energy B :=
      creation_energy_le k y B hb
    _ = p * (1 - p) * Finset.sum (grade (Index := Index) k)
        (fun I => weight q I * h I ^ 2) := by
      have hy : Finset.sum univ (fun i => y i ^ 2) = p * (1 - p) :=
        Hypercube.Algebra.square_root_weighted_binary_variance q f hq hqsum hbinary
      rw [hy, weightedCochain_energy q hq h k]

theorem real_signed_unit_integer (a : Real)
    (ha : Or (a = -1) (Or (a = 0) (a = 1))) :
    exists z : Int, (z : Real) = a := by
  rcases ha with ha | ha | ha
  next =>
    exact Exists.intro (-1) (by simp [ha])
  next =>
    exact Exists.intro 0 (by simp [ha])
  next =>
    exact Exists.intro 1 (by simp [ha])

omit [Fintype Index] in
theorem finite_sum_integer (S : Finset Index) (a : Index -> Real)
    (ha : forall i, Membership.mem S i -> exists z : Int, (z : Real) = a i) :
    exists z : Int, (z : Real) = Finset.sum S a := by
  induction S using Finset.induction_on with
  | empty => exact Exists.intro 0 (by simp)
  | @insert i S hi ih =>
      let hiinteger := ha i (mem_insert_self i S)
      let zi := Classical.choose hiinteger
      have hzi := Classical.choose_spec hiinteger
      let hsinteger := ih (fun j hj => ha j (mem_insert_of_mem hj))
      let zs := Classical.choose hsinteger
      have hzs := Classical.choose_spec hsinteger
      refine Exists.intro (zi + zs) ?_
      rw [Int.cast_add, sum_insert hi, hzi, hzs]

omit [Fintype Index] in
theorem boundary_integer (f : Index -> Real)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (h : Finset Index -> Real) (k : Nat)
    (hunit : forall I, I.card = k -> Or (h I = -1) (Or (h I = 0) (h I = 1)))
    (J : Finset Index) (hJ : J.card = k + 1) :
    exists z : Int, (z : Real) = boundary f h J := by
  apply finite_sum_integer
  intro i hi
  have hcard : (J.erase i).card = k := by
    have he := card_erase_of_mem hi
    omega
  have hsign : Or (sign i J = -1) (Or (sign i J = 0) (sign i J = 1)) := by
    rcases sq_eq_one_iff.mp (sign_sq i J) with hp | hm
    next =>
      exact Or.inr (Or.inr hp)
    next =>
      exact Or.inl hm
  let hainteger := real_signed_unit_integer _ hsign
  let za := Classical.choose hainteger
  have hza := Classical.choose_spec hainteger
  have hf : Or (f i = -1) (Or (f i = 0) (f i = 1)) := Or.inr (hbinary i)
  let hfinteger := real_signed_unit_integer _ hf
  let zf := Classical.choose hfinteger
  have hzf := Classical.choose_spec hfinteger
  let hhinteger := real_signed_unit_integer _ (hunit _ hcard)
  let zh := Classical.choose hhinteger
  have hzh := Classical.choose_spec hhinteger
  refine Exists.intro (za * zf * zh) ?_
  rw [Int.cast_mul, Int.cast_mul, hza, hzf, hzh]

/-- The weighted binary cocycle inequality, including zero masses. -/
theorem weighted_binary_cocycle (q f : Index -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (h : Finset Index -> Real) (k : Nat)
    (hunit : forall I, I.card = k -> Or (h I = -1) (Or (h I = 0) (h I = 1)))
    (hcycle : forall J, J.card = k + 1 -> boundary (fun _ => 1) h J = 0) :
    let p := Finset.sum univ (fun i => q i * f i)
    Finset.sum (grade (Index := Index) (k + 1))
        (fun J => weight q J * |boundary f h J|) <=
      p * (1 - p) * Finset.sum (grade (Index := Index) k)
        (fun I => weight q I * |h I|) := by
  dsimp only
  let p := Finset.sum univ (fun i => q i * f i)
  calc
    Finset.sum (grade (Index := Index) (k + 1))
        (fun J => weight q J * |boundary f h J|) <=
        Finset.sum (grade (Index := Index) (k + 1))
          (fun J => weight q J * boundary f h J ^ 2) := by
      apply sum_le_sum
      intro J hJ
      let hjinteger := boundary_integer f hbinary h k hunit J (mem_filter.mp hJ).2
      let z := Classical.choose hjinteger
      have hz := Classical.choose_spec hjinteger
      have hw : 0 <= weight q J := Finset.prod_nonneg (fun i _ => hq i)
      apply mul_le_mul_of_nonneg_left _ hw
      rw [<- hz]
      exact Hypercube.Algebra.integer_abs_le_square z
    _ <= p * (1 - p) * Finset.sum (grade (Index := Index) k)
        (fun I => weight q I * h I ^ 2) :=
      weighted_cocycle_square_estimate q f hq hqsum hbinary h k hcycle
    _ = p * (1 - p) * Finset.sum (grade (Index := Index) k)
        (fun I => weight q I * |h I|) := by
      congr 1
      apply sum_congr rfl
      intro I hI
      rw [Hypercube.Algebra.signed_unit_square _ (hunit I (mem_filter.mp hI).2)]

omit [LinearOrder Index] in
/-- The finite-subset degree used internally is exactly the paper's subset set. -/
theorem grade_eq_powersetCard (k : Nat) :
    grade (Index := Index) k = (univ : Finset Index).powersetCard k := by
  ext S
  simp [grade]

/-- The position of a label in the increasing order on a finite subset. -/
def rankIn (i : Index) (J : Finset Index) : Nat :=
  (J.filter (fun j => j < i)).card

/-- The alternating omission sum in the manuscript, with the binary label included. -/
def alternatingSum (f : Index -> Real) (h : Finset Index -> Real)
    (J : Finset Index) : Real :=
  Finset.sum J (fun i => (-1 : Real) ^ rankIn i J * f i * h (J.erase i))

/-- The alternating omission sum without a binary label. -/
def cocycleSum (h : Finset Index -> Real) (J : Finset Index) : Real :=
  Finset.sum J (fun i => (-1 : Real) ^ rankIn i J * h (J.erase i))

/-- The same source coefficient written using j_0 < ... < j_(card J - 1). -/
def increasingAlternatingSum (f : Index -> Real) (h : Finset Index -> Real)
    (J : Finset Index) : Real :=
  Finset.sum univ (fun r : Fin J.card =>
    (-1 : Real) ^ r.val * f (J.orderEmbOfFin rfl r) *
      h (J.erase (J.orderEmbOfFin rfl r)))

omit [Fintype Index] in
theorem alternatingSum_eq_increasingAlternatingSum (f : Index -> Real)
    (h : Finset Index -> Real) (J : Finset Index) :
    alternatingSum f h J = increasingAlternatingSum f h J := by
  let e := J.orderEmbOfFin rfl
  let term := fun i => (-1 : Real) ^ rankIn i J * f i * h (J.erase i)
  have hs : Finset.sum ((univ : Finset (Fin J.card)).map e.toEmbedding) term =
      Finset.sum J term := by
    rw [J.map_orderEmbOfFin_univ rfl]
  change Finset.sum J term = increasingAlternatingSum f h J
  rw [<- hs, sum_map]
  unfold increasingAlternatingSum
  apply sum_congr rfl
  intro r _
  dsimp [term, e, rankIn]
  rw [card_filter_lt_orderEmbOfFin]

omit [Fintype Index] in
theorem boundary_eq_alternatingSum (f : Index -> Real)
    (h : Finset Index -> Real) (J : Finset Index) :
    boundary f h J = alternatingSum f h J := by
  simp only [boundary, alternatingSum, rankIn, sign_rank]

omit [Fintype Index] in
theorem boundary_one_eq_cocycleSum (h : Finset Index -> Real) (J : Finset Index) :
    boundary (fun _ => 1) h J = cocycleSum h J := by
  simp only [boundary, cocycleSum, rankIn, sign_rank, mul_one]

omit [Fintype Index] in
/-- Values assigned to subsets outside the required degree have no effect. -/
theorem alternatingSum_degree_ext (f : Index -> Real)
    (h h' : Finset Index -> Real) (k : Nat)
    (heq : forall I, I.card = k -> h I = h' I)
    (J : Finset Index) (hJ : J.card = k + 1) :
    alternatingSum f h J = alternatingSum f h' J := by
  unfold alternatingSum
  apply sum_congr rfl
  intro i hi
  have hcard : (J.erase i).card = k := by
    have he := card_erase_of_mem hi
    omega
  rw [heq _ hcard]

/-- Paper-facing Lemma 4.1, preserving the stated finite dimension and degree range.
Increasing subsets are represented by finite sets. The exponent `rankIn i J`
is the zero-based position r of i in the increasing enumeration of J.
All source assumptions occur explicitly; the zero-mass endpoint uses no division. -/
theorem weighted_binary_cocycle_paper {N k : Nat}
    (_hk : 1 <= k) (_hkN : k <= N)
    (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (h : Finset (Fin N) -> Real)
    (hunit : forall I, I.card = k -> Or (h I = -1) (Or (h I = 0) (h I = 1)))
    (hcycle : forall J, J.card = k + 1 -> cocycleSum h J = 0) :
    let p := Finset.sum univ (fun i => q i * f i)
    Finset.sum ((univ : Finset (Fin N)).powersetCard (k + 1))
        (fun J => (Finset.prod J q) * |alternatingSum f h J|) <=
      p * (1 - p) * Finset.sum ((univ : Finset (Fin N)).powersetCard k)
        (fun I => (Finset.prod I q) * |h I|) := by
  have hc : forall J, J.card = k + 1 -> boundary (fun _ => 1) h J = 0 := by
    intro J hJ
    rw [boundary_one_eq_cocycleSum]
    exact hcycle J hJ
  simpa only [grade_eq_powersetCard, weight, boundary_eq_alternatingSum] using
    weighted_binary_cocycle q f hq hqsum hbinary h k hunit hc

/-- Exact increasing-enumeration form of the paper's binary cocycle lemma. -/
theorem weighted_binary_cocycle_increasing {N k : Nat}
    (hk : 1 <= k) (hkN : k <= N)
    (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (h : Finset (Fin N) -> Real)
    (hunit : forall I, I.card = k -> Or (h I = -1) (Or (h I = 0) (h I = 1)))
    (hcycle : forall J, J.card = k + 1 ->
      increasingAlternatingSum (fun _ => 1) h J = 0) :
    let p := Finset.sum univ (fun i => q i * f i)
    Finset.sum ((univ : Finset (Fin N)).powersetCard (k + 1))
        (fun J => (Finset.prod J q) * |increasingAlternatingSum f h J|) <=
      p * (1 - p) * Finset.sum ((univ : Finset (Fin N)).powersetCard k)
        (fun I => (Finset.prod I q) * |h I|) := by
  have hc : forall J, J.card = k + 1 -> cocycleSum h J = 0 := by
    intro J hJ
    have he : cocycleSum h J = alternatingSum (fun _ => 1) h J := by
      simp only [cocycleSum, alternatingSum, mul_one]
    rw [he, alternatingSum_eq_increasingAlternatingSum]
    exact hcycle J hJ
  simpa only [alternatingSum_eq_increasingAlternatingSum] using
    weighted_binary_cocycle_paper hk hkN q f hq hqsum hbinary h hunit hc

end SubsetCoordinates

end Hypercube.BinaryCocycle
