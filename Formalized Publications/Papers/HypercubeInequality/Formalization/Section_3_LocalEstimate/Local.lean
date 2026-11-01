module

/-
# Exterior-algebra Bernoulli estimate (HI-LOCAL, HI-WEIGHTED)

Paper Sections 3–4 with `m = d - 1`: atoms `Z_i = (Y_i, B_i)` indexed by
`Fin N` (paper: `1, …, N`), probabilities `p`, binary heights `B`.

Representation bridge: the paper encodes the alternating cocycle
identities in the exterior algebra of `ℝ^N`.  Only the *coordinates* of
that computation are formalized: `d`-vector components on increasing
`d`-sets, wedge-with-vector coefficients `C_T` (with `wedgeSign`, which
matches the paper's `(-1)^{d-r}` exactly), and the Pythagorean identity
`wedge_pythagoras` (HI-LAGRANGE) in place of `‖V∧w‖ ≤ ‖V‖‖w‖`.  No
Mathlib exterior algebra is used; every exterior step is an explicit
finite-sum identity with the same constants.
-/

public import Mathlib
public import Section_1_Introduction.Core
public import Section_3_LocalEstimate.Lagrange
public import Section_2_Cocycle.Cocycle

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

variable {m N : ℕ} (p : Fin N → ℝ) (Yatom : Fin N → EuclideanSpace ℝ (Fin m))
  (B : Fin N → ℝ)

/-- Atom-set weight `w_J = ∏ p_i`. -/
@[expose] public noncomputable def atomWeight (J : Finset (Fin N)) : ℝ :=
  ∏ i ∈ J, p i

/-- Projected determinant `D(U)` via the increasing enumeration. -/
@[expose] public noncomputable def detOf (U : Finset (Fin N))
    (h : U.card = m + 1) : ℝ :=
  simDet (fun k => Yatom (U.orderEmbOfFin h k))

/-- Projected simplex hull `conv(Y_i : i ∈ U)`. -/
@[expose] public noncomputable def hullOf (U : Finset (Fin N)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  convexHull ℝ ((fun i => Yatom i) '' ↑U)

/-- Indicator `1_U(x)` as a real value. -/
@[expose] public noncomputable def indOf (U : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (hullOf Yatom U).indicator (1 : EuclideanSpace ℝ (Fin m) → ℝ) x

/-- Signed indicator `S_U(x) = sgn(D(U)) 1_U(x)`. -/
@[expose] public noncomputable def signedOf (U : Finset (Fin N))
    (h : U.card = m + 1) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sign (detOf Yatom U h) * indOf Yatom U x

/-- Mean height `p̄ = ∑ p_i B_i`. -/
@[expose] public noncomputable def pbar : ℝ :=
  ∑ i, p i * B i

/-- `d`-vector components `a_U = √w_U S_U` (`0` off the `d`-sets). -/
@[expose] public noncomputable def lawVec (x : EuclideanSpace ℝ (Fin m))
    (U : Finset (Fin N)) : ℝ :=
  if h : U.card = m + 1 then
    Real.sqrt (atomWeight p U) * signedOf Yatom U h x
  else 0

/-- Height-vector components `u_i = √p_i B_i`. -/
@[expose] public noncomputable def heightVec (i : Fin N) : ℝ :=
  Real.sqrt (p i) * B i

/-- Base-vector components `(v_0)_i = √p_i`. -/
@[expose] public noncomputable def baseVec (i : Fin N) : ℝ :=
  Real.sqrt (p i)

/-- Centered-vector components `b̃_i = √p_i (B_i - p̄)`. -/
@[expose] public noncomputable def centVec (i : Fin N) : ℝ :=
  Real.sqrt (p i) * (B i - pbar p B)

/-- Wedge coefficient `C_T(c) = ∑_{i∈T} ±a_{T∖i} c_i`. -/
@[expose] public noncomputable def wedgeCoeff (T : Finset (Fin N))
    (c : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i ∈ T, wedgeSign T i * lawVec p Yatom x (T.erase i) * c i

/-- Erasing one element of a `(d+1)`-set leaves a `d`-set. -/
public theorem erase_card (T : Finset (Fin N)) (hT : T.card = m + 2)
    (i : Fin N) (hi : i ∈ T) : (T.erase i).card = m + 1 := by
  rw [Finset.card_erase_of_mem hi, hT]
  omega

/-- `lawVec` unfolds on `d`-sets. -/
public theorem lawVec_eq (x : EuclideanSpace ℝ (Fin m))
    (U : Finset (Fin N)) (h : U.card = m + 1) :
    lawVec p Yatom x U
      = Real.sqrt (atomWeight p U) * signedOf Yatom U h x := by
  simp only [lawVec]
  exact dite_eq_left h

/-- Weights are positive for positive probabilities. -/
public theorem atomWeight_pos (hpos : ∀ i, 0 < p i)
    (J : Finset (Fin N)) : 0 < atomWeight p J := by
  simp only [atomWeight]
  exact Finset.prod_pos (fun i _ => hpos i)

/-- Weights are nonnegative for positive probabilities. -/
public theorem atomWeight_nonneg (hpos : ∀ i, 0 < p i)
    (J : Finset (Fin N)) : 0 ≤ atomWeight p J :=
  le_of_lt (atomWeight_pos p hpos J)

/-- The weight splits off one atom. -/
public theorem atomWeight_erase_mul (T : Finset (Fin N))
    (i : Fin N) (hi : i ∈ T) :
    atomWeight p (T.erase i) * p i = atomWeight p T := by
  simp only [atomWeight]
  rw [mul_comm]
  exact Finset.mul_prod_erase _ _ hi

/-- Square roots split likewise. -/
public theorem sqrt_atomWeight_erase (hpos : ∀ i, 0 < p i)
    (T : Finset (Fin N)) (i : Fin N) (hi : i ∈ T) :
    Real.sqrt (atomWeight p T)
      = Real.sqrt (atomWeight p (T.erase i)) * Real.sqrt (p i) := by
  rw [← atomWeight_erase_mul p T i hi,
    Real.sqrt_mul (atomWeight_nonneg p hpos _)]

/-- The wedge sign is `(-1)` to the number of greater elements. -/
public theorem wedgeSign_eq_neg_one_pow (T : Finset (Fin N)) (i : Fin N) :
    wedgeSign T i
      = (-1) ^ (T.filter (fun j => i < j)).card := by
  have h1 : ∏ j ∈ T.filter (fun j => i < j),
      (if i < j then (-1 : ℝ) else 1)
      = (-1) ^ (T.filter (fun j => i < j)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : i < j := (Finset.mem_filter.mp hj).2
    simp [hj']
  have h0 : ∏ j ∈ T.filter (fun j => ¬ i < j),
      (if i < j then (-1 : ℝ) else 1) = 1 := by
    rw [← Finset.prod_const_one]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : ¬ i < j := (Finset.mem_filter.mp hj).2
    simp [hj']
  simp only [wedgeSign]
  have hsplit := Finset.prod_filter_mul_prod_filter_not T (fun j => i < j)
    (fun j => if i < j then (-1 : ℝ) else 1)
  rw [← hsplit, h1, h0, mul_one]

/-- Elements above the `r`-th element biject with `Ioi r`. -/
public theorem card_filter_gt_orderEmbOfFin (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    (T.filter (fun j => T.orderEmbOfFin hT r < j)).card
      = m + 1 - r.val := by
  have hbij : (Finset.Ioi r).card
      = (T.filter (fun j => T.orderEmbOfFin hT r < j)).card := by
    apply Finset.card_bij (fun s _ => T.orderEmbOfFin hT s)
    · intro s hs
      rw [Finset.mem_Ioi] at hs
      simp only [Finset.mem_filter]
      refine ⟨T.orderEmbOfFin_mem hT s, ?_⟩
      exact (T.orderEmbOfFin hT).strictMono.lt_iff_lt.mpr hs
    · intro a _ b _ hab
      exact (T.orderEmbOfFin hT).injective hab
    · intro b hb
      obtain ⟨hbT, hblt⟩ := Finset.mem_filter.mp hb
      have hbrange : b ∈ Set.range (T.orderEmbOfFin hT) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hbT
      obtain ⟨a, ha⟩ := hbrange
      refine ⟨a, ?_, ?_⟩
      · rw [Finset.mem_Ioi]
        have hlt : T.orderEmbOfFin hT r < T.orderEmbOfFin hT a :=
          ha ▸ hblt
        exact (T.orderEmbOfFin hT).strictMono.lt_iff_lt.mp hlt
      · exact ha
  rw [← hbij, Fin.card_Ioi]
  omega

/-- The wedge sign at the `r`-th element of a `(d+1)`-set. -/
public theorem wedgeSign_orderEmbOfFin (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    wedgeSign T (T.orderEmbOfFin hT r) = (-1) ^ (m + 1 - r.val) := by
  rw [wedgeSign_eq_neg_one_pow,
    card_filter_gt_orderEmbOfFin T hT r]

/-- Strictly monotone maps `Fin n → Fin N` with the same range are equal
(restriction induction). -/
public theorem strictMono_eq_of_range_eq {n : ℕ} {f g : Fin n → Fin N}
    (hf : StrictMono f) (hg : StrictMono g)
    (hr : Set.range f = Set.range g) : f = g := by
  induction n with
  | zero =>
    funext k
    exact Fin.elim0 k
  | succ n ih =>
    have h0 : f 0 = g 0 := by
      have hf0 : ∀ k, f 0 ≤ f k := fun k => hf.monotone (Fin.zero_le k)
      have hg0 : ∀ k, g 0 ≤ g k := fun k => hg.monotone (Fin.zero_le k)
      obtain ⟨k, hk⟩ : g 0 ∈ Set.range f := hr ▸ ⟨0, rfl⟩
      obtain ⟨j, hj⟩ : f 0 ∈ Set.range g := hr.symm ▸ ⟨0, rfl⟩
      have h1 : f 0 ≤ g 0 := hk ▸ hf0 k
      have h2 : g 0 ≤ f 0 := hj ▸ hg0 j
      exact le_antisymm h1 h2
    have hf' : StrictMono (f ∘ Fin.succ) := hf.comp Fin.strictMono_succ
    have hg' : StrictMono (g ∘ Fin.succ) := hg.comp Fin.strictMono_succ
    have erange : ∀ h : Fin (n + 1) → Fin N, ∀ hh : StrictMono h,
        Set.range (h ∘ Fin.succ) = Set.range h \ {h 0} := by
      intro h hh
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨⟨_, rfl⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact ne_of_gt (hh (Fin.succ_pos k))
      · rintro ⟨⟨k, rfl⟩, hne⟩
        simp only [Set.mem_singleton_iff] at hne
        have hk0 : k ≠ 0 := fun heq => hne (congrArg _ heq)
        rw [← Fin.succ_pred k hk0]
        exact ⟨_, rfl⟩
    have hr' : Set.range (f ∘ Fin.succ) = Set.range (g ∘ Fin.succ) := by
      rw [erange f hf, erange g hg, hr, h0]
    have heq := ih hf' hg' hr'
    funext k
    by_cases hk : k = 0
    · subst hk
      exact h0
    · rw [← Fin.succ_pred k hk]
      exact congrFun heq (k.pred hk)

/-- The erase-enumeration equals the composed enumeration. -/
public theorem orderEmbOfFin_erase (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    (T.erase (T.orderEmbOfFin hT r)).orderEmbOfFin
        (erase_card T hT _ (T.orderEmbOfFin_mem hT r))
      = fun k => T.orderEmbOfFin hT (r.succAbove k) := by
  apply strictMono_eq_of_range_eq
  · exact (Finset.orderEmbOfFin _ _).strictMono
  · exact ((T.orderEmbOfFin hT).strictMono.comp
      (Fin.strictMono_succAbove r))
  · rw [Finset.range_orderEmbOfFin]
    have hcomp : Set.range (T.orderEmbOfFin hT ∘ r.succAbove)
        = ↑(T.erase (T.orderEmbOfFin hT r)) := by
      rw [Set.range_comp, Fin.range_succAbove]
      ext b
      simp only [Set.mem_image, Set.mem_compl_iff,
        Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_erase]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨?_, T.orderEmbOfFin_mem hT a⟩
        exact fun h => ha ((T.orderEmbOfFin hT).injective h)
      · rintro ⟨hne, hbT⟩
        have hbrange : b ∈ Set.range (T.orderEmbOfFin hT) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.mpr hbT
        obtain ⟨a, ha⟩ := hbrange
        refine ⟨a, ?_, ha⟩
        intro hcon
        rw [hcon] at ha
        exact hne ha.symm
    exact hcomp.symm

/-- Reindexing a sum over `T` through the increasing enumeration. -/
public theorem sum_orderEmbOfFin (T : Finset (Fin N)) (hT : T.card = m + 2)
    (F : Fin N → ℝ) :
    ∑ i ∈ T, F i = ∑ r : Fin (m + 2), F (T.orderEmbOfFin hT r) := by
  have h : ∑ r ∈ (Finset.univ : Finset (Fin (m + 2))),
      F (T.orderEmbOfFin hT r) = ∑ i ∈ T, F i :=
    Finset.sum_bij (fun r _ => T.orderEmbOfFin hT r)
      (fun r _ => T.orderEmbOfFin_mem hT r)
      (fun a _ b _ hab => (T.orderEmbOfFin hT).injective hab)
      (fun b hb => by
        have hbrange : b ∈ Set.range (T.orderEmbOfFin hT) := by
          rw [Finset.range_orderEmbOfFin]
          exact Finset.mem_coe.mpr hb
        obtain ⟨a, ha⟩ := hbrange
        exact ⟨a, Finset.mem_univ a, ha⟩)
      (fun r _ => rfl)
  exact h.symm

/-- The cocycle tuple of a `(d+1)`-set. -/
@[expose] public noncomputable def cocycleTupleOf (T : Finset (Fin N))
    (hT : T.card = m + 2) : Fin (m + 2) → EuclideanSpace ℝ (Fin m) :=
  fun r => Yatom (T.orderEmbOfFin hT r)

/-- `D(T∖{t_r})` equals the cocycle deletion determinant. -/
public theorem detOf_erase_eq_cocycleDet (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    detOf Yatom (T.erase (T.orderEmbOfFin hT r))
        (erase_card T hT _ (T.orderEmbOfFin_mem hT r))
      = cocycleDet (cocycleTupleOf Yatom T hT) r := by
  simp only [detOf, cocycleDet]
  refine congrArg simDet ?_
  funext k
  exact congrArg _ (congrFun (orderEmbOfFin_erase T hT r) k)

/-- `1_{T∖{t_r}}` equals the cocycle omission indicator. -/
public theorem indOf_erase_eq_cocycleSimplex (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2))
    (x : EuclideanSpace ℝ (Fin m)) :
    indOf Yatom (T.erase (T.orderEmbOfFin hT r)) x
      = (cocycleSimplex (cocycleTupleOf Yatom T hT) r).indicator
          (1 : EuclideanSpace ℝ (Fin m) → ℝ) x := by
  have hset : hullOf Yatom (T.erase (T.orderEmbOfFin hT r))
      = cocycleSimplex (cocycleTupleOf Yatom T hT) r := by
    show convexHull ℝ ((fun i => Yatom i) '' ↑(T.erase (T.orderEmbOfFin hT r)))
      = convexHull ℝ (Set.range
          (fun i => Yatom (T.orderEmbOfFin hT (r.succAbove i))))
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe,
      Finset.mem_erase]
    constructor
    · rintro ⟨b, ⟨hne, hbT⟩, rfl⟩
      have hbrange : b ∈ Set.range (T.orderEmbOfFin hT) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hbT
      obtain ⟨a, ha⟩ := hbrange
      have har : a ≠ r := by
        intro hcon
        rw [hcon] at ha
        exact hne ha.symm
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq har
      exact ⟨j, by rw [hj, ha]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨T.orderEmbOfFin hT (r.succAbove i),
        ⟨?_, T.orderEmbOfFin_mem hT _⟩, rfl⟩
      intro hcon
      have hinj := (T.orderEmbOfFin hT).injective
      have hsing : r.succAbove i = r := hinj hcon
      exact r.succAbove_ne i hsing
  rw [indOf, hset]

/-- `(-1)^{m+1-r} = (-1)^{m+1} (-1)^r`. -/
public theorem neg_one_pow_sub (r : Fin (m + 2)) :
    (-1 : ℝ) ^ (m + 1 - r.val) = (-1) ^ (m + 1) * (-1) ^ (r.val) := by
  have hsq : ((-1 : ℝ) ^ r.val) * ((-1 : ℝ) ^ r.val) = 1 := by
    rw [← pow_two, ← pow_mul]
    exact Even.neg_one_pow ⟨r.val, mul_two r.val⟩
  have hbase : r.val ≤ m + 1 := by omega
  have hexp : m + 1 - r.val + r.val = m + 1 := Nat.sub_add_cancel hbase
  have hpow : (-1 : ℝ) ^ (m + 1)
      = (-1) ^ (m + 1 - r.val) * (-1) ^ r.val := by
    have h := pow_add (-1 : ℝ) (m + 1 - r.val) r.val
    rw [hexp] at h
    exact h
  calc (-1 : ℝ) ^ (m + 1 - r.val)
      = (-1) ^ (m + 1 - r.val) * 1 := (mul_one _).symm
    _ = (-1) ^ (m + 1 - r.val) * ((-1) ^ r.val * (-1) ^ r.val) := by
        rw [hsq]
    _ = ((-1) ^ (m + 1 - r.val) * (-1) ^ r.val) * (-1) ^ r.val := by
        ring
    _ = (-1) ^ (m + 1) * (-1) ^ r.val := by rw [← hpow]

/-- One wedge-coefficient summand in factored form. -/
public theorem wedgeCoeff_term (hpos : ∀ i, 0 < p i)
    (T : Finset (Fin N)) (hT : T.card = m + 2)
    (f : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (r : Fin (m + 2)) :
    wedgeSign T (T.orderEmbOfFin hT r)
        * lawVec p Yatom x (T.erase (T.orderEmbOfFin hT r))
        * (Real.sqrt (p (T.orderEmbOfFin hT r)) * f (T.orderEmbOfFin hT r))
      = (-1) ^ (m + 1) * Real.sqrt (atomWeight p T)
        * ((-1) ^ (r.val) * signedOf Yatom
            (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x
          * f (T.orderEmbOfFin hT r)) := by
  rw [wedgeSign_orderEmbOfFin T hT r,
    lawVec_eq _ _ _ _ (erase_card T hT _ (T.orderEmbOfFin_mem hT r)),
    neg_one_pow_sub r,
    sqrt_atomWeight_erase p hpos T _ (T.orderEmbOfFin_mem hT r)]
  ring

/-- The paper's `s_T(x)`: signed omission sum weighted by `f`. -/
@[expose] public noncomputable def signedSumT (T : Finset (Fin N))
    (hT : T.card = m + 2) (f : Fin N → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ r : Fin (m + 2), (-1) ^ (r.val : ℕ)
    * signedOf Yatom (T.erase (T.orderEmbOfFin hT r))
        (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x
    * f (T.orderEmbOfFin hT r)

/-- Wedge coefficients factor through the signed omission sum. -/
public theorem wedgeCoeff_eq (hpos : ∀ i, 0 < p i)
    (T : Finset (Fin N)) (hT : T.card = m + 2)
    (f : Fin N → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    wedgeCoeff p Yatom T (fun i => Real.sqrt (p i) * f i) x
      = (-1) ^ (m + 1) * Real.sqrt (atomWeight p T)
        * signedSumT Yatom T hT f x := by
  simp only [wedgeCoeff, signedSumT]
  rw [sum_orderEmbOfFin T hT, Finset.mul_sum]
  exact Finset.sum_congr rfl
    (fun r _ => wedgeCoeff_term p Yatom hpos T hT f x r)

/-- The unweighted omission sum is the cocycle sum. -/
public theorem signedSumT_one_eq_cocycle (T : Finset (Fin N))
    (hT : T.card = m + 2) (x : EuclideanSpace ℝ (Fin m)) :
    signedSumT Yatom T hT (fun _ => 1) x
      = ∑ r, cocycleSigma (cocycleTupleOf Yatom T hT) r
        * (cocycleSimplex (cocycleTupleOf Yatom T hT) r).indicator
            (1 : EuclideanSpace ℝ (Fin m) → ℝ) x := by
  simp only [signedSumT, signedOf]
  apply Finset.sum_congr rfl
  intro r _
  rw [detOf_erase_eq_cocycleDet Yatom T hT r,
    indOf_erase_eq_cocycleSimplex Yatom T hT r x]
  simp only [cocycleSigma]
  ring

/-- Each `C_T(v_0)` vanishes almost everywhere. -/
public theorem wedgeCoeff_baseVec_ae (hpos : ∀ i, 0 < p i)
    (T : Finset (Fin N)) (hT : T.card = m + 2) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      wedgeCoeff p Yatom T (baseVec p) x = 0 := by
  have hbase : baseVec p = fun i => Real.sqrt (p i) * 1 := by
    funext i
    simp [baseVec, mul_one]
  rw [hbase]
  have hcoc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∑ r, cocycleSigma (cocycleTupleOf Yatom T hT) r
        * (cocycleSimplex (cocycleTupleOf Yatom T hT) r).indicator
            (1 : EuclideanSpace ℝ (Fin m) → ℝ) x = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      exact cocycle_dim1 (cocycleTupleOf Yatom T hT)
    · exact cocycle_alternating_sum hmpos (cocycleTupleOf Yatom T hT)
  filter_upwards [hcoc] with x hx
  rw [wedgeCoeff_eq p Yatom hpos T hT (fun _ => 1) x,
    signedSumT_one_eq_cocycle Yatom T hT x, hx, mul_zero]

/-- All `C_T(v_0)` vanish simultaneously outside one null set. -/
public theorem wedgeCoeff_baseVec_all_ae (hpos : ∀ i, 0 < p i) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        wedgeCoeff p Yatom T (baseVec p) x = 0 := by
  rw [Filter.eventually_all_finset]
  intro T hT
  have hcard : T.card = m + 2 := (Finset.mem_powersetCard.mp hT).2
  exact wedgeCoeff_baseVec_ae p Yatom hpos T hcard

/-- `((-1)^n)^2 = 1`. -/
public theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨n, mul_two n⟩

/-- Bernoulli variance: `‖b̃‖² = p̄(1-p̄)`. -/
public theorem centVec_sq_sum (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hbin : ∀ i, B i = 0 ∨ B i = 1) :
    ∑ i, (centVec p B i) ^ 2 = pbar p B * (1 - pbar p B) := by
  have hB2 : ∀ i, (B i) ^ 2 = B i := by
    intro i
    rcases hbin i with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hterm : ∀ i : Fin N, (centVec p B i) ^ 2
      = p i * B i - 2 * pbar p B * (p i * B i)
        + (pbar p B) ^ 2 * p i := by
    intro i
    simp only [centVec]
    have hsqrt : (Real.sqrt (p i)) ^ 2 = p i :=
      Real.sq_sqrt (le_of_lt (hpos i))
    rw [mul_pow, hsqrt]
    have hexpand : (B i - pbar p B) ^ 2
        = B i - 2 * B i * pbar p B + (pbar p B) ^ 2 := by
      have hrr : (B i - pbar p B) ^ 2
          = (B i) ^ 2 - 2 * B i * pbar p B + (pbar p B) ^ 2 := by
        ring
      rw [hB2 i] at hrr
      exact hrr
    rw [hexpand]
    ring
  calc ∑ i, (centVec p B i) ^ 2
      = ∑ i, (p i * B i - 2 * pbar p B * (p i * B i)
          + (pbar p B) ^ 2 * p i) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = pbar p B * (1 - pbar p B) := by
        simp only [pbar]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hsum]
        ring

/-- `S_U² ≤ 1_U` pointwise. -/
public theorem signedOf_sq_le_indOf (U : Finset (Fin N))
    (h : U.card = m + 1) (x : EuclideanSpace ℝ (Fin m)) :
    (signedOf Yatom U h x) ^ 2 ≤ indOf Yatom U x := by
  have hsgn : (Real.sign (detOf Yatom U h)) ^ 2 ≤ 1 := by
    rcases Real.sign_apply_eq (detOf Yatom U h) with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hind2 : (indOf Yatom U x) ^ 2 = indOf Yatom U x := by
    simp only [indOf]
    by_cases hx : x ∈ hullOf Yatom U
    · rw [Set.indicator_of_mem hx _]
      simp
    · rw [Set.indicator_of_notMem hx _]
      norm_num
  have hindnn : 0 ≤ indOf Yatom U x := by
    simp only [indOf]
    by_cases hx : x ∈ hullOf Yatom U
    · rw [Set.indicator_of_mem hx _]
      simp
    · rw [Set.indicator_of_notMem hx _]
  simp only [signedOf, mul_pow]
  rw [hind2]
  calc (Real.sign (detOf Yatom U h)) ^ 2 * indOf Yatom U x
      ≤ 1 * indOf Yatom U x :=
        mul_le_mul_of_nonneg_right hsgn hindnn
    _ = indOf Yatom U x := one_mul _

/-- `|k| ≤ k²` for integers (as reals). -/
public theorem abs_le_sq_of_int (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    norm_num
  · have hcast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
      calc ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℤ)) : ℝ) := by
            rw [Int.cast_natCast]
        _ = ((|k| : ℤ) : ℝ) := by rw [Int.abs_eq_natAbs]
        _ = |(k : ℝ)| := Int.cast_abs
    have hn : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← hcast]
      exact_mod_cast hn
    calc |(k : ℝ)| ≤ |(k : ℝ)| ^ 2 := by
          nlinarith [mul_nonneg (abs_nonneg (k : ℝ))
            (sub_nonneg.mpr h1)]
      _ = (k : ℝ) ^ 2 := by rw [sq_abs]

/-- `(-1)^n` is an integer cast. -/
public theorem neg_one_pow_int (n : ℕ) : ∃ a : ℤ, (-1 : ℝ) ^ n = (a : ℝ) := by
  rcases Nat.even_or_odd n with h | h
  · exact ⟨1, by rw [h.neg_one_pow]; norm_num⟩
  · exact ⟨-1, by rw [h.neg_one_pow]; norm_num⟩

/-- `s_T(B)` is an integer. -/
public theorem signedSumT_int (hbin : ∀ i, B i = 0 ∨ B i = 1)
    (T : Finset (Fin N)) (hT : T.card = m + 2)
    (x : EuclideanSpace ℝ (Fin m)) :
    ∃ K : ℤ, signedSumT Yatom T hT B x = (K : ℝ) := by
  have hsgn : ∀ r : Fin (m + 2), ∃ a : ℤ,
      Real.sign (detOf Yatom (T.erase (T.orderEmbOfFin hT r))
        (erase_card T hT _ (T.orderEmbOfFin_mem hT r))) = (a : ℝ) := by
    intro r
    rcases Real.sign_apply_eq _ with h | h | h
    · exact ⟨-1, by rw [h]; norm_num⟩
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  have hind : ∀ r : Fin (m + 2), ∃ b : ℤ,
      indOf Yatom (T.erase (T.orderEmbOfFin hT r)) x = (b : ℝ) := by
    intro r
    simp only [indOf]
    by_cases hx : x ∈ hullOf Yatom (T.erase (T.orderEmbOfFin hT r))
    · exact ⟨1, by rw [Set.indicator_of_mem hx _]; simp⟩
    · exact ⟨0, by rw [Set.indicator_of_notMem hx _]; norm_num⟩
  have hB : ∀ r : Fin (m + 2), ∃ c : ℤ,
      B (T.orderEmbOfFin hT r) = (c : ℝ) := by
    intro r
    rcases hbin _ with h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  have hterm : ∀ r : Fin (m + 2), ∃ K : ℤ,
      (-1 : ℝ) ^ (r.val) * signedOf Yatom
        (T.erase (T.orderEmbOfFin hT r))
        (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x
        * B (T.orderEmbOfFin hT r) = (K : ℝ) := by
    intro r
    obtain ⟨a, ha⟩ := neg_one_pow_int r.val
    obtain ⟨s, hs⟩ := hsgn r
    obtain ⟨b, hb⟩ := hind r
    obtain ⟨c, hc⟩ := hB r
    refine ⟨a * (s * b) * c, ?_⟩
    simp only [signedOf]
    rw [ha, hs, hb, hc]
    push_cast
    ring
  choose K hK using hterm
  refine ⟨∑ r, K r, ?_⟩
  simp only [signedSumT]
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl (fun r _ => hK r)

/-- Totalized `s_T(B)` (`0` off the `(d+1)`-sets). -/
@[expose] public noncomputable def signedSumT' (T : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  if hT : T.card = m + 2 then signedSumT Yatom T hT B x else 0

/-- `signedSumT'` unfolds on `(d+1)`-sets. -/
public theorem signedSumT'_eq (T : Finset (Fin N))
    (hT : T.card = m + 2) (x : EuclideanSpace ℝ (Fin m)) :
    signedSumT' Yatom B T x = signedSumT Yatom T hT B x := by
  simp only [signedSumT']
  exact dite_eq_left hT

/-- Wedge coefficients are linear in the vector argument. -/
public theorem wedgeCoeff_sub (T : Finset (Fin N))
    (c₁ c₂ : Fin N → ℝ) (k : ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    wedgeCoeff p Yatom T (fun i => c₁ i - k * c₂ i) x
      = wedgeCoeff p Yatom T c₁ x - k * wedgeCoeff p Yatom T c₂ x := by
  have hterm : ∀ i ∈ T, wedgeSign T i * lawVec p Yatom x (T.erase i)
        * (c₁ i - k * c₂ i)
      = (wedgeSign T i * lawVec p Yatom x (T.erase i) * c₁ i)
        - k * (wedgeSign T i * lawVec p Yatom x (T.erase i) * c₂ i) :=
    fun i _ => by ring
  simp only [wedgeCoeff]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

/-- Centered coefficients equal uncentered ones when `C_T(v_0) = 0`. -/
public theorem wedgeCoeff_centVec_eq (T : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin m))
    (h0 : wedgeCoeff p Yatom T (baseVec p) x = 0) :
    wedgeCoeff p Yatom T (centVec p B) x
      = wedgeCoeff p Yatom T (heightVec p B) x := by
  have hdecomp : ∀ i, centVec p B i
      = heightVec p B i - pbar p B * baseVec p i := by
    intro i
    simp only [centVec, heightVec, baseVec]
    ring
  have hfun : centVec p B
      = fun i => heightVec p B i - pbar p B * baseVec p i :=
    funext hdecomp
  rw [hfun, wedgeCoeff_sub p Yatom T _ _ _ x, h0, mul_zero, sub_zero]

/-- `C_T(u)² = w_T s_T²`. -/
public theorem wedgeCoeff_heightVec_sq (hpos : ∀ i, 0 < p i)
    (T : Finset (Fin N)) (hT : T.card = m + 2)
    (x : EuclideanSpace ℝ (Fin m)) :
    (wedgeCoeff p Yatom T (heightVec p B) x) ^ 2
      = atomWeight p T * (signedSumT Yatom T hT B x) ^ 2 := by
  have hu : heightVec p B = fun i => Real.sqrt (p i) * B i := rfl
  rw [hu, wedgeCoeff_eq p Yatom hpos T hT B x]
  have hsqrt : (Real.sqrt (atomWeight p T)) ^ 2 = atomWeight p T :=
    Real.sq_sqrt (atomWeight_nonneg p hpos T)
  rw [mul_pow, mul_pow, neg_one_pow_sq, hsqrt]
  ring

/-- `‖a‖² ≤ ∑ w_U 1_U` pointwise. -/
public theorem lawVec_sq_sum_le (hpos : ∀ i, 0 < p i)
    (x : EuclideanSpace ℝ (Fin m)) :
    ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
        (lawVec p Yatom x U) ^ 2
      ≤ ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
        atomWeight p U * indOf Yatom U x := by
  apply Finset.sum_le_sum
  intro U hU
  have hcard : U.card = m + 1 := (Finset.mem_powersetCard.mp hU).2
  rw [lawVec_eq p Yatom x U hcard, mul_pow,
    Real.sq_sqrt (atomWeight_nonneg p hpos U)]
  exact mul_le_mul_of_nonneg_left
    (signedOf_sq_le_indOf Yatom U hcard x)
    (atomWeight_nonneg p hpos U)

/-- The mean height lies in `[0, 1]`. -/
public theorem pbar_mem_Icc (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hbin : ∀ i, B i = 0 ∨ B i = 1) :
    0 ≤ pbar p B ∧ pbar p B ≤ 1 := by
  constructor
  · simp only [pbar]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (le_of_lt (hpos i))
    rcases hbin i with h | h <;> simp [h]
  · simp only [pbar]
    calc ∑ i, p i * B i ≤ ∑ i, p i * 1 := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (hpos i))
          rcases hbin i with h | h <;> simp [h]
      _ = 1 := by
          simp only [mul_one]
          exact hsum

/-- Lemma 3.1 (Local Bernoulli estimate). -/
public theorem local_bernoulli_estimate (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hbin : ∀ i, B i = 0 ∨ B i = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T * |signedSumT' Yatom B T x|
        ≤ pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * indOf Yatom U x := by
  filter_upwards [wedgeCoeff_baseVec_all_ae p Yatom hpos] with x hC0
  have hcardT : ∀ T ∈ Finset.powersetCard (m + 2)
      (Finset.univ : Finset (Fin N)), T.card = m + 2 :=
    fun T hT => (Finset.mem_powersetCard.mp hT).2
  have hstep1 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |signedSumT' Yatom B T x|
      ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * (signedSumT' Yatom B T x) ^ 2 := by
    apply Finset.sum_le_sum
    intro T hT
    have hTc := hcardT T hT
    rw [signedSumT'_eq Yatom B T hTc x]
    refine mul_le_mul_of_nonneg_left ?_ (atomWeight_nonneg p hpos T)
    obtain ⟨K, hK⟩ := signedSumT_int Yatom B hbin T hTc x
    rw [hK]
    exact abs_le_sq_of_int K
  have hstep2 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * (signedSumT' Yatom B T x) ^ 2
      = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        (wedgeCoeff p Yatom T (heightVec p B) x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro T hT
    have hTc := hcardT T hT
    rw [signedSumT'_eq Yatom B T hTc x,
      wedgeCoeff_heightVec_sq p Yatom B hpos T hTc x]
  have hstep3 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        (wedgeCoeff p Yatom T (heightVec p B) x) ^ 2
      = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        (wedgeCoeff p Yatom T (centVec p B) x) ^ 2 := by
    apply Finset.sum_congr rfl
    intro T hT
    have hC0T := hC0 T hT
    rw [wedgeCoeff_centVec_eq p Yatom B T x hC0T]
  have hstep4 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        (wedgeCoeff p Yatom T (centVec p B) x) ^ 2
      ≤ (∑ i, (centVec p B i) ^ 2)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          (lawVec p Yatom x U) ^ 2 := by
    have hpyth := wedge_pythagoras (N := N) (d := m + 1)
      (by omega : 1 ≤ m + 1) (lawVec p Yatom x) (centVec p B)
    have hR : 0 ≤ ∑ W ∈ Finset.powersetCard (m + 1 - 1) Finset.univ,
        (∑ i ∈ Finset.univ \ W,
          wedgeSign (insert i W) i * lawVec p Yatom x (insert i W)
            * centVec p B i) ^ 2 := by
      apply Finset.sum_nonneg
      intro W _
      exact sq_nonneg _
    have hidx : m + 1 + 1 = m + 2 := by omega
    have hTeq : (∑ T ∈ Finset.powersetCard (m + 1 + 1) Finset.univ,
          (∑ i ∈ T, wedgeSign T i * lawVec p Yatom x (T.erase i)
            * centVec p B i) ^ 2)
        = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          (wedgeCoeff p Yatom T (centVec p B) x) ^ 2 := by
      rw [hidx]
      apply Finset.sum_congr rfl
      intro T _
      simp only [wedgeCoeff]
    rw [hTeq] at hpyth
    linarith [hpyth, hR]
  calc ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T * |signedSumT' Yatom B T x|
      ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T * (signedSumT' Yatom B T x) ^ 2 := hstep1
    _ = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          (wedgeCoeff p Yatom T (heightVec p B) x) ^ 2 := hstep2
    _ = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          (wedgeCoeff p Yatom T (centVec p B) x) ^ 2 := hstep3
    _ ≤ (∑ i, (centVec p B i) ^ 2)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            (lawVec p Yatom x U) ^ 2 := hstep4
    _ = pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            (lawVec p Yatom x U) ^ 2 := by
        rw [centVec_sq_sum p B hpos hsum hbin]
    _ ≤ pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * indOf Yatom U x := by
        apply mul_le_mul_of_nonneg_left _ _
        · exact lawVec_sq_sum_le p Yatom hpos x
        · obtain ⟨hlo, hhi⟩ := pbar_mem_Icc p B hpos hsum hbin
          exact mul_nonneg hlo (sub_nonneg.mpr hhi)

/-- The `A_T(B)` matrix (B-column first; the paper uses B last, a
documented column-order difference affecting only an overall sign that
drops out of `|A_T|`). -/
@[expose] public noncomputable def detATMat (T : Finset (Fin N))
    (hT : T.card = m + 2) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of (fun r c =>
    Fin.cases (B (T.orderEmbOfFin hT r))
      (fun j => Fin.cases (1 : ℝ)
        (fun t => Yatom (T.orderEmbOfFin hT r) t) j) c)

/-- The lifted determinant `A_T(B)`. -/
@[expose] public noncomputable def detAT (T : Finset (Fin N))
    (hT : T.card = m + 2) : ℝ :=
  Matrix.det (detATMat Yatom B T hT)

/-- Deletion minor of the `A_T(B)` matrix. -/
@[expose] public noncomputable def detATMinor (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of (fun a b => Fin.cases (1 : ℝ)
    (fun t => Yatom ((T.erase (T.orderEmbOfFin hT r)).orderEmbOfFin
      (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) a) t) b)

/-- The deletion minor is the `D`-matrix of the erased tuple. -/
public theorem detAT_minor (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    (detATMat Yatom B T hT).submatrix r.succAbove Fin.succ
      = detATMinor Yatom T hT r := by
  ext a b
  simp only [detATMat, detATMinor, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.cases_succ]
  simp only [orderEmbOfFin_erase]

/-- Last-column expansion of `A_T(B)`. -/
public theorem detAT_eq_expansion (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    detAT Yatom B T hT
      = ∑ r : Fin (m + 2), (-1) ^ (r.val : ℕ)
        * B (T.orderEmbOfFin hT r)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) := by
  have hterm : ∀ r : Fin (m + 2),
      (-1) ^ ((r : ℕ)) * detATMat Yatom B T hT r 0
        * Matrix.det ((detATMat Yatom B T hT).submatrix
          r.succAbove Fin.succ)
      = (-1) ^ (r.val : ℕ) * B (T.orderEmbOfFin hT r)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) := by
    intro r
    have hm0 : detATMat Yatom B T hT r 0
        = B (T.orderEmbOfFin hT r) := by
      simp only [detATMat, Matrix.of_apply, Fin.cases_zero]
    have hdm : Matrix.det ((detATMat Yatom B T hT).submatrix
          r.succAbove Fin.succ)
        = detOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) := by
      rw [detAT_minor]
      rfl
    rw [hm0, hdm]
  simp only [detAT]
  rw [Matrix.det_succ_column_zero]
  exact Finset.sum_congr rfl (fun r _ => hterm r)

/-- Hulls of atom sets are compact. -/
public theorem hullOf_isCompact (U : Finset (Fin N)) :
    IsCompact (hullOf Yatom U) := by
  simp only [hullOf]
  apply Set.Finite.isCompact_convexHull
  have hfin : ((fun i => Yatom i) '' ↑U).Finite := by
    rw [← Finset.coe_image]
    exact Finset.finite_toSet _
  exact hfin

/-- Hulls of atom sets are measurable. -/
public theorem hullOf_measurableSet (U : Finset (Fin N)) :
    MeasurableSet (hullOf Yatom U) :=
  (hullOf_isCompact Yatom U).measurableSet

/-- Hulls of atom sets have finite volume. -/
public theorem hullOf_finite_measure (U : Finset (Fin N)) :
    volume (hullOf Yatom U) < ∞ :=
  (hullOf_isCompact Yatom U).measure_lt_top

/-- Hulls of atom sets are range-hulls of their enumerations. -/
public theorem hullOf_eq_range (U : Finset (Fin N)) (h : U.card = m + 1) :
    hullOf Yatom U = convexHull ℝ (Set.range
      (fun k => Yatom (U.orderEmbOfFin h k))) := by
  have himg : Set.range (fun k => Yatom (U.orderEmbOfFin h k))
      = (fun i => Yatom i) '' ↑U := by
    have hcomp : (fun k => Yatom (U.orderEmbOfFin h k))
        = Yatom ∘ U.orderEmbOfFin h := rfl
    rw [hcomp, Set.range_comp, Finset.range_orderEmbOfFin]
  simp only [hullOf, himg]

/-- Integrals of `1_U` are hull volumes. -/
public theorem integral_indOf (U : Finset (Fin N)) :
    ∫ x, indOf Yatom U x ∂volume
      = (volume (hullOf Yatom U)).toReal := by
  have h := integral_indicator_one
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (hullOf_measurableSet Yatom U)
  have hreal : Measure.real volume (hullOf Yatom U)
      = (volume (hullOf Yatom U)).toReal := rfl
  rw [hreal] at h
  simpa [indOf] using h

/-- `|D(U)| = m! vol(hull)`. -/
public theorem abs_detOf_eq_toReal (U : Finset (Fin N))
    (h : U.card = m + 1) :
    |detOf Yatom U h|
      = (m ! : ℝ) * (volume (hullOf Yatom U)).toReal := by
  have hsim := abs_simDet_eq_volume_convexHull
    (fun k => Yatom (U.orderEmbOfFin h k))
  rw [← hullOf_eq_range Yatom U h] at hsim
  have hreal := congrArg ENNReal.toReal hsim
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at hreal
  exact hreal

/-- `D(U) = m! ∫ S_U`. -/
public theorem detOf_eq_integral (U : Finset (Fin N))
    (h : U.card = m + 1) :
    detOf Yatom U h
      = (m ! : ℝ) * ∫ x, signedOf Yatom U h x ∂volume := by
  have hsign : detOf Yatom U h
      = Real.sign (detOf Yatom U h) * |detOf Yatom U h| := by
    rcases lt_trichotomy (detOf Yatom U h) 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, abs_of_neg hneg]; ring
    · rw [hzero, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos hpos, abs_of_pos hpos]; ring
  have hSint : ∫ x, signedOf Yatom U h x ∂volume
      = Real.sign (detOf Yatom U h)
        * ∫ x, indOf Yatom U x ∂volume := by
    simp only [signedOf]
    rw [integral_const_mul]
  rw [hsign, abs_detOf_eq_toReal Yatom U h, hSint, integral_indOf]
  ring

/-- `|D(U)| = m! ∫ 1_U`. -/
public theorem abs_detOf_eq_integral (U : Finset (Fin N))
    (h : U.card = m + 1) :
    |detOf Yatom U h|
      = (m ! : ℝ) * ∫ x, indOf Yatom U x ∂volume := by
  rw [abs_detOf_eq_toReal Yatom U h, integral_indOf]

/-- Indicators of atom hulls are integrable. -/
public theorem integrable_indOf (U : Finset (Fin N)) :
    Integrable (indOf Yatom U) volume := by
  have hfin : volume (hullOf Yatom U) ≠ ∞ :=
    ne_of_lt (hullOf_finite_measure Yatom U)
  have hInt : IntegrableOn (fun _ => (1 : ℝ)) (hullOf Yatom U) volume :=
    integrableOn_const hfin (by simp)
  have h := (integrable_indicator_iff (hullOf_measurableSet Yatom U)).mpr
    hInt
  exact h

/-- Signed indicators are integrable. -/
public theorem integrable_signedOf (U : Finset (Fin N))
    (h : U.card = m + 1) :
    Integrable (signedOf Yatom U h) volume :=
  (integrable_indOf Yatom U).const_mul _

/-- Summands of `s_T(B)` are integrable. -/
public theorem integrable_signedSumT_term (T : Finset (Fin N))
    (hT : T.card = m + 2) (r : Fin (m + 2)) :
    Integrable (fun x => (-1 : ℝ) ^ (r.val)
      * signedOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x
      * B (T.orderEmbOfFin hT r)) volume :=
  ((integrable_signedOf Yatom _ _).const_mul _).mul_const _

/-- `s_T(B)` is integrable. -/
public theorem integrable_signedSumT (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    Integrable (signedSumT Yatom T hT B) volume :=
  integrable_finsetSum _ (fun r _ => integrable_signedSumT_term _ _ T hT r)

/-- `A_T(B) = m! ∫ s_T(B)`. -/
public theorem detAT_eq_integral (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    detAT Yatom B T hT
      = (m ! : ℝ) * ∫ x, signedSumT Yatom T hT B x ∂volume := by
  have hper : ∀ r : Fin (m + 2),
      (-1 : ℝ) ^ (r.val) * B (T.orderEmbOfFin hT r)
        * detOf Yatom (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r))
      = (-1 : ℝ) ^ (r.val) * B (T.orderEmbOfFin hT r)
        * ((m ! : ℝ) * ∫ x, signedOf Yatom
          (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x ∂volume) := by
    intro r
    rw [detOf_eq_integral Yatom
      (T.erase (T.orderEmbOfFin hT r))
      (erase_card T hT _ (T.orderEmbOfFin_mem hT r))]
  have hinter : ∫ x, signedSumT Yatom T hT B x ∂volume
      = ∑ r : Fin (m + 2), ∫ x, ((-1 : ℝ) ^ (r.val)
        * signedOf Yatom (T.erase (T.orderEmbOfFin hT r))
            (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x
        * B (T.orderEmbOfFin hT r)) ∂volume :=
    integral_finsetSum _ (fun r _ => integrable_signedSumT_term _ _ T hT r)
  have hintR : (m ! : ℝ) * ∫ x, signedSumT Yatom T hT B x ∂volume
      = ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r.val)
        * B (T.orderEmbOfFin hT r)
        * ((m ! : ℝ) * ∫ x, signedOf Yatom
          (T.erase (T.orderEmbOfFin hT r))
          (erase_card T hT _ (T.orderEmbOfFin_mem hT r)) x ∂volume) := by
    rw [hinter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_mul_const, integral_const_mul]
    ring
  rw [detAT_eq_expansion Yatom B T hT, hintR]
  exact Finset.sum_congr rfl (fun r _ => hper r)

/-- `|A_T(B)| ≤ m! ∫ |s_T(B)|`. -/
public theorem abs_detAT_le (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    |detAT Yatom B T hT|
      ≤ (m ! : ℝ) * ∫ x, |signedSumT Yatom T hT B x| ∂volume := by
  have hnorm : ‖∫ x, signedSumT Yatom T hT B x ∂volume‖
      ≤ ∫ x, ‖signedSumT Yatom T hT B x‖ ∂volume :=
    norm_integral_le_integral_norm _
  rw [detAT_eq_integral Yatom B T hT]
  have hfact : (0 : ℝ) ≤ (m ! : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hfact]
  refine mul_le_mul_of_nonneg_left ?_ hfact
  simp only [Real.norm_eq_abs] at hnorm
  exact hnorm

/-- Totalized `A_T(B)` (`0` off the `(d+1)`-sets). -/
@[expose] public noncomputable def detAT' (T : Finset (Fin N)) : ℝ :=
  if hT : T.card = m + 2 then detAT Yatom B T hT else 0

/-- Totalized `D(U)` (`0` off the `d`-sets). -/
@[expose] public noncomputable def detOf' (U : Finset (Fin N)) : ℝ :=
  if h : U.card = m + 1 then detOf Yatom U h else 0

/-- `detAT'` unfolds on `(d+1)`-sets. -/
public theorem detAT'_eq (T : Finset (Fin N))
    (hT : T.card = m + 2) : detAT' Yatom B T = detAT Yatom B T hT := by
  simp only [detAT']
  exact dite_eq_left hT

/-- `detOf'` unfolds on `d`-sets. -/
public theorem detOf'_eq (U : Finset (Fin N))
    (h : U.card = m + 1) : detOf' Yatom U = detOf Yatom U h := by
  simp only [detOf']
  exact dite_eq_left h

/-- Lemma 4.1 (Weighted Bernoulli inequality). -/
public theorem weighted_bernoulli_inequality (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hbin : ∀ i, B i = 0 ∨ B i = 1) :
    ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom B T|
      ≤ pbar p B * (1 - pbar p B)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U| := by
  have hcardT : ∀ T ∈ Finset.powersetCard (m + 2)
      (Finset.univ : Finset (Fin N)), T.card = m + 2 :=
    fun T hT => (Finset.mem_powersetCard.mp hT).2
  have hcardU : ∀ U ∈ Finset.powersetCard (m + 1)
      (Finset.univ : Finset (Fin N)), U.card = m + 1 :=
    fun U hU => (Finset.mem_powersetCard.mp hU).2
  have hIntT : ∀ T ∈ Finset.powersetCard (m + 2) Finset.univ,
      Integrable
        (fun x => atomWeight p T * |signedSumT' Yatom B T x|) volume := by
    intro T hT
    have hTc := hcardT T hT
    have hfun : (fun x => atomWeight p T * |signedSumT' Yatom B T x|)
        = fun x => atomWeight p T
          * |signedSumT Yatom T hTc B x| := by
      funext x
      rw [signedSumT'_eq Yatom B T hTc x]
    rw [hfun]
    exact ((integrable_signedSumT Yatom B T hTc).abs.const_mul _)
  have hIntU : ∀ U ∈ Finset.powersetCard (m + 1) Finset.univ,
      Integrable
        (fun x => atomWeight p U * indOf Yatom U x) volume :=
    fun U _ => (integrable_indOf Yatom U).const_mul _
  have hstep1 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T * |detAT' Yatom B T|
        ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T
            * ((m ! : ℝ) * ∫ x, |signedSumT' Yatom B T x| ∂volume) := by
    apply Finset.sum_le_sum
    intro T hT
    have hTc := hcardT T hT
    have hseq : (fun x => |signedSumT' Yatom B T x|)
        = fun x => |signedSumT Yatom T hTc B x| := by
      funext x
      rw [signedSumT'_eq Yatom B T hTc x]
    rw [detAT'_eq Yatom B T hTc, hseq]
    exact mul_le_mul_of_nonneg_left (abs_detAT_le Yatom B T hTc)
      (atomWeight_nonneg p hpos T)
  have hstep2 : ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T
            * ((m ! : ℝ) * ∫ x, |signedSumT' Yatom B T x| ∂volume)
        = (m ! : ℝ) * ∫ x, (∑ T ∈ Finset.powersetCard (m + 2)
          Finset.univ, atomWeight p T * |signedSumT' Yatom B T x|)
          ∂volume := by
    have hinter : ∫ x, (∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
            atomWeight p T * |signedSumT' Yatom B T x|) ∂volume
          = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
            ∫ x, (atomWeight p T * |signedSumT' Yatom B T x|) ∂volume :=
      integral_finsetSum _ (fun T hT => hIntT T hT)
    rw [hinter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [integral_const_mul]
    ring
  have hstep3 : (m ! : ℝ) * ∫ x, (∑ T ∈ Finset.powersetCard (m + 2)
            Finset.univ, atomWeight p T * |signedSumT' Yatom B T x|)
          ∂volume
        ≤ (m ! : ℝ) * ∫ x, (pbar p B * (1 - pbar p B)
            * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
              atomWeight p U * indOf Yatom U x) ∂volume := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply integral_mono_ae _ _ _
    · exact integrable_finsetSum _ (fun T hT => hIntT T hT)
    · have hsumU : Integrable
          (fun x => ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * indOf Yatom U x) volume :=
        integrable_finsetSum _ (fun U hU => hIntU U hU)
      exact hsumU.const_mul _
    · exact local_bernoulli_estimate p Yatom B hpos hsum hbin
  have hstep4 : (m ! : ℝ) * ∫ x, (pbar p B * (1 - pbar p B)
            * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
              atomWeight p U * indOf Yatom U x) ∂volume
        = pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * |detOf' Yatom U| := by
    have hinterU : ∫ x, (∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * indOf Yatom U x) ∂volume
          = ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            ∫ x, (atomWeight p U * indOf Yatom U x) ∂volume :=
      integral_finsetSum _ (fun U hU => hIntU U hU)
    have hperU : ∀ U ∈ Finset.powersetCard (m + 1) Finset.univ,
        (m ! : ℝ) * (pbar p B * (1 - pbar p B))
          * ∫ x, (atomWeight p U * indOf Yatom U x) ∂volume
        = pbar p B * (1 - pbar p B)
          * (atomWeight p U * |detOf' Yatom U|) := by
      intro U hU
      have hUc := hcardU U hU
      rw [detOf'_eq Yatom U hUc, abs_detOf_eq_integral Yatom U hUc,
        integral_const_mul]
      ring
    rw [integral_const_mul, hinterU]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    rw [← hperU U hU]
    ring
  calc ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T * |detAT' Yatom B T|
      ≤ ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
          atomWeight p T
            * ((m ! : ℝ) * ∫ x, |signedSumT' Yatom B T x| ∂volume) :=
        hstep1
    _ = (m ! : ℝ) * ∫ x, (∑ T ∈ Finset.powersetCard (m + 2)
          Finset.univ, atomWeight p T * |signedSumT' Yatom B T x|)
          ∂volume := hstep2
    _ ≤ (m ! : ℝ) * ∫ x, (pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * indOf Yatom U x) ∂volume := hstep3
    _ = pbar p B * (1 - pbar p B)
        * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
          atomWeight p U * |detOf' Yatom U| := hstep4

end HypercubeInequality
