module

/-
# Signed simplex cancellation (HI-COCYCLE, HI-COCYCLE-D1)

For `Y : Fin (m+2) → EuclideanSpace ℝ (Fin m)` (paper: `d = m+1`,
`Y_0, …, Y_d ∈ ℝ^{d-1}`), the omission data: `T_r = conv` of the tuple
with index `r` deleted, `D_r` the deletion determinant, and signed
coefficients `σ_r = (-1)^r sgn(D_r)`.

Lemma 2.1 (Alternating deletion identity): `∑ σ_r 1_{T_r} = 0` a.e.
The `d = 1` case (`m = 0`) is proved here; both omission simplices are
the single point of `ℝ^0` and the two signed terms are `1` and `-1`.
The general case (affine-dependence line argument + null set) is the
hardest analysis lemma and is staged separately.
-/

public import Mathlib
public import Section_1_Introduction.Core
public import Section_3_LocalEstimate.SimplexVolume

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

/-- Deletion tuple: omit index `r` via `Fin.succAbove`. -/
@[expose] public noncomputable def cocycleDel {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) :
    Fin (m + 1) → EuclideanSpace ℝ (Fin m) :=
  fun i => Y (r.succAbove i)

/-- Omission determinant `D_r`. -/
@[expose] public noncomputable def cocycleDet {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) : ℝ :=
  simDet (cocycleDel Y r)

/-- Signed coefficient `σ_r = (-1)^r sgn(D_r)`. -/
@[expose] public noncomputable def cocycleSigma {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) : ℝ :=
  (-1) ^ (r.val) * Real.sign (cocycleDet Y r)

/-- Omission simplex `T_r`: convex hull of the deletion tuple. -/
@[expose] public noncomputable def cocycleSimplex {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  convexHull ℝ (Set.range (cocycleDel Y r))

/-- The `0`-dimensional determinant is `1`. -/
public theorem simDet_dim0 (v : Fin 1 → EuclideanSpace ℝ (Fin 0)) :
    simDet v = 1 := by
  have hM : (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => v r j) c)
      : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
    ext r c
    rw [Fin.eq_zero r, Fin.eq_zero c]
    simp
  simp only [simDet, hM, Matrix.det_one]

/-- `ℝ^0` is a subsingleton (all points equal). -/
public theorem euclideanSpace_dim0_subsingleton
    (x y : EuclideanSpace ℝ (Fin 0)) : x = y := by
  have hfg : (WithLp.ofLp x : Fin 0 → ℝ) = WithLp.ofLp y := by
    funext i
    exact (Nat.not_lt_zero _ i.isLt).elim
  calc x = WithLp.toLp 2 (WithLp.ofLp x) := (WithLp.toLp_ofLp 2 x).symm
    _ = WithLp.toLp 2 (WithLp.ofLp y) := by rw [hfg]
    _ = y := WithLp.toLp_ofLp 2 y

/-- In dimension zero, every omission simplex is the whole space. -/
public theorem cocycleSimplex_dim0 (Y : Fin 2 → EuclideanSpace ℝ (Fin 0))
    (r : Fin 2) : cocycleSimplex Y r = Set.univ := by
  have hrange : Set.range (cocycleDel Y r) = {cocycleDel Y r 0} := by
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rw [Fin.eq_zero i]
    · rintro rfl
      exact ⟨0, rfl⟩
  simp only [cocycleSimplex, hrange, convexHull_singleton]
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact euclideanSpace_dim0_subsingleton z _

/-- HI-COCYCLE-D1: the `d = 1` cocycle identity (holds everywhere). -/
public theorem cocycle_dim1 (Y : Fin 2 → EuclideanSpace ℝ (Fin 0)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 0))),
      ∑ r, cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0 := by
  apply Filter.Eventually.of_forall
  intro x
  rw [Fin.sum_univ_two]
  have hdet : ∀ r : Fin 2, cocycleDet Y r = 1 := fun r => simDet_dim0 _
  have h0 : cocycleSigma Y 0 = 1 := by
    simp [cocycleSigma, hdet, Real.sign_one]
  have h1 : cocycleSigma Y 1 = -1 := by
    simp [cocycleSigma, hdet, Real.sign_one]
  have hind : ∀ r : Fin 2,
      (cocycleSimplex Y r).indicator (1 : EuclideanSpace ℝ (Fin 0) → ℝ) x = 1 := by
    intro r
    rw [cocycleSimplex_dim0 Y r]
    simp
  rw [h0, h1, hind 0, hind 1]
  norm_num

/-- Affine-dependence coefficients `λ_r = (-1)^r D_r`. -/
@[expose] public noncomputable def cocycleLambda {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) : ℝ :=
  (-1) ^ (r : ℕ) * cocycleDet Y r

/-- Shared minor block: the `D`-matrix rows. -/
@[expose] public noncomputable def cocycleBlock {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2))
    (j : Fin (m + 1)) : ℝ :=
  Fin.cases (1 : ℝ) (fun t => Y r t) j

/-- Repeated-column matrix with leading column `f` (for cofactor expansion). -/
@[expose] public noncomputable def cocycleMat {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (f : Fin (m + 2) → ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of fun r c => Fin.cases (f r) (fun j => cocycleBlock Y r j) c

/-- The column-0 minor is the `D`-matrix of the deletion tuple. -/
public theorem cocycleMat_minor {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (f : Fin (m + 2) → ℝ)
    (r : Fin (m + 2)) :
    (cocycleMat Y f).submatrix r.succAbove Fin.succ
      = Matrix.of (fun i j => Fin.cases (1 : ℝ)
          (fun t => cocycleDel Y r i t) j) := by
  ext i j
  simp only [cocycleMat, cocycleBlock, Matrix.of_apply,
    Matrix.submatrix_apply, Fin.cases_succ, cocycleDel]

/-- Weighted cofactor expansion: a vanishing repeated-column determinant
gives `∑ (-1)^r f_r D_r = 0`. -/
public theorem cocycle_weighted_sum {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (f : Fin (m + 2) → ℝ)
    (hdet0 : Matrix.det (cocycleMat Y f) = 0) :
    ∑ r : Fin (m + 2), (-1) ^ ((r : ℕ)) * f r * cocycleDet Y r = 0 := by
  have hexpand := Matrix.det_succ_column_zero (cocycleMat Y f)
  rw [hdet0] at hexpand
  have hterm : ∀ r : Fin (m + 2),
      (-1) ^ ((r : ℕ)) * cocycleMat Y f r 0
        * Matrix.det ((cocycleMat Y f).submatrix r.succAbove Fin.succ)
      = (-1) ^ ((r : ℕ)) * f r * cocycleDet Y r := by
    intro r
    have hm0 : cocycleMat Y f r 0 = f r := by simp [cocycleMat]
    have hdm : Matrix.det ((cocycleMat Y f).submatrix r.succAbove Fin.succ)
        = cocycleDet Y r := by
      rw [cocycleMat_minor]
      rfl
    rw [hm0, hdm]
  calc ∑ r : Fin (m + 2), (-1) ^ ((r : ℕ)) * f r * cocycleDet Y r
        = ∑ r : Fin (m + 2), ((-1) ^ ((r : ℕ)) * cocycleMat Y f r 0
          * Matrix.det ((cocycleMat Y f).submatrix r.succAbove Fin.succ)) := by
          apply Finset.sum_congr rfl
          intro r _
          exact (hterm r).symm
      _ = Matrix.det (cocycleMat Y f) :=
          (Matrix.det_succ_column_zero (cocycleMat Y f)).symm
      _ = 0 := hdet0

/-- The double-ones matrix has determinant zero (columns `0`, `1` agree). -/
public theorem cocycleMat1_det {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    Matrix.det (cocycleMat Y (fun _ => 1)) = 0 :=
  Matrix.det_zero_of_column_eq (Ne.symm (Fin.succ_ne_zero 0)) (fun r => by
    simp only [cocycleMat, cocycleBlock, Matrix.of_apply, Fin.cases_zero,
      Fin.cases_succ])

/-- The coordinate matrix has determinant zero (columns `0`, `t+2` agree). -/
public theorem cocycleMat2_det {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (t : Fin m) :
    Matrix.det (cocycleMat Y (fun r => Y r t)) = 0 := by
  apply Matrix.det_zero_of_column_eq
    (Ne.symm (Fin.succ_ne_zero (Fin.succ t)))
  intro r
  simp only [cocycleMat, cocycleBlock, Matrix.of_apply, Fin.cases_zero,
    Fin.cases_succ]

/-- First dependency identity: `∑ λ = 0`. -/
public theorem cocycleLambda_sum {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    ∑ r, cocycleLambda Y r = 0 := by
  have h := cocycle_weighted_sum Y (fun _ => 1) (cocycleMat1_det Y)
  have heq : (∑ r, cocycleLambda Y r)
      = ∑ r : Fin (m + 2), (-1) ^ ((r : ℕ)) * (fun _ : Fin (m + 2) => 1) r
        * cocycleDet Y r := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [cocycleLambda]
    ring
  rw [heq]
  exact h

/-- Per-coordinate dependency identity. -/
public theorem cocycleLambda_coord {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (t : Fin m) :
    ∑ r, cocycleLambda Y r * Y r t = 0 := by
  have h := cocycle_weighted_sum Y (fun r => Y r t) (cocycleMat2_det Y t)
  have heq : (∑ r, cocycleLambda Y r * Y r t)
      = ∑ r : Fin (m + 2), (-1) ^ ((r : ℕ)) * (fun r => Y r t) r * cocycleDet Y r := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [cocycleLambda]
    ring
  rw [heq]
  exact h

/-- Second dependency identity: `∑ λ_r Y_r = 0`. -/
public theorem cocycleLambda_orth {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    ∑ r, cocycleLambda Y r • Y r = 0 := by
  apply PiLp.ext
  intro t
  have hproj : ∀ x : EuclideanSpace ℝ (Fin m),
      EuclideanSpace.projₗ t x = x t := fun x => rfl
  simp only [← hproj, _root_.map_sum, map_smul, map_zero]
  simp only [hproj, smul_eq_mul]
  exact cocycleLambda_coord Y t

/-- Padded double-deletion tuple: single deletion with the `i₀`-entry
overwritten by the `j₀`-entry (a repeated value when `j₀ ≠ i₀`). -/
@[expose] public noncomputable def cocyclePadded {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r _r' : Fin (m + 2))
    (i₀ j₀ : Fin (m + 1)) : Fin (m + 1) → EuclideanSpace ℝ (Fin m) :=
  Function.update (cocycleDel Y r) i₀ (cocycleDel Y r j₀)

/-- The padded tuple covers all double-deletion values. -/
public theorem cocyclePadded_mem_range {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r r' : Fin (m + 2))
    (i₀ j₀ : Fin (m + 1)) (hi₀ : r.succAbove i₀ = r')
    (s : Fin (m + 2)) (hsr : s ≠ r) (hsr' : s ≠ r') :
    Y s ∈ Set.range (cocyclePadded Y r r' i₀ j₀) := by
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hsr
  have hii₀ : i ≠ i₀ := by
    intro hii
    apply hsr'
    rw [← hi, hii, hi₀]
  refine ⟨i, ?_⟩
  have h1 : cocyclePadded Y r r' i₀ j₀ i = cocycleDel Y r i := by
    simp [cocyclePadded, hii₀]
  rw [h1]
  simp only [cocycleDel]
  rw [hi]

/-- The padded tuple has determinant zero (repeated value). -/
public theorem simDet_cocyclePadded {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r r' : Fin (m + 2))
    (i₀ j₀ : Fin (m + 1)) (hj₀ : j₀ ≠ i₀) :
    simDet (cocyclePadded Y r r' i₀ j₀) = 0 := by
  have hrep : cocyclePadded Y r r' i₀ j₀ i₀
      = cocyclePadded Y r r' i₀ j₀ j₀ := by
    simp [cocyclePadded, hj₀]
  have hrows : (Matrix.of (fun a c => Fin.cases (1 : ℝ)
      (fun t => cocyclePadded Y r r' i₀ j₀ a t) c)
      : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) i₀
      = (Matrix.of (fun a c => Fin.cases (1 : ℝ)
        (fun t => cocyclePadded Y r r' i₀ j₀ a t) c)
        : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) j₀ := by
    funext c
    simp only [Matrix.of_apply]
    rw [hrep]
  exact Matrix.det_zero_of_row_eq hj₀ hrows.symm

/-- Each null-set piece has volume zero (via HI-SIMPVOL). -/
public theorem volume_convexHull_padded {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r r' : Fin (m + 2))
    (i₀ j₀ : Fin (m + 1)) (hj₀ : j₀ ≠ i₀) :
    volume (convexHull ℝ
      (Set.range (cocyclePadded Y r r' i₀ j₀))) = 0 := by
  have hsim := abs_simDet_eq_volume_convexHull (cocyclePadded Y r r' i₀ j₀)
  rw [simDet_cocyclePadded Y r r' i₀ j₀ hj₀] at hsim
  simp only [abs_zero, ENNReal.ofReal_zero] at hsim
  have hm0 : (((m ! : ℕ)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  exact (mul_eq_zero.mp hsim.symm).resolve_left hm0

/-- The exceptional null set: all padded double-deletion hulls. -/
@[expose] public noncomputable def cocycleNull {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  ⋃ r ∈ (Set.univ : Set (Fin (m + 2))),
  ⋃ r' ∈ (Set.univ : Set (Fin (m + 2))),
  ⋃ i₀ ∈ (Set.univ : Set (Fin (m + 1))),
  ⋃ j₀ ∈ {j₀ : Fin (m + 1) | j₀ ≠ i₀},
    convexHull ℝ (Set.range (cocyclePadded Y r r' i₀ j₀))

/-- The exceptional set has volume zero. -/
public theorem volume_cocycleNull {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    volume (cocycleNull Y) = 0 := by
  simp only [cocycleNull]
  rw [measure_biUnion_null_iff Set.countable_univ]
  intro r hr
  rw [measure_biUnion_null_iff Set.countable_univ]
  intro r' hr'
  rw [measure_biUnion_null_iff Set.countable_univ]
  intro i₀ hi₀
  rw [measure_biUnion_null_iff
    (Set.Countable.mono (Set.subset_univ _) Set.countable_univ)]
  intro j₀ hj₀
  simp only [Set.mem_ofPred_eq] at hj₀
  exact volume_convexHull_padded Y r r' i₀ j₀ hj₀

/-- Membership in a tuple convex hull gives explicit weights. -/
public theorem mem_convexHull_range_tuple {k : ℕ}
    (w : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) (hx : x ∈ convexHull ℝ (Set.range w)) :
    ∃ W : Fin (k + 1) → ℝ, (∀ i, 0 ≤ W i) ∧ ∑ i, W i = 1
      ∧ ∑ i, W i • w i = x := by
  rw [convexHull_range_eq_image w] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hu' : (∀ j, 0 ≤ u j) ∧ ∑ j, u j ≤ 1 := hu
  obtain ⟨hupos, husum⟩ := hu'
  set W : Fin (k + 1) → ℝ := Fin.cases (1 - ∑ j, u j) u with hW
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp only [hW, Fin.cases_zero]
      linarith
    · intro j
      simp only [hW, Fin.cases_succ]
      exact hupos j
  · have hS : ∑ i : Fin k, W i.succ = ∑ j, u j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hW, Fin.cases_succ]
    rw [Fin.sum_univ_succ, hS]
    simp only [hW, Fin.cases_zero]
    ring
  · have hsplit : ∑ i, W i • w i
        = W 0 • w 0 + ∑ j : Fin k, W j.succ • w j.succ :=
      Fin.sum_univ_succ (fun i => W i • w i)
    rw [hsplit]
    simp only [hW, Fin.cases_zero, Fin.cases_succ]
    show (1 - ∑ j, u j) • w 0 + ∑ j, u j • w j.succ = simAffine w u
    show (1 - ∑ j, u j) • w 0 + ∑ j, u j • w j.succ
        = w 0 + simLin w u
    rw [simLin_apply]
    have hexpand : ∑ j, u j • (w j.succ - w 0)
        = (∑ j, u j • w j.succ) - (∑ j, u j) • w 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [hexpand]
    have hfin : (1 - ∑ j, u j) • w 0 + ∑ j, u j • w j.succ
        = w 0 + ((∑ j, u j • w j.succ) - (∑ j, u j) • w 0) := by
      rw [sub_smul, one_smul]
      abel
    exact hfin

/-- A convex combination lies in the tuple convex hull. -/
public theorem mem_convexHull_range_tuple_of_combo {k : ℕ}
    (w : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
    (W : Fin (k + 1) → ℝ) (x : EuclideanSpace ℝ (Fin k))
    (hpos : ∀ i, 0 ≤ W i) (hsum : ∑ i, W i = 1)
    (hcomb : ∑ i, W i • w i = x) :
    x ∈ convexHull ℝ (Set.range w) :=
  mem_convexHull_of_exists_fintype W w hpos hsum
    (fun i => Set.mem_range_self i) hcomb

/-- Membership in an omission simplex iff a full representation with zero
at the omitted index. -/
public theorem mem_cocycleSimplex_iff {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2))
    (x : EuclideanSpace ℝ (Fin m)) :
    x ∈ cocycleSimplex Y r ↔ ∃ β : Fin (m + 2) → ℝ, (∀ s, 0 ≤ β s)
      ∧ ∑ s, β s = 1 ∧ (∑ s, β s • Y s) = x ∧ β r = 0 := by
  constructor
  · intro hx
    have hx' : x ∈ convexHull ℝ (Set.range (cocycleDel Y r)) := hx
    obtain ⟨W, hpos, hsum, hcomb⟩ :=
      mem_convexHull_range_tuple (cocycleDel Y r) x hx'
    set e := finSuccAboveEquiv r with he
    set β : Fin (m + 2) → ℝ := fun s => dite (s = r) (fun _ => (0 : ℝ))
      (fun h => W (e.symm ⟨s, h⟩)) with hβ
    have hr0 : β r = 0 := by simp [hβ]
    have hterm : ∀ i : Fin (m + 1), β (r.succAbove i) = W i := by
      intro i
      have hne : r.succAbove i ≠ r := r.succAbove_ne i
      simp only [hβ, dite_eq_right hne]
      congr 1
      have heq : (⟨r.succAbove i, hne⟩ : {x : Fin (m + 2) // x ≠ r})
          = e i := by
        rw [he]
        exact Subtype.ext rfl
      rw [heq]
      exact Equiv.symm_apply_apply e i
    refine ⟨β, ?_, ?_, ?_, hr0⟩
    · intro s
      by_cases hs : s = r
      · simp [hβ, hs]
      · simp only [hβ, dite_eq_right hs]
        exact hpos _
    · have hsplit := Fin.sum_univ_succAbove (fun s => β s) r
      rw [hsplit, hr0, zero_add]
      rw [show (∑ i, β (r.succAbove i)) = ∑ i, W i from
        Finset.sum_congr rfl (fun i _ => hterm i)]
      exact hsum
    · have hsplit := Fin.sum_univ_succAbove (fun s => β s • Y s) r
      rw [hsplit, hr0]
      simp only [zero_smul, zero_add]
      have hterm2 : ∀ i : Fin (m + 1),
          β (r.succAbove i) • Y (r.succAbove i)
            = W i • cocycleDel Y r i := by
        intro i
        simp [hterm i, cocycleDel]
      rw [show (∑ i, β (r.succAbove i) • Y (r.succAbove i))
          = ∑ i, W i • cocycleDel Y r i from
        Finset.sum_congr rfl (fun i _ => hterm2 i)]
      exact hcomb
  · rintro ⟨β, hpos, hsum, hcomb, hr0⟩
    refine mem_convexHull_range_tuple_of_combo (cocycleDel Y r)
      (fun i => β (r.succAbove i)) x (fun i => hpos _) ?_ ?_
    · show ∑ i, β (r.succAbove i) = 1
      have hsplit := Fin.sum_univ_succAbove β r
      rw [hsum, hr0, zero_add] at hsplit
      exact hsplit.symm
    · show ∑ i, β (r.succAbove i) • cocycleDel Y r i = x
      have hsplit := Fin.sum_univ_succAbove (fun s => β s • Y s) r
      rw [hcomb, hr0] at hsplit
      simp only [zero_smul, zero_add] at hsplit
      show ∑ i, β (r.succAbove i) • Y (r.succAbove i) = x
      exact hsplit.symm

/-- A nonvanishing determinant forces trivial affine dependencies. -/
public theorem affineDep_trivial_of_simDet_ne_zero {k : ℕ}
    (w : Fin (k + 1) → EuclideanSpace ℝ (Fin k))
    (hdet : simDet w ≠ 0)
    (c : Fin (k + 1) → ℝ) (hsum : ∑ i, c i = 0)
    (hcomb : ∑ i, c i • w i = 0) : c = 0 := by
  set A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => w r j) c) with hA
  have hdetA : Matrix.det A ≠ 0 := by
    rw [hA]
    exact hdet
  have hcoord : ∀ t : Fin k, ∑ i, c i * w i t = 0 := by
    intro t
    have hproj : ∀ x : EuclideanSpace ℝ (Fin k),
        EuclideanSpace.projₗ t x = x t := fun x => rfl
    have h0 := congrArg (EuclideanSpace.projₗ t) hcomb
    simp only [_root_.map_sum, map_smul, map_zero] at h0
    simp only [hproj, smul_eq_mul] at h0
    exact h0
  have hmul : Matrix.mulVec (Matrix.transpose A) c = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.zero_apply]
    refine Fin.cases ?_ ?_ j
    · simp only [hA, Matrix.of_apply, Fin.cases_zero, one_mul]
      exact hsum
    · intro t
      simp only [hA, Matrix.of_apply, Fin.cases_succ]
      have hcomm : (∑ x, w x t * c x) = ∑ x, c x * w x t :=
        Finset.sum_congr rfl (fun x _ => mul_comm _ _)
      rw [hcomm]
      exact hcoord t
  have hunit : IsUnit (Matrix.transpose A) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdetA
  have hinj : Function.Injective (Matrix.mulVec (Matrix.transpose A)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  apply hinj
  rw [hmul, Matrix.mulVec_zero]

/-- Full affine dependencies are multiples of `λ` (given `λ r₀ ≠ 0`). -/
public theorem affineDep_eq_smul_lambda {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r₀ : Fin (m + 2))
    (hlam : cocycleLambda Y r₀ ≠ 0)
    (c : Fin (m + 2) → ℝ) (hsum : ∑ s, c s = 0)
    (hcomb : ∑ s, c s • Y s = 0) :
    ∃ t : ℝ, c = fun s => t * cocycleLambda Y s := by
  refine ⟨c r₀ / cocycleLambda Y r₀, ?_⟩
  set t : ℝ := c r₀ / cocycleLambda Y r₀ with ht
  set c' : Fin (m + 2) → ℝ := fun s => c s - t * cocycleLambda Y s with hc'
  have hsum' : ∑ s, c' s = 0 := by
    simp only [hc', Finset.sum_sub_distrib, ← Finset.mul_sum,
      cocycleLambda_sum, mul_zero, hsum, sub_zero]
  have hcomb' : ∑ s, c' s • Y s = 0 := by
    simp only [hc', sub_smul, Finset.sum_sub_distrib, mul_smul,
      ← Finset.smul_sum, cocycleLambda_orth, smul_zero, hcomb, sub_zero]
  have hr0' : c' r₀ = 0 := by
    have hdiv : (c r₀ / cocycleLambda Y r₀) * cocycleLambda Y r₀ = c r₀ :=
      div_mul_cancel₀ _ hlam
    simp only [hc', ht]
    rw [hdiv, sub_self]
  have hW : ∀ i : Fin (m + 1), c' (r₀.succAbove i) = 0 := by
    have hWsum : ∑ i, c' (r₀.succAbove i) = 0 := by
      have hsplit := Fin.sum_univ_succAbove c' r₀
      rw [hsum', hr0', zero_add] at hsplit
      exact hsplit.symm
    have hWcomb : ∑ i, c' (r₀.succAbove i) • cocycleDel Y r₀ i = 0 := by
      have hsplit := Fin.sum_univ_succAbove (fun s => c' s • Y s) r₀
      rw [hcomb'] at hsplit
      rw [hr0'] at hsplit
      simp only [zero_smul, zero_add] at hsplit
      have heq : (∑ i, c' (r₀.succAbove i) • cocycleDel Y r₀ i)
          = ∑ i, c' (r₀.succAbove i) • Y (r₀.succAbove i) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      rw [heq]
      exact hsplit.symm
    have hD : cocycleDet Y r₀ ≠ 0 := by
      have hlam' : cocycleLambda Y r₀ ≠ 0 := hlam
      simp only [cocycleLambda] at hlam'
      exact (mul_ne_zero_iff.mp hlam').2
    have hdet0 : simDet (cocycleDel Y r₀) ≠ 0 := hD
    have hW0 : (fun i => c' (r₀.succAbove i)) = 0 :=
      affineDep_trivial_of_simDet_ne_zero (cocycleDel Y r₀) hdet0 _ hWsum
        hWcomb
    intro i
    exact congrFun hW0 i
  have hc's : ∀ s, c' s = 0 := by
    intro s
    by_cases hs : s = r₀
    · rw [hs]
      exact hr0'
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hs
      rw [← hi]
      exact hW i
  funext s
  have h0 : c s - t * cocycleLambda Y s = 0 := by
    simpa [hc'] using hc's s
  exact sub_eq_zero.mp h0

/-- Affine representations of a point form a line in the `λ` direction. -/
public theorem affineRep_line {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r₀ : Fin (m + 2))
    (hlam : cocycleLambda Y r₀ ≠ 0)
    (x : EuclideanSpace ℝ (Fin m))
    (β β0 : Fin (m + 2) → ℝ)
    (hsum : ∑ s, β s = 1) (hcomb : ∑ s, β s • Y s = x)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x) :
    ∃ t : ℝ, β = fun s => β0 s + t * cocycleLambda Y s := by
  have hsumc : ∑ s, (β s - β0 s) = 0 := by
    simp only [Finset.sum_sub_distrib, hsum, hsum0, sub_self]
  have hcombc : ∑ s, (β s - β0 s) • Y s = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hcomb, hcomb0, sub_self]
  obtain ⟨t, ht⟩ := affineDep_eq_smul_lambda Y r₀ hlam
    (fun s => β s - β0 s) hsumc hcombc
  refine ⟨t, ?_⟩
  funext s
  have hs : β s - β0 s = t * cocycleLambda Y s := congrFun ht s
  show β s = β0 s + t * cocycleLambda Y s
  rw [← hs]
  ring

/-- Both `λ` sign classes are nonempty (given `λ ≠ 0`). -/
public theorem cocycleLambda_sign_classes {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (hne : ∃ r₀, cocycleLambda Y r₀ ≠ 0) :
    (∃ r, 0 < cocycleLambda Y r) ∧ (∃ r, cocycleLambda Y r < 0) := by
  obtain ⟨r₀, hr₀⟩ := hne
  have hsum := cocycleLambda_sum Y
  constructor
  · by_contra hnone
    push Not at hnone
    have hneg : cocycleLambda Y r₀ < 0 :=
      lt_of_le_of_ne' (hnone r₀) (Ne.symm hr₀)
    have hpos : 0 < ∑ r, -cocycleLambda Y r := by
      apply Finset.sum_pos'
      · intro r _
        exact neg_nonneg.mpr (hnone r)
      · exact ⟨r₀, Finset.mem_univ r₀, neg_pos.mpr hneg⟩
    have hsum0 : ∑ r, -cocycleLambda Y r = 0 := by
      rw [Finset.sum_neg_distrib, hsum, neg_zero]
    rw [hsum0] at hpos
    exact lt_irrefl 0 hpos
  · by_contra hnone
    push Not at hnone
    have hpos' : 0 < cocycleLambda Y r₀ :=
      lt_of_le_of_ne' (hnone r₀) hr₀
    have hpos : 0 < ∑ r, cocycleLambda Y r := by
      apply Finset.sum_pos'
      · intro r _
        exact hnone r
      · exact ⟨r₀, Finset.mem_univ r₀, hpos'⟩
    rw [hsum] at hpos
    exact lt_irrefl 0 hpos

/-- Point on the representation line at parameter `t`. -/
@[expose] public noncomputable def cocycleBeta {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (t : ℝ) : Fin (m + 2) → ℝ :=
  fun s => β0 s + t * cocycleLambda Y s

/-- Parameter where coordinate `r` vanishes. -/
@[expose] public noncomputable def cocycleT {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (r : Fin (m + 2)) : ℝ :=
  -β0 r / cocycleLambda Y r

/-- Positive `λ` indices. -/
@[expose] public noncomputable def cocyclePos {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) : Finset (Fin (m + 2)) :=
  Finset.univ.filter (fun r => 0 < cocycleLambda Y r)

/-- Negative `λ` indices. -/
@[expose] public noncomputable def cocycleNeg {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) : Finset (Fin (m + 2)) :=
  Finset.univ.filter (fun r => cocycleLambda Y r < 0)

/-- Left feasibility endpoint. -/
@[expose] public noncomputable def cocycleTmin {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hP : (cocyclePos Y).Nonempty) : ℝ :=
  ((cocyclePos Y).image (cocycleT Y β0)).max' (hP.image _)

/-- Right feasibility endpoint. -/
@[expose] public noncomputable def cocycleTmax {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hN : (cocycleNeg Y).Nonempty) : ℝ :=
  ((cocycleNeg Y).image (cocycleT Y β0)).min' (hN.image _)

/-- Vanishing characterization of the `t`-value. -/
public theorem cocycleT_eq {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (r : Fin (m + 2)) (t : ℝ)
    (hlam : cocycleLambda Y r ≠ 0) :
    β0 r + t * cocycleLambda Y r = 0 ↔ t = cocycleT Y β0 r := by
  simp only [cocycleT]
  constructor
  · intro h
    have h' : t * cocycleLambda Y r = -β0 r := by linarith
    exact (eq_div_iff hlam).mpr h'
  · intro h
    rw [h]
    have hdiv : (-β0 r / cocycleLambda Y r) * cocycleLambda Y r
        = -β0 r := div_mul_cancel₀ _ hlam
    linarith [hdiv]

/-- Line points sum to one. -/
public theorem cocycleBeta_sum {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hsum0 : ∑ s, β0 s = 1) (t : ℝ) :
    ∑ s, cocycleBeta Y β0 t s = 1 := by
  simp only [cocycleBeta, Finset.sum_add_distrib, ← Finset.mul_sum,
    cocycleLambda_sum, mul_zero, hsum0, add_zero]

/-- Line points represent the same `x`. -/
public theorem cocycleBeta_comb {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hcomb0 : ∑ s, β0 s • Y s = x) (t : ℝ) :
    ∑ s, cocycleBeta Y β0 t s • Y s = x := by
  simp only [cocycleBeta, add_smul, Finset.sum_add_distrib, mul_smul,
    ← Finset.smul_sum, cocycleLambda_orth, smul_zero, hcomb0, add_zero]

/-- Omission membership iff the vanishing point is nonnegative. -/
public theorem mem_cocycleSimplex_iff_beta {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r₀ : Fin (m + 2))
    (hlam0 : cocycleLambda Y r₀ ≠ 0)
    (x : EuclideanSpace ℝ (Fin m)) (β0 : Fin (m + 2) → ℝ)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x)
    (r : Fin (m + 2)) (hlam : cocycleLambda Y r ≠ 0) :
    x ∈ cocycleSimplex Y r
      ↔ ∀ s, 0 ≤ cocycleBeta Y β0 (cocycleT Y β0 r) s := by
  rw [mem_cocycleSimplex_iff]
  constructor
  · rintro ⟨β, hpos, hsum, hcomb, hr0⟩
    obtain ⟨t, ht⟩ := affineRep_line Y r₀ hlam0 x β β0 hsum hcomb
      hsum0 hcomb0
    have htr : t = cocycleT Y β0 r := by
      have h0 : β0 r + t * cocycleLambda Y r = 0 := by
        calc β0 r + t * cocycleLambda Y r = β r := (congrFun ht r).symm
          _ = 0 := hr0
      exact (cocycleT_eq Y β0 r t hlam).mp h0
    have hβ : β = cocycleBeta Y β0 (cocycleT Y β0 r) := by
      rw [htr] at ht
      exact ht
    intro s
    rw [← hβ]
    exact hpos s
  · intro hpos
    refine ⟨cocycleBeta Y β0 (cocycleT Y β0 r), hpos, ?_, ?_, ?_⟩
    · exact cocycleBeta_sum Y β0 hsum0 _
    · exact cocycleBeta_comb Y β0 x hcomb0 _
    · show cocycleBeta Y β0 (cocycleT Y β0 r) r = 0
      have h0 : β0 r + cocycleT Y β0 r * cocycleLambda Y r = 0 :=
        (cocycleT_eq Y β0 r _ hlam).mpr rfl
      simpa [cocycleBeta] using h0

/-- The left endpoint is attained. -/
public theorem cocycleTmin_attains {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hP : (cocyclePos Y).Nonempty) :
    ∃ r ∈ cocyclePos Y, cocycleT Y β0 r = cocycleTmin Y β0 hP := by
  have hmem := Finset.max'_mem ((cocyclePos Y).image (cocycleT Y β0))
    (hP.image _)
  rw [Finset.mem_image] at hmem
  obtain ⟨r, hr, hrT⟩ := hmem
  exact ⟨r, hr, hrT⟩

/-- The right endpoint is attained. -/
public theorem cocycleTmax_attains {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hN : (cocycleNeg Y).Nonempty) :
    ∃ r ∈ cocycleNeg Y, cocycleT Y β0 r = cocycleTmax Y β0 hN := by
  have hmem := Finset.min'_mem ((cocycleNeg Y).image (cocycleT Y β0))
    (hN.image _)
  rw [Finset.mem_image] at hmem
  obtain ⟨r, hr, hrT⟩ := hmem
  exact ⟨r, hr, hrT⟩

/-- Positive `t`-values lie below the left endpoint. -/
public theorem cocycleT_le_Tmin {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hP : (cocyclePos Y).Nonempty)
    (s : Fin (m + 2)) (hs : s ∈ cocyclePos Y) :
    cocycleT Y β0 s ≤ cocycleTmin Y β0 hP := by
  have hmem : cocycleT Y β0 s
      ∈ (cocyclePos Y).image (cocycleT Y β0) :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  exact Finset.le_max' _ _ hmem

/-- Negative `t`-values lie above the right endpoint. -/
public theorem cocycleTmax_le_T {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hN : (cocycleNeg Y).Nonempty)
    (s : Fin (m + 2)) (hs : s ∈ cocycleNeg Y) :
    cocycleTmax Y β0 hN ≤ cocycleT Y β0 s := by
  have hmem : cocycleT Y β0 s
      ∈ (cocycleNeg Y).image (cocycleT Y β0) :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  exact Finset.min'_le _ _ hmem

/-- Feasibility: `β(t) ≥ 0` iff zero-class OK and `t` in `[tmin, tmax]`. -/
public theorem cocycleBeta_nonneg_iff {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ)
    (hP : (cocyclePos Y).Nonempty) (hN : (cocycleNeg Y).Nonempty)
    (t : ℝ) :
    (∀ s, 0 ≤ cocycleBeta Y β0 t s)
      ↔ (∀ s, cocycleLambda Y s = 0 → 0 ≤ β0 s)
        ∧ cocycleTmin Y β0 hP ≤ t ∧ t ≤ cocycleTmax Y β0 hN := by
  constructor
  · intro hpos
    refine ⟨?_, ?_, ?_⟩
    · intro s hs0
      have h := hpos s
      simp only [cocycleBeta, hs0, mul_zero, add_zero] at h
      exact h
    · obtain ⟨r, hrP, hrT⟩ := cocycleTmin_attains Y β0 hP
      have hposr : (0 : ℝ) < cocycleLambda Y r := by
        simp only [cocyclePos, Finset.mem_filter, Finset.mem_univ,
          true_and] at hrP
        exact hrP
      have h := hpos r
      simp only [cocycleBeta] at h
      have hle : cocycleT Y β0 r ≤ t := by
        simp only [cocycleT]
        rw [div_le_iff₀ hposr]
        linarith [h]
      rw [hrT] at hle
      exact hle
    · obtain ⟨r, hrN, hrT⟩ := cocycleTmax_attains Y β0 hN
      have hnegr : cocycleLambda Y r < 0 := by
        simp only [cocycleNeg, Finset.mem_filter, Finset.mem_univ,
          true_and] at hrN
        exact hrN
      have h := hpos r
      simp only [cocycleBeta] at h
      have hle : t ≤ cocycleT Y β0 r := by
        simp only [cocycleT]
        rw [le_div_iff_of_neg hnegr]
        linarith [h]
      rw [hrT] at hle
      exact hle
  · rintro ⟨hQ, htmin, htmax⟩ s
    simp only [cocycleBeta]
    by_cases hs0 : cocycleLambda Y s = 0
    · rw [hs0, mul_zero, add_zero]
      exact hQ s hs0
    · by_cases hpos : 0 < cocycleLambda Y s
      · have hmem : s ∈ cocyclePos Y := by
          simp only [cocyclePos, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact hpos
        have hle : cocycleT Y β0 s ≤ cocycleTmin Y β0 hP :=
          cocycleT_le_Tmin Y β0 hP s hmem
        have hval : cocycleT Y β0 s * cocycleLambda Y s = -β0 s := by
          simp only [cocycleT]
          exact div_mul_cancel₀ _ (ne_of_gt hpos)
        have hmul : cocycleT Y β0 s * cocycleLambda Y s
            ≤ t * cocycleLambda Y s :=
          mul_le_mul_of_nonneg_right (le_trans hle htmin) (le_of_lt hpos)
        linarith [hval, hmul]
      · have hneg : cocycleLambda Y s < 0 :=
          lt_of_le_of_ne' (not_lt.mp hpos) (Ne.symm hs0)
        have hmem : s ∈ cocycleNeg Y := by
          simp only [cocycleNeg, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact hneg
        have hle : cocycleTmax Y β0 hN ≤ cocycleT Y β0 s :=
          cocycleTmax_le_T Y β0 hN s hmem
        have hval : cocycleT Y β0 s * cocycleLambda Y s = -β0 s := by
          simp only [cocycleT]
          exact div_mul_cancel₀ _ (ne_of_lt hneg)
        have hmul : cocycleT Y β0 s * cocycleLambda Y s
            ≤ t * cocycleLambda Y s :=
          mul_le_mul_of_nonpos_right (le_trans htmax hle) (le_of_lt hneg)
        linarith [hval, hmul]

/-- A representation with two zero coordinates lies in the null set. -/
public theorem mem_cocycleNull_of_two_zeros {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m))
    (β : Fin (m + 2) → ℝ) (r₁ r₂ : Fin (m + 2)) (hne : r₁ ≠ r₂)
    (hpos : ∀ s, 0 ≤ β s) (hsum : ∑ s, β s = 1)
    (hcomb : ∑ s, β s • Y s = x)
    (hz1 : β r₁ = 0) (hz2 : β r₂ = 0) :
    x ∈ cocycleNull Y := by
  obtain ⟨i₀, hi₀⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
  have hcard : 1 < Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card hcard i₀
  set rest : Finset (Fin (m + 2)) :=
    Finset.univ.filter (fun s => s ≠ r₁ ∧ s ≠ r₂) with hrest
  have hrestmem : ∀ s : Fin (m + 2), s ∈ rest ↔ s ≠ r₁ ∧ s ≠ r₂ := by
    intro s
    simp [hrest]
  have hset : Finset.univ.filter (fun s : Fin (m + 2) => ¬(s ≠ r₁ ∧ s ≠ r₂))
      = {r₁, r₂} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : s = r₁
    · simp [h1]
    · by_cases h2 : s = r₂
      · simp [h2]
      · simp [h1, h2]
  have hcompl : ∀ f : (Fin (m + 2) → ℝ),
      ∑ s ∈ Finset.univ.filter (fun s => ¬(s ≠ r₁ ∧ s ≠ r₂)), f s
        = f r₁ + f r₂ := by
    intro f
    rw [hset]
    simp [hne]
  have hsumrest : ∑ s ∈ rest, β s = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s => s ≠ r₁ ∧ s ≠ r₂) β
    rw [← hrest] at hsplit
    rw [hcompl β, hz1, hz2, add_zero, hsum, add_zero] at hsplit
    exact hsplit
  have hcombrest : ∑ s ∈ rest, β s • Y s = x := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun s => s ≠ r₁ ∧ s ≠ r₂) (fun s => β s • Y s)
    rw [← hrest] at hsplit
    have hcompl0 : ∑ s ∈ Finset.univ.filter
        (fun s => ¬(s ≠ r₁ ∧ s ≠ r₂)), β s • Y s = 0 := by
      rw [hset]
      simp [hz1, hz2, hne]
    rw [hcompl0, add_zero, hcomb] at hsplit
    exact hsplit
  have hz : ∀ s ∈ rest,
      Y s ∈ Set.range (cocyclePadded Y r₁ r₂ i₀ j₀) := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hrestmem s).mp hs
    exact cocyclePadded_mem_range Y r₁ r₂ i₀ j₀ hi₀ s h1 h2
  have hmem : x ∈ convexHull ℝ
      (Set.range (cocyclePadded Y r₁ r₂ i₀ j₀)) := by
    have hcc : (∑ s ∈ rest, β s • Y s) ∈ convexHull ℝ
        (Set.range (cocyclePadded Y r₁ r₂ i₀ j₀)) :=
      (convex_convexHull ℝ _).sum_mem (fun s _ => hpos s) hsumrest
        (fun s hs => subset_convexHull ℝ _ (hz s hs))
    rw [hcombrest] at hcc
    exact hcc
  simp only [cocycleNull]
  exact Set.mem_biUnion (Set.mem_univ r₁) (Set.mem_biUnion (Set.mem_univ r₂)
    (Set.mem_biUnion (Set.mem_univ i₀) (Set.mem_biUnion hj₀ hmem)))

/-- Positive-class membership unfolds to `0 < λ`. -/
public theorem cocyclePos_mem {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2))
    (hr : r ∈ cocyclePos Y) : 0 < cocycleLambda Y r := by
  simp only [cocyclePos, Finset.mem_filter, Finset.mem_univ,
    true_and] at hr
  exact hr

/-- Negative-class membership unfolds to `λ < 0`. -/
public theorem cocycleNeg_mem {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2))
    (hr : r ∈ cocycleNeg Y) : cocycleLambda Y r < 0 := by
  simp only [cocycleNeg, Finset.mem_filter, Finset.mem_univ,
    true_and] at hr
  exact hr

/-- The left endpoint is nonpositive for nonnegative weights. -/
public theorem cocycleTmin_le_zero {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hP : (cocyclePos Y).Nonempty)
    (hpos0 : ∀ s, 0 ≤ β0 s) :
    cocycleTmin Y β0 hP ≤ 0 := by
  obtain ⟨r, hrP, hrT⟩ := cocycleTmin_attains Y β0 hP
  have hpos : (0 : ℝ) < cocycleLambda Y r := cocyclePos_mem Y r hrP
  rw [← hrT]
  simp only [cocycleT]
  rw [div_le_iff₀ hpos, zero_mul]
  exact neg_nonpos.mpr (hpos0 r)

/-- The right endpoint is nonnegative for nonnegative weights. -/
public theorem cocycleTmax_nonneg {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hN : (cocycleNeg Y).Nonempty)
    (hpos0 : ∀ s, 0 ≤ β0 s) :
    0 ≤ cocycleTmax Y β0 hN := by
  obtain ⟨r, hrN, hrT⟩ := cocycleTmax_attains Y β0 hN
  have hneg : cocycleLambda Y r < 0 := cocycleNeg_mem Y r hrN
  rw [← hrT]
  simp only [cocycleT]
  rw [le_div_iff_of_neg hneg, zero_mul]
  exact neg_nonpos.mpr (hpos0 r)

/-- Line points in `[tmin, tmax]` are nonnegative for nonnegative weights. -/
public theorem cocycleBeta_nonneg_of_mem_Icc {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hP : (cocyclePos Y).Nonempty)
    (hN : (cocycleNeg Y).Nonempty) (hpos0 : ∀ s, 0 ≤ β0 s)
    (t : ℝ) (hlo : cocycleTmin Y β0 hP ≤ t)
    (hhi : t ≤ cocycleTmax Y β0 hN) :
    ∀ s, 0 ≤ cocycleBeta Y β0 t s := by
  rw [cocycleBeta_nonneg_iff Y β0 hP hN t]
  exact ⟨fun s _ => hpos0 s, hlo, hhi⟩

/-- The signed coefficient equals the sign of `λ`. -/
public theorem cocycleSigma_eq_sign_lambda {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) (r : Fin (m + 2)) :
    cocycleSigma Y r = Real.sign (cocycleLambda Y r) := by
  simp only [cocycleSigma, cocycleLambda]
  set c : ℝ := (-1) ^ (r : ℕ) with hc
  have hc01 : c = 1 ∨ c = -1 := by
    rw [hc]
    rcases Nat.even_or_odd (r : ℕ) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  have hc2 : c * c = 1 := by
    rcases hc01 with h | h
    · rw [h, one_mul]
    · rw [h, neg_mul_neg, one_mul]
  have hD : cocycleDet Y r = c * cocycleLambda Y r := by
    simp only [cocycleLambda]
    rw [← hc, ← mul_assoc, hc2, one_mul]
  rcases hc01 with h | h
  · rw [h, one_mul, one_mul]
  · have hDm : cocycleDet Y r = -cocycleLambda Y r := by
      rw [hD, h, neg_one_mul]
    have e1 : (-1 : ℝ) * -cocycleLambda Y r = cocycleLambda Y r := by
      rw [neg_mul_neg, one_mul]
    have e2 : (-1 : ℝ) * -Real.sign (cocycleLambda Y r)
        = Real.sign (cocycleLambda Y r) := by
      rw [neg_mul_neg, one_mul]
    rw [h, hDm, Real.sign_neg, e1, e2]

/-- Off the null set, the left-endpoint attainer is unique. -/
public theorem cocyclePos_attainer_unique {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) (hxN : x ∉ cocycleNull Y)
    (β0 : Fin (m + 2) → ℝ) (hpos0 : ∀ s, 0 ≤ β0 s)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x)
    (hP : (cocyclePos Y).Nonempty) (hN : (cocycleNeg Y).Nonempty)
    (rmin : Fin (m + 2)) (hrminP : rmin ∈ cocyclePos Y)
    (hrminT : cocycleT Y β0 rmin = cocycleTmin Y β0 hP)
    (r : Fin (m + 2)) (hrP : r ∈ cocyclePos Y)
    (hrT : cocycleT Y β0 r = cocycleTmin Y β0 hP) :
    r = rmin := by
  by_contra hne
  have hlammin : cocycleLambda Y rmin ≠ 0 :=
    ne_of_gt (cocyclePos_mem Y rmin hrminP)
  have hlamr : cocycleLambda Y r ≠ 0 :=
    ne_of_gt (cocyclePos_mem Y r hrP)
  have htmin : cocycleTmin Y β0 hP ≤ cocycleTmax Y β0 hN :=
    le_trans (cocycleTmin_le_zero Y β0 hP hpos0)
      (cocycleTmax_nonneg Y β0 hN hpos0)
  have hposT : ∀ s, 0 ≤ cocycleBeta Y β0 (cocycleTmin Y β0 hP) s :=
    cocycleBeta_nonneg_of_mem_Icc Y β0 hP hN hpos0 _ le_rfl htmin
  have hzmin : cocycleBeta Y β0 (cocycleTmin Y β0 hP) rmin = 0 := by
    have h0 : β0 rmin + cocycleTmin Y β0 hP * cocycleLambda Y rmin = 0 :=
      (cocycleT_eq Y β0 rmin _ hlammin).mpr hrminT.symm
    simpa [cocycleBeta] using h0
  have hzr : cocycleBeta Y β0 (cocycleTmin Y β0 hP) r = 0 := by
    have h0 : β0 r + cocycleTmin Y β0 hP * cocycleLambda Y r = 0 :=
      (cocycleT_eq Y β0 r _ hlamr).mpr hrT.symm
    simpa [cocycleBeta] using h0
  have hNmem : x ∈ cocycleNull Y :=
    mem_cocycleNull_of_two_zeros hm Y x _ rmin r (Ne.symm hne)
      hposT (cocycleBeta_sum Y β0 hsum0 _)
      (cocycleBeta_comb Y β0 x hcomb0 _) hzmin hzr
  exact hxN hNmem

/-- Off the null set, the right-endpoint attainer is unique. -/
public theorem cocycleNeg_attainer_unique {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) (hxN : x ∉ cocycleNull Y)
    (β0 : Fin (m + 2) → ℝ) (hpos0 : ∀ s, 0 ≤ β0 s)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x)
    (hP : (cocyclePos Y).Nonempty) (hN : (cocycleNeg Y).Nonempty)
    (rmax : Fin (m + 2)) (hrmaxN : rmax ∈ cocycleNeg Y)
    (hrmaxT : cocycleT Y β0 rmax = cocycleTmax Y β0 hN)
    (r : Fin (m + 2)) (hrN : r ∈ cocycleNeg Y)
    (hrT : cocycleT Y β0 r = cocycleTmax Y β0 hN) :
    r = rmax := by
  by_contra hne
  have hlammax : cocycleLambda Y rmax ≠ 0 :=
    ne_of_lt (cocycleNeg_mem Y rmax hrmaxN)
  have hlamr : cocycleLambda Y r ≠ 0 :=
    ne_of_lt (cocycleNeg_mem Y r hrN)
  have htmin : cocycleTmin Y β0 hP ≤ cocycleTmax Y β0 hN :=
    le_trans (cocycleTmin_le_zero Y β0 hP hpos0)
      (cocycleTmax_nonneg Y β0 hN hpos0)
  have hposT : ∀ s, 0 ≤ cocycleBeta Y β0 (cocycleTmax Y β0 hN) s :=
    cocycleBeta_nonneg_of_mem_Icc Y β0 hP hN hpos0 _ htmin le_rfl
  have hzmax : cocycleBeta Y β0 (cocycleTmax Y β0 hN) rmax = 0 := by
    have h0 : β0 rmax + cocycleTmax Y β0 hN * cocycleLambda Y rmax = 0 :=
      (cocycleT_eq Y β0 rmax _ hlammax).mpr hrmaxT.symm
    simpa [cocycleBeta] using h0
  have hzr : cocycleBeta Y β0 (cocycleTmax Y β0 hN) r = 0 := by
    have h0 : β0 r + cocycleTmax Y β0 hN * cocycleLambda Y r = 0 :=
      (cocycleT_eq Y β0 r _ hlamr).mpr hrT.symm
    simpa [cocycleBeta] using h0
  have hNmem : x ∈ cocycleNull Y :=
    mem_cocycleNull_of_two_zeros hm Y x _ rmax r (Ne.symm hne)
      hposT (cocycleBeta_sum Y β0 hsum0 _)
      (cocycleBeta_comb Y β0 x hcomb0 _) hzmax hzr
  exact hxN hNmem

/-- Positive-class omission membership iff attaining the left endpoint. -/
public theorem mem_cocycleSimplex_iff_Tmin {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hpos0 : ∀ s, 0 ≤ β0 s)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x)
    (hP : (cocyclePos Y).Nonempty) (hN : (cocycleNeg Y).Nonempty)
    (r : Fin (m + 2)) (hrP : r ∈ cocyclePos Y) :
    x ∈ cocycleSimplex Y r ↔ cocycleT Y β0 r = cocycleTmin Y β0 hP := by
  have hlam : cocycleLambda Y r ≠ 0 :=
    ne_of_gt (cocyclePos_mem Y r hrP)
  have htmin : cocycleTmin Y β0 hP ≤ cocycleTmax Y β0 hN :=
    le_trans (cocycleTmin_le_zero Y β0 hP hpos0)
      (cocycleTmax_nonneg Y β0 hN hpos0)
  rw [mem_cocycleSimplex_iff_beta Y r hlam x β0 hsum0 hcomb0 r hlam,
    cocycleBeta_nonneg_iff Y β0 hP hN]
  constructor
  · rintro ⟨hQ, hlo, hhi⟩
    exact le_antisymm (cocycleT_le_Tmin Y β0 hP r hrP) hlo
  · intro heq
    refine ⟨fun s _ => hpos0 s, ?_, ?_⟩
    · simp [heq]
    · rw [heq]; exact htmin

/-- Negative-class omission membership iff attaining the right endpoint. -/
public theorem mem_cocycleSimplex_iff_Tmax {m : ℕ}
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m))
    (β0 : Fin (m + 2) → ℝ) (hpos0 : ∀ s, 0 ≤ β0 s)
    (hsum0 : ∑ s, β0 s = 1) (hcomb0 : ∑ s, β0 s • Y s = x)
    (hP : (cocyclePos Y).Nonempty) (hN : (cocycleNeg Y).Nonempty)
    (r : Fin (m + 2)) (hrN : r ∈ cocycleNeg Y) :
    x ∈ cocycleSimplex Y r ↔ cocycleT Y β0 r = cocycleTmax Y β0 hN := by
  have hlam : cocycleLambda Y r ≠ 0 :=
    ne_of_lt (cocycleNeg_mem Y r hrN)
  have htmin : cocycleTmin Y β0 hP ≤ cocycleTmax Y β0 hN :=
    le_trans (cocycleTmin_le_zero Y β0 hP hpos0)
      (cocycleTmax_nonneg Y β0 hN hpos0)
  rw [mem_cocycleSimplex_iff_beta Y r hlam x β0 hsum0 hcomb0 r hlam,
    cocycleBeta_nonneg_iff Y β0 hP hN]
  constructor
  · rintro ⟨hQ, hlo, hhi⟩
    exact le_antisymm hhi (cocycleTmax_le_T Y β0 hN r hrN)
  · intro heq
    refine ⟨fun s _ => hpos0 s, ?_, ?_⟩
    · rw [heq]; exact htmin
    · simp [heq]

/-- Lemma 2.1 (general case, `m ≥ 1`): the alternating deletion sum
vanishes a.e. Off the null set, either no convex representation exists
(all indicators vanish), all `λ` coefficients vanish (all signs vanish),
or the line analysis gives two delta contributions `+1` and `-1`. -/
public theorem cocycle_alternating_sum {m : ℕ} (hm : 1 ≤ m)
    (Y : Fin (m + 2) → EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∑ r, cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x = 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      x ∉ cocycleNull Y :=
    measure_eq_zero_iff_ae_notMem.mp (volume_cocycleNull Y)
  filter_upwards [hae] with x hxN
  by_cases hex : ∃ β0 : Fin (m + 2) → ℝ, (∀ s, 0 ≤ β0 s)
      ∧ ∑ s, β0 s = 1 ∧ (∑ s, β0 s • Y s) = x
  · obtain ⟨β0, hpos0, hsum0, hcomb0⟩ := hex
    by_cases hlam : ∃ r₀, cocycleLambda Y r₀ ≠ 0
    · obtain ⟨⟨rp, hrp⟩, ⟨rn, hrn⟩⟩ := cocycleLambda_sign_classes Y hlam
      have hP : (cocyclePos Y).Nonempty :=
        ⟨rp, Finset.mem_filter.mpr ⟨Finset.mem_univ rp, hrp⟩⟩
      have hN : (cocycleNeg Y).Nonempty :=
        ⟨rn, Finset.mem_filter.mpr ⟨Finset.mem_univ rn, hrn⟩⟩
      obtain ⟨rmin, hrminP, hrminT⟩ := cocycleTmin_attains Y β0 hP
      obtain ⟨rmax, hrmaxN, hrmaxT⟩ := cocycleTmax_attains Y β0 hN
      have hposmin : (0 : ℝ) < cocycleLambda Y rmin :=
        cocyclePos_mem Y rmin hrminP
      have hnegmax : cocycleLambda Y rmax < 0 :=
        cocycleNeg_mem Y rmax hrmaxN
      have hminneq : rmin ≠ rmax := by
        intro heq
        rw [heq] at hposmin
        linarith
      have hsigmin : cocycleSigma Y rmin = 1 := by
        rw [cocycleSigma_eq_sign_lambda]
        exact Real.sign_of_pos hposmin
      have hsigmax : cocycleSigma Y rmax = -1 := by
        rw [cocycleSigma_eq_sign_lambda]
        exact Real.sign_of_neg hnegmax
      have hindmin : (cocycleSimplex Y rmin).indicator
          (1 : EuclideanSpace ℝ (Fin m) → ℝ) x = (1 : ℝ) := by
        have hmem : x ∈ cocycleSimplex Y rmin := by
          rw [mem_cocycleSimplex_iff_Tmin Y x β0 hpos0 hsum0 hcomb0 hP hN
            rmin hrminP]
          exact hrminT
        simp only [Set.indicator_of_mem hmem 1, Pi.one_apply]
      have hindmax : (cocycleSimplex Y rmax).indicator
          (1 : EuclideanSpace ℝ (Fin m) → ℝ) x = (1 : ℝ) := by
        have hmem : x ∈ cocycleSimplex Y rmax := by
          rw [mem_cocycleSimplex_iff_Tmax Y x β0 hpos0 hsum0 hcomb0 hP hN
            rmax hrmaxN]
          exact hrmaxT
        simp only [Set.indicator_of_mem hmem 1, Pi.one_apply]
      have hterm : ∀ r : Fin (m + 2),
          cocycleSigma Y r * (cocycleSimplex Y r).indicator 1 x
            = (if r = rmin then (1 : ℝ) else 0)
              - (if r = rmax then (1 : ℝ) else 0) := by
        intro r
        by_cases hrmin : r = rmin
        · by_cases hrmax : r = rmax
          · exact absurd (hrmin.symm.trans hrmax) hminneq
          · subst hrmin
            simp only [hrmax, ite_false, ite_true,
              hsigmin, hindmin, one_mul, sub_zero]
        · by_cases hrmax : r = rmax
          · subst hrmax
            simp only [hrmin, ite_false, ite_true,
              hsigmax, hindmax, mul_one, zero_sub]
          · simp only [hrmin, hrmax, ite_false]
            by_cases hlamr : cocycleLambda Y r = 0
            · rw [cocycleSigma_eq_sign_lambda, hlamr, Real.sign_zero,
                zero_mul, sub_zero]
            · rcases lt_or_gt_of_ne hlamr with hneg | hpos
              · have hrN : r ∈ cocycleNeg Y :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ r, hneg⟩
                have hnot : x ∉ cocycleSimplex Y r := by
                  rw [mem_cocycleSimplex_iff_Tmax Y x β0 hpos0 hsum0
                    hcomb0 hP hN r hrN]
                  intro hcon
                  exact hrmax (cocycleNeg_attainer_unique hm Y x hxN β0
                    hpos0 hsum0 hcomb0 hP hN rmax hrmaxN hrmaxT r hrN hcon)
                rw [Set.indicator_of_notMem hnot 1, mul_zero, sub_zero]
              · have hrP : r ∈ cocyclePos Y :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpos⟩
                have hnot : x ∉ cocycleSimplex Y r := by
                  rw [mem_cocycleSimplex_iff_Tmin Y x β0 hpos0 hsum0
                    hcomb0 hP hN r hrP]
                  intro hcon
                  exact hrmin (cocyclePos_attainer_unique hm Y x hxN β0
                    hpos0 hsum0 hcomb0 hP hN rmin hrminP hrminT r hrP hcon)
                rw [Set.indicator_of_notMem hnot 1, mul_zero, sub_zero]
      rw [Finset.sum_congr rfl (fun r _ => hterm r),
        Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]
    · have hall : ∀ r, cocycleLambda Y r = 0 :=
        fun r => not_ne_iff.mp fun h => hlam ⟨r, h⟩
      apply Finset.sum_eq_zero
      intro r _
      rw [cocycleSigma_eq_sign_lambda, hall r, Real.sign_zero, zero_mul]
  · apply Finset.sum_eq_zero
    intro r _
    have hnot : x ∉ cocycleSimplex Y r := by
      intro hmem
      rw [mem_cocycleSimplex_iff] at hmem
      obtain ⟨β, hpos, hsum, hcomb, hr0⟩ := hmem
      exact hex ⟨β, hpos, hsum, hcomb⟩
    rw [Set.indicator_of_notMem hnot 1, mul_zero]

end HypercubeInequality
