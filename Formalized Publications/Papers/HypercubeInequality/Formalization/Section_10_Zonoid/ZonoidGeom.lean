module

/-
# Lifted zonotopes: concrete construction and the `vol_1` identity

For a finite law with atoms `z_i` and weights `q_i`, the paper's
lifted zonotope is

`Kν = Σ_i [0, q_i (z_i, 1)] = { Σ_i t_i q_i (z_i, 1) : 0 ≤ t_i ≤ 1 }`

(Minkowski sum of segments, equivalently the image of the unit cube
under the linear map with columns `q_i (z_i, 1)`; the paper gives
both descriptions).  This module constructs `Kν` in the cube-image
form, for arbitrary generators, and proves kernel-checked:

* the membership characterization of a general zonotope;
* the one-dimensional zonotope identity: a zonotope on the line
  with nonnegative generators is the segment `[0, Σ a_i]`;
* `vol_1 (P_L Kν) = 1`: the last-coordinate projection of `Kν` is
  `[0, Σ q_i] = [0, 1]`, of one-dimensional Lebesgue measure `1`.

Still open (HI-ZONOID): the determinant volume identities
`vol_{d+1}(Kν) = S_d(ν)/(d+1)` and `vol_2(P_{E_j} Kν) = D_j(ν)/2`
(the zonotope volume formula in dimensions `≥ 2`), generator
orientation and horizontal-generator approximation in the volume
identities, and the Hausdorff-limit extension to all zonoids.
The reduction from those identities to Corollary 10.1 is
kernel-checked in `Zonoid.lean` (`HI-ZONOID-RED`).
-/

public import Section_7_Approximation.Approx

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

/-- Lift a point of `ℝ^d` to `ℝ^{d+1}` by appending coordinate `1`. -/
@[expose] public noncomputable def liftPt {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.lastCases (1 : ℝ) (fun t => z t))

public theorem liftPt_castSucc {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (t : Fin d) : liftPt z t.castSucc = z t := by
  simp only [liftPt, WithLp.ofLp_toLp, Fin.lastCases_castSucc]

public theorem liftPt_last {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    liftPt z (Fin.last d) = 1 := by
  simp only [liftPt, WithLp.ofLp_toLp, Fin.lastCases_last]

/-- A zonotope: image of the unit cube under the linear map whose
columns are the generators `g i`.  Allows arbitrary generators. -/
@[expose] public noncomputable def zonotope {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • g i) '' (Set.pi Set.univ fun _ => Set.Icc 0 1)

/-- Membership in a zonotope. -/
public theorem mem_zonotope {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ι → E) (x : E) :
    x ∈ zonotope g ↔ ∃ t : ι → ℝ, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
      ∧ x = ∑ i, t i • g i := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, fun i => Set.mem_pi.mp ht i (Set.mem_univ i), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Set.mem_pi.mpr (fun i _ => ht i), rfl⟩

/-- Lifted zonotope of finite data `(q, z)`. -/
@[expose] public noncomputable def liftZonotope {d : ℕ} {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (z : ι → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  zonotope (fun i => q i • liftPt (z i))

/-- One-dimensional zonotope with nonnegative generators. -/
public theorem zonotope_one_dim {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : Finset ι) :
    (fun t : ι → ℝ => ∑ i ∈ s, t i * a i)
        '' {t | ∀ i ∈ s, t i ∈ Set.Icc (0 : ℝ) 1}
      = Set.Icc 0 (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    ext y
    constructor
    · rintro ⟨t, -, rfl⟩
      simp only [Finset.sum_empty]
      exact ⟨le_rfl, le_rfl⟩
    · intro hy
      simp only [Finset.sum_empty, Set.mem_Icc] at hy
      refine ⟨0, by simp, ?_⟩
      simp [le_antisymm hy.2 hy.1]
  | insert i s hi ih =>
    have hsplit : ∀ t : ι → ℝ, (∑ x ∈ insert i s, t x * a x)
        = t i * a i + ∑ x ∈ s, t x * a x := fun t =>
      Finset.sum_insert hi
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      show (∑ i ∈ insert i s, t i * a i) ∈ Set.Icc 0 (∑ i ∈ insert i s, a i)
      rw [hsplit]
      have h1 : t i * a i ∈ Set.Icc 0 (a i) := by
        have hti := ht i (Finset.mem_insert_self i s)
        constructor
        · exact mul_nonneg hti.1 (ha i)
        · calc t i * a i ≤ 1 * a i :=
              mul_le_mul_of_nonneg_right hti.2 (ha i)
            _ = a i := one_mul _
      have h2 : (∑ x ∈ s, t x * a x) ∈ Set.Icc 0 (∑ x ∈ s, a x) := by
        have : (∑ x ∈ s, t x * a x) ∈ (fun t : ι → ℝ => ∑ x ∈ s, t x * a x)
            '' {t | ∀ i ∈ s, t i ∈ Set.Icc (0 : ℝ) 1} :=
          ⟨t, fun j hj => ht j (Finset.mem_insert_of_mem hj), rfl⟩
        rw [ih] at this
        exact this
      constructor
      · exact add_nonneg h1.1 h2.1
      · calc t i * a i + ∑ x ∈ s, t x * a x ≤ a i + ∑ x ∈ s, a x :=
            add_le_add h1.2 h2.2
          _ = ∑ x ∈ insert i s, a x := (Finset.sum_insert hi).symm
    · intro hy
      have hsum : (∑ x ∈ insert i s, a x) = a i + ∑ x ∈ s, a x :=
        Finset.sum_insert hi
      rw [hsum] at hy
      set u : ℝ := min y (a i) with hu
      have hu0 : 0 ≤ u := le_min hy.1 (ha i)
      have huai : u ≤ a i := min_le_right _ _
      have hv : y - u ∈ Set.Icc 0 (∑ x ∈ s, a x) := by
        constructor
        · have : u ≤ y := min_le_left _ _
          linarith
        · by_cases h : y ≤ a i
          · have hu2 : u = y := min_eq_left h
            rw [hu2]
            simp only [sub_self]
            exact Finset.sum_nonneg (fun x _ => ha x)
          · have hu2 : u = a i := min_eq_right (le_of_lt (not_le.mp h))
            rw [hu2]
            have := hy.2
            linarith
      rw [← ih] at hv
      obtain ⟨t', ht', hv'⟩ := hv
      set ti : ℝ := if a i = 0 then 0 else u / (a i) with hti_def
      have hti : ti ∈ Set.Icc (0 : ℝ) 1 := by
        by_cases hai : a i = 0
        · rw [hti_def, if_pos hai]
          exact ⟨le_rfl, by norm_num⟩
        · rw [hti_def, if_neg hai]
          constructor
          · exact div_nonneg hu0 (ha i)
          · rw [div_le_one (lt_of_le_of_ne (ha i) (Ne.symm hai))]
            exact huai
      have hua : ti * a i = u := by
        by_cases hai : a i = 0
        · have hu0 : u = 0 := by
            rw [hu, hai]
            exact min_eq_right hy.1
          rw [hti_def, if_pos hai, hai, hu0]
          simp
        · rw [hti_def, if_neg hai]
          field_simp
      refine ⟨Function.update t' i ti, ?_, ?_⟩
      · intro j hj
        rcases (Finset.mem_insert.mp hj) with rfl | hj'
        · rwa [Function.update_self]
        · have hji : j ≠ i := fun h => hi (h ▸ hj')
          rw [Function.update_of_ne hji]
          exact ht' j hj'
      · show (∑ x ∈ insert i s, (Function.update t' i ti) x * a x) = y
        rw [hsplit, Function.update_self, hua]
        have hrest : (∑ x ∈ s, (Function.update t' i ti) x * a x)
            = ∑ x ∈ s, t' x * a x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Function.update_of_ne (fun h : x = i => hi (by rw [h] at hx; exact hx))]
        have hv'' : (∑ x ∈ s, t' x * a x) = y - u := hv'
        rw [hrest, hv'']
        linarith [min_le_left y (a i)]

/-- Last-coordinate projection of the lifted zonotope is
`[0, Σ q_i]`: this is the `vol_1(P_L Kν) = 1` identity, once
`volume` on `ℝ` is read as one-dimensional Lebesgue measure. -/
public theorem projLast_liftZonotope {d : ℕ} {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (z : ι → EuclideanSpace ℝ (Fin d)) :
    (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d))
        '' liftZonotope q z
      = Set.Icc 0 (∑ i, q i) := by
  classical
  have hcoord : ∀ t : ι → ℝ,
      (∑ i, t i • (q i • liftPt (z i))) (Fin.last d)
        = ∑ i, t i * q i := by
    have key : ∀ (s : Finset ι) (t : ι → ℝ),
        (∑ i ∈ s, t i • (q i • liftPt (z i))) (Fin.last d)
          = ∑ i ∈ s, t i * q i := by
      intro s t
      induction s using Finset.induction with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
        simp [PiLp.add_apply, PiLp.smul_apply, liftPt_last]
    intro t
    exact key Finset.univ t
  have hcomp : (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d))
        ∘ (fun t : ι → ℝ => ∑ i, t i • (q i • liftPt (z i)))
      = fun t : ι → ℝ => ∑ i, t i * q i :=
    funext hcoord
  calc (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d))
        '' liftZonotope q z
      = (fun t : ι → ℝ => ∑ i, t i * q i)
          '' (Set.pi Set.univ fun _ => Set.Icc 0 1) := by
        rw [liftZonotope, zonotope, Set.image_image]
        congr 1
    _ = (fun t : ι → ℝ => ∑ i ∈ Finset.univ, t i * q i)
          '' {t | ∀ i ∈ (Finset.univ : Finset ι), t i ∈ Set.Icc (0 : ℝ) 1} := by
        have hset : (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1)
            = {t | ∀ i ∈ (Finset.univ : Finset ι), t i ∈ Set.Icc (0 : ℝ) 1} := by
          ext t
          constructor
          · intro h i _
            exact h i (Set.mem_univ i)
          · intro h i _
            exact h i (Finset.mem_univ i)
        rw [hset]
    _ = Set.Icc 0 (∑ i, q i) := zonotope_one_dim q hq Finset.univ

/-- `vol_1 (P_L Kν) = 1` for probability weights. -/
public theorem volume_projLast_liftZonotope {d : ℕ} {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1)
    (z : ι → EuclideanSpace ℝ (Fin d)) :
    volume ((fun x : EuclideanSpace ℝ (Fin (d + 1)) => x (Fin.last d))
        '' liftZonotope q z) = 1 := by
  rw [projLast_liftZonotope q hq z, hsum]
  simp [Real.volume_Icc]


end HypercubeInequality
