import VolumetricNets
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open GaussianEllipsoid

namespace GaussianEllipsoid.Localized

/-- The coefficient space on a deterministic support. -/
abbrev Coeff (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SupportCoeff {n : ℕ} (I : Finset (Fin n)) := EuclideanSpace ℝ I

/-- Extend a coefficient vector by zero off its deterministic support. -/
def extend {n : ℕ} (I : Finset (Fin n)) (u : SupportCoeff I) : Coeff n :=
  (WithLp.equiv 2 _).symm (fun i => if hi : i ∈ I then u ⟨i, hi⟩ else 0)

@[simp] theorem extend_apply {n : ℕ} (I : Finset (Fin n)) (u : SupportCoeff I) (i : Fin n) :
    extend I u i = if hi : i ∈ I then u ⟨i, hi⟩ else 0 := rfl

@[simp] theorem extend_add {n : ℕ} (I : Finset (Fin n)) (u v : SupportCoeff I) :
    extend I (u + v) = extend I u + extend I v := by
  ext i
  simp only [extend_apply, PiLp.add_apply]
  split_ifs <;> simp

@[simp] theorem extend_smul {n : ℕ} (I : Finset (Fin n)) (a : ℝ) (u : SupportCoeff I) :
    extend I (a • u) = a • extend I u := by
  ext i
  simp only [extend_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

@[simp] theorem extend_neg {n : ℕ} (I : Finset (Fin n)) (u : SupportCoeff I) :
    extend I (-u) = -extend I u := by
  simpa only [neg_one_smul] using extend_smul I (-1) u

@[simp] theorem extend_sub {n : ℕ} (I : Finset (Fin n)) (u v : SupportCoeff I) :
    extend I (u-v) = extend I u-extend I v := by simp [sub_eq_add_neg]

@[simp] theorem norm_extend {n : ℕ} (I : Finset (Fin n)) (u : SupportCoeff I) :
    ‖extend I u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ i, ‖extend I u i‖ ^ 2) = ∑ i ∈ I, ‖extend I u i‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      simp [extend_apply, hi]
    _ = ∑ i : I, ‖u i‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      simp

/-- Zero extension preserves the coordinate l1 norm exactly. -/
@[simp] theorem l1_extend {n : ℕ} (I : Finset (Fin n)) (u : SupportCoeff I) :
    ∑ i, |extend I u i| = ∑ i, |u i| := by
  calc
    (∑ i, |extend I u i|) = ∑ i ∈ I, |extend I u i| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      simp [extend_apply, hi]
    _ = ∑ i : I, |u i| := by
      rw [← Finset.sum_coe_sort]
      simp

/-- Restriction to a deterministic support. -/
def restrict {n : ℕ} (I : Finset (Fin n)) (u : Coeff n) : SupportCoeff I :=
  (WithLp.equiv 2 _).symm (fun i => u i)

@[simp] theorem restrict_apply {n : ℕ} (I : Finset (Fin n)) (u : Coeff n) (i : I) :
    restrict I u i = u i := rfl

@[simp] theorem extend_restrict {n : ℕ} (I : Finset (Fin n)) (u : Coeff n)
    (hu : ∀ i ∉ I, u i = 0) : extend I (restrict I u) = u := by
  ext i
  simp only [extend_apply, restrict_apply]
  split_ifs with hi
  · rfl
  · exact (hu i hi).symm

/-- Both coefficient nets are internal, so every tail center retains every cap
and lower-norm condition in the tail class. -/
theorem exists_support_net {n : ℕ} (I : Finset (Fin n))
    (T : Set (SupportCoeff I)) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hT : ∀ u ∈ T, ‖u‖ ≤ R) :
    ∃ C : Finset (SupportCoeff I), (∀ u ∈ C, u ∈ T) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / δ)^I.card ∧
      (∀ u ∈ T, ∃ v ∈ C, ‖extend I u - extend I v‖ < δ) := by
  obtain ⟨C, hC, hcard, hnet, _⟩ := exists_internal_net T hR hδ hT
  refine ⟨C, hC, ?_, ?_⟩
  · simpa only [finrank_euclideanSpace, Fintype.card_coe] using hcard
  · intro u hu
    obtain ⟨v, hv, huv⟩ := hnet u hu
    refine ⟨v, hv, ?_⟩
    simpa only [← extend_sub, norm_extend, dist_eq_norm] using huv

end GaussianEllipsoid.Localized

namespace GaussianEllipsoid.Localized

/-- Euclidean norm is at most the coordinate l1 norm. -/
theorem norm_le_l1 {ι : Type*} [Fintype ι] (u : EuclideanSpace ℝ ι) :
    ‖u‖ ≤ ∑ i, |u i| := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [Real.norm_eq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |u i|)
      (fun i _ => abs_nonneg _))

/-- The l1-bounded head class on a fixed support. -/
def headClass {n : ℕ} (I : Finset (Fin n)) (R : ℝ) : Set (SupportCoeff I) :=
  {u | ∑ i, |u i| ≤ R}

/-- The normalized admissible tail class. Coordinatewise squared cap is
exactly the usual sqrt(d) times infinity-norm cap. -/
def tailClass {n : ℕ} (I : Finset (Fin n)) (β B d : ℝ) : Set (SupportCoeff I) :=
  {v | β ≤ ‖v‖ ∧ ‖v‖ ≤ B ∧ ∀ i, d * (v i)^2 ≤ ‖v‖^2}

theorem exists_head_net {n : ℕ} (I : Finset (Fin n)) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ C : Finset (SupportCoeff I), (∀ u ∈ C, u ∈ headClass I R) ∧
      (C.card : ℝ) ≤ (1 + 2 * R / δ)^I.card ∧
      (∀ u ∈ headClass I R, ∃ v ∈ C, ‖extend I u - extend I v‖ < δ) :=
  exists_support_net I (headClass I R) hR hδ
    (fun u hu => (norm_le_l1 u).trans hu)

theorem exists_tail_net {n : ℕ} (I : Finset (Fin n)) {β B d δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : Finset (SupportCoeff I), (∀ u ∈ C, u ∈ tailClass I β B d) ∧
      (C.card : ℝ) ≤ (1 + 2 * B / δ)^I.card ∧
      (∀ u ∈ tailClass I β B d, ∃ v ∈ C, ‖extend I u - extend I v‖ < δ) :=
  exists_support_net I (tailClass I β B d) hB hδ (fun u hu => hu.2.1)

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.exists_head_net
#print axioms GaussianEllipsoid.Localized.exists_tail_net
