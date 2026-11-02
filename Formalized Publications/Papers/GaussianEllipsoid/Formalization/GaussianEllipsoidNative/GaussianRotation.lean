import GaussianQuadraticSpectral
import GaussianProductMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]
abbrev E (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def rot (t : ℝ) (x : E (ι ⊕ ι)) : E (ι ⊕ ι) :=
  (WithLp.equiv 2 _).symm (Sum.elim
    (fun i => Real.cos t * x (.inl i) + Real.sin t * x (.inr i))
    (fun i => -Real.sin t * x (.inl i) + Real.cos t * x (.inr i)))

@[simp] theorem rot_inl (t : ℝ) (x : E (ι ⊕ ι)) (i : ι) :
    rot t x (.inl i) = Real.cos t * x (.inl i) + Real.sin t * x (.inr i) := rfl
@[simp] theorem rot_inr (t : ℝ) (x : E (ι ⊕ ι)) (i : ι) :
    rot t x (.inr i) = -Real.sin t * x (.inl i) + Real.cos t * x (.inr i) := rfl

private theorem rot_neg_rot (t : ℝ) (x : E (ι ⊕ ι)) : rot (-t) (rot t x) = x := by
  ext i
  cases i with
  | inl i =>
    simp only [rot_inl, rot_inr, Real.cos_neg, Real.sin_neg, neg_neg]
    linear_combination x (.inl i) * Real.sin_sq_add_cos_sq t
  | inr i =>
    simp only [rot_inl, rot_inr, Real.cos_neg, Real.sin_neg, neg_neg]
    linear_combination x (.inr i) * Real.sin_sq_add_cos_sq t

def rotation (t : ℝ) : E (ι ⊕ ι) ≃ₗᵢ[ℝ] E (ι ⊕ ι) where
  toFun := rot t
  invFun := rot (-t)
  left_inv := rot_neg_rot t
  right_inv := by intro x; simpa only [neg_neg] using rot_neg_rot (-t) x
  map_add' := by intros x y; ext i; cases i <;> simp [rot] <;> ring
  map_smul' := by intros c x; ext i; cases i <;> simp [rot] <;> ring
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖rot t x‖ ^ 2 = ‖x‖ ^ 2
    simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs,
      rot_inl, rot_inr]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    linear_combination ((x (.inl i))^2 + (x (.inr i))^2) * Real.sin_sq_add_cos_sq t

theorem rotation_preserving (t : ℝ) :
    MeasurePreserving (rotation (ι := ι) t)
      (euclideanGaussianLaw (ι ⊕ ι)) (euclideanGaussianLaw (ι ⊕ ι)) :=
  ⟨(rotation t).continuous.measurable, BMQuadraticSpectral.euclideanGaussianLaw_map_isometry _⟩

end GaussianVariance

namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

def split : E (ι ⊕ ι) ≃ᵐ E ι × E ι :=
  (((MeasurableEquiv.toLp 2 ((ι ⊕ ι) → ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ))).trans
    ((MeasurableEquiv.toLp 2 (ι → ℝ)).prodCongr
      (MeasurableEquiv.toLp 2 (ι → ℝ)))

@[simp] theorem split_fst_apply (x : E (ι ⊕ ι)) (i : ι) :
    (split x).1 i = x (.inl i) := rfl
@[simp] theorem split_snd_apply (x : E (ι ⊕ ι)) (i : ι) :
    (split x).2 i = x (.inr i) := rfl

theorem split_preserving : MeasurePreserving (split (ι := ι))
    (euclideanGaussianLaw (ι ⊕ ι)) ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) := by
  have h1 := BMQuadraticSpectral.coordinates_preserving (ι := ι ⊕ ι)
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have h3 := (BMQuadraticSpectral.coordinates_preserving (ι := ι)).symm
  exact (h3.prod h3).comp (h2.comp h1)

def pairRotation (t : ℝ) : E ι × E ι ≃ᵐ E ι × E ι :=
  (split.symm.trans (rotation t).toHomeomorph.toMeasurableEquiv).trans split

theorem pairRotation_apply (t : ℝ) (x : E ι × E ι) :
    pairRotation t x =
      (Real.cos t • x.1 + Real.sin t • x.2, -Real.sin t • x.1 + Real.cos t • x.2) := by
  ext i <;> rfl

theorem pairRotation_preserving (t : ℝ) :
    MeasurePreserving (pairRotation (ι := ι) t)
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι))
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) :=
  split_preserving.comp ((rotation_preserving t).comp split_preserving.symm)

end GaussianVariance

namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

def first (t : ℝ) (z : E ι × E ι) : E ι := Real.cos t • z.1 + Real.sin t • z.2

theorem continuous_first (t : ℝ) : Continuous (first (ι := ι) t) := by
  unfold first
  fun_prop

@[simp] theorem first_zero (z : E ι × E ι) : first 0 z = z.1 := by simp [first]
@[simp] theorem first_pi_div_two (z : E ι × E ι) : first (Real.pi/2) z = z.2 := by simp [first]

theorem first_add (t s : ℝ) (z : E ι × E ι) :
    first (t+s) z = first t (pairRotation s z) := by
  rw [pairRotation_apply]
  ext i
  simp only [first, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Real.cos_add, Real.sin_add]
  ring

theorem first_hasDerivAt (z : E ι × E ι) : HasDerivAt (fun t => first t z) z.2 0 := by
  simpa only [first, Pi.add_def, Real.sin_zero, Real.cos_zero, neg_zero, zero_smul, one_smul,
    zero_add] using ((Real.hasDerivAt_cos 0).smul_const z.1).add
      ((Real.hasDerivAt_sin 0).smul_const z.2)

theorem first_increment_stationary (f : E ι → ℝ) (t s : ℝ) :
    (∫ z, (f (first (t+s) z) - f (first s z))^2
      ∂(euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι)) =
    ∫ z, (f (first t z) - f z.1)^2
      ∂(euclideanGaussianLaw ι).prod (euclideanGaussianLaw ι) := by
  have h := (pairRotation_preserving (ι := ι) s).integral_comp'
    (fun z => (f (first t z)-f z.1)^2)
  convert h using 1
  congr 1
  funext z
  rw [first_add, pairRotation_apply]
  rfl

end GaussianVariance

namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

theorem first_derivative (t : ℝ) (z : E ι × E ι) :
    HasDerivAt (fun s => first s z) (-Real.sin t • z.1 + Real.cos t • z.2) t := by
  exact ((Real.hasDerivAt_cos t).smul_const z.1).add ((Real.hasDerivAt_sin t).smul_const z.2)

theorem first_velocity_bound (t : ℝ) (z : E ι × E ι) :
    ‖-Real.sin t • z.1 + Real.cos t • z.2‖ ≤ ‖z.1‖+‖z.2‖ := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul, norm_neg, Real.norm_eq_abs]
  exact add_le_add (by nlinarith [Real.abs_sin_le_one t, norm_nonneg z.1])
    (by nlinarith [Real.abs_cos_le_one t, norm_nonneg z.2])

end GaussianVariance

namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

theorem first_sub_bound (t : ℝ) (z : E ι × E ι) :
    ‖first t z-z.1‖ ≤ (‖z.1‖+‖z.2‖)*|t| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => first s z)
    (fun s _ => (first_derivative s z).hasDerivWithinAt)
    (fun s _ => first_velocity_bound s z)
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [first_zero, sub_zero, Real.norm_eq_abs] using h

theorem telescoping_square_bound (a : ℕ → ℝ) (n : ℕ) :
    (a n-a 0)^2 ≤ (n : ℝ)*∑ i ∈ Finset.range n, (a (i+1)-a i)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun _ : ℕ => (1 : ℝ)) (fun i => a (i+1)-a i)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Finset.sum_range_sub] using h

end GaussianVariance
