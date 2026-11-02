import GaussianProductMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Actual independent real-Gaussian realization of the normalized complex
Gaussian factors used at manuscript lines 2656--2678.  No distributional or
moment identity is assumed in the statements below. -/

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators

namespace AHHGaussian

abbrev Entries (n h : ℕ) := (Fin n × Fin h) → ℝ
abbrev PairEntries (n h : ℕ) := Entries n h × Entries n h
abbrev FourEntries (n h : ℕ) := PairEntries n h × PairEntries n h

def pairGaussianLaw (n h : ℕ) : Measure (PairEntries n h) :=
  (gaussianProductLaw (Fin n × Fin h)).prod (gaussianProductLaw (Fin n × Fin h))

def fourGaussianLaw (n h : ℕ) : Measure (FourEntries n h) :=
  (pairGaussianLaw n h).prod (pairGaussianLaw n h)

instance pairGaussianLaw_probability (n h : ℕ) : IsProbabilityMeasure (pairGaussianLaw n h) := by
  unfold pairGaussianLaw
  infer_instance

instance fourGaussianLaw_probability (n h : ℕ) : IsProbabilityMeasure (fourGaussianLaw n h) := by
  unfold fourGaussianLaw
  infer_instance

/-- The Boolean selects one of the two independent real copies, not a complex sign. -/
def selectCopy {n h : ℕ} (b : Bool) (x : PairEntries n h) : Entries n h :=
  if b then x.2 else x.1

theorem measurable_selectCopy (n h : ℕ) (b : Bool) :
    Measurable (@selectCopy n h b) := by
  cases b
  · exact measurable_fst
  · exact measurable_snd

theorem pairGaussianLaw_map_selectCopy (n h : ℕ) (b : Bool) :
    (pairGaussianLaw n h).map (selectCopy b) = gaussianProductLaw (Fin n × Fin h) := by
  cases b
  · change Measure.map Prod.fst ((gaussianProductLaw (Fin n × Fin h)).prod
      (gaussianProductLaw (Fin n × Fin h))) = _
    simp
  · change Measure.map Prod.snd ((gaussianProductLaw (Fin n × Fin h)).prod
      (gaussianProductLaw (Fin n × Fin h))) = _
    simp

/-- All four real tensor pairs have exactly the original real tensor law. -/
theorem fourGaussianLaw_map_select (n h : ℕ) (b c : Bool) :
    (fourGaussianLaw n h).map (fun x => (selectCopy b x.1, selectCopy c x.2)) =
      pairGaussianLaw n h := by
  change Measure.map (Prod.map (selectCopy b) (selectCopy c))
    ((pairGaussianLaw n h).prod (pairGaussianLaw n h)) = _
  rw [← Measure.map_prod_map _ _ (measurable_selectCopy n h b)
    (measurable_selectCopy n h c), pairGaussianLaw_map_selectCopy,
    pairGaussianLaw_map_selectCopy]
  rfl

def sign (s : Bool) : ℝ := if s then 1 else -1

@[simp] theorem sign_sq (s : Bool) : sign s ^ 2 = 1 := by
  cases s <;> norm_num [sign]

def normalizedCoordinate (h : ℕ) (s : Bool) (a a' : ℝ) : ℂ :=
  ((a : ℂ) + Complex.I * (sign s : ℂ) * (a' : ℂ)) / (Real.sqrt (2 * (h : ℝ)) : ℂ)

def normalizedFactor (n h : ℕ) (s : Bool) (x : PairEntries n h) (i : Fin n) :
    EuclideanSpace ℂ (Fin h) :=
  (MeasurableEquiv.toLp 2 (Fin h → ℂ))
    (fun j => normalizedCoordinate h s (x.1 (i,j)) (x.2 (i,j)))

@[simp] theorem normalizedFactor_apply (n h : ℕ) (s : Bool) (x : PairEntries n h)
    (i : Fin n) (j : Fin h) :
    normalizedFactor n h s x i j = normalizedCoordinate h s (x.1 (i,j)) (x.2 (i,j)) := rfl

theorem normalizedCoordinate_norm_sq (h : ℕ) (s : Bool) (a a' : ℝ) :
    ‖normalizedCoordinate h s a a'‖ ^ 2 = (a^2 + a'^2) / (2 * (h : ℝ)) := by
  rw [normalizedCoordinate, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (by positivity), Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.mul_im,
    Complex.I_im, zero_mul, one_mul, sub_zero, mul_zero, zero_add,
    Complex.add_im, add_zero]
  cases s <;> simp [sign] <;> ring

theorem normalizedFactor_norm_sq (n h : ℕ) (s : Bool) (x : PairEntries n h)
    (i : Fin n) :
    ‖normalizedFactor n h s x i‖ ^ 2 =
      ∑ j : Fin h, ((x.1 (i,j))^2 + (x.2 (i,j))^2) / (2 * (h : ℝ)) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [normalizedFactor_apply, normalizedCoordinate_norm_sq]

theorem coordinate_integrable_pow {ι : Type*} [Fintype ι] (i : ι) (k : ℕ) :
    Integrable (fun x : ι → ℝ => x i ^ k) (gaussianProductLaw ι) := by
  have hi := standardGaussian_integrable_pow k
  rw [← gaussianProductLaw_coordinate i] at hi
  exact (integrable_map_measure (continuous_pow k).aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp hi

theorem coordinate_second_moment {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, x i ^ 2 ∂gaussianProductLaw ι) = 1 := by
  have he := integral_map (μ := gaussianProductLaw ι) (φ := fun x : ι → ℝ => x i)
    (f := fun z : ℝ => z^2) (measurable_pi_apply i).aemeasurable
    (continuous_pow 2).aestronglyMeasurable
  rw [gaussianProductLaw_coordinate] at he
  rw [← he]
  simpa using standardGaussian_moment_even 1

theorem pair_coordinate_sq_integrable (n h : ℕ) (i : Fin n × Fin h) (b : Bool) :
    Integrable (fun x : PairEntries n h => (selectCopy b x i)^2) (pairGaussianLaw n h) := by
  exact (show MeasurePreserving (selectCopy b) (pairGaussianLaw n h)
    (gaussianProductLaw (Fin n × Fin h)) from
      ⟨measurable_selectCopy n h b, pairGaussianLaw_map_selectCopy n h b⟩).integrable_comp_of_integrable (coordinate_integrable_pow i 2)

theorem pair_coordinate_second_moment (n h : ℕ) (i : Fin n × Fin h) (b : Bool) :
    (∫ x : PairEntries n h, (selectCopy b x i)^2 ∂pairGaussianLaw n h) = 1 := by
  have he := integral_map (μ := pairGaussianLaw n h) (φ := @selectCopy n h b)
    (f := fun x : Entries n h => x i^2) (measurable_selectCopy n h b).aemeasurable
    ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
  rw [pairGaussianLaw_map_selectCopy] at he
  rw [← he]
  exact coordinate_second_moment i

/-- Integrability is proved for the squared Euclidean norm, before taking its expectation. -/
theorem normalizedFactor_integrable_norm_sq (n h : ℕ) (s : Bool) (i : Fin n) :
    Integrable (fun x => ‖normalizedFactor n h s x i‖^2) (pairGaussianLaw n h) := by
  simp_rw [normalizedFactor_norm_sq]
  apply integrable_finset_sum
  intro j hj
  exact ((pair_coordinate_sq_integrable n h (i,j) false).add
    (pair_coordinate_sq_integrable n h (i,j) true)).div_const _

/-- The exact normalization E‖φ‖²=1 for every positive local dimension and every sign. -/
theorem normalizedFactor_expected_norm_sq (n h : ℕ) (hh : 0 < h)
    (s : Bool) (i : Fin n) :
    (∫ x, ‖normalizedFactor n h s x i‖^2 ∂pairGaussianLaw n h) = 1 := by
  simp_rw [normalizedFactor_norm_sq]
  have hij (j : Fin h) : Integrable (fun x : PairEntries n h =>
      ((x.1 (i,j))^2 + (x.2 (i,j))^2) / (2 * (h : ℝ))) (pairGaussianLaw n h) :=
    ((pair_coordinate_sq_integrable n h (i,j) false).add
      (pair_coordinate_sq_integrable n h (i,j) true)).div_const _
  rw [integral_finset_sum _ (fun j _ => hij j)]
  have hterm (j : Fin h) :
      (∫ x : PairEntries n h, ((x.1 (i,j))^2 + (x.2 (i,j))^2) /
        (2 * (h : ℝ)) ∂pairGaussianLaw n h) = 1 / (h : ℝ) := by
    change (∫ x : PairEntries n h,
      ((selectCopy false x (i,j))^2 + (selectCopy true x (i,j))^2) /
      (2 * (h : ℝ)) ∂pairGaussianLaw n h) = _
    rw [integral_div, integral_add (pair_coordinate_sq_integrable n h (i,j) false)
      (pair_coordinate_sq_integrable n h (i,j) true)]
    rw [pair_coordinate_second_moment, pair_coordinate_second_moment]
    ring
  simp_rw [hterm]
  simp [ne_of_gt (show (0:ℝ) < h by exact_mod_cast hh)]

/-- The real and imaginary coordinates are formed from independent actual
standard real normals. -/
theorem normalizedFactor_coordinate_parts_independent (n h : ℕ) (s : Bool)
    (i : Fin n) (j : Fin h) :
    IndepFun (fun x : PairEntries n h => (normalizedFactor n h s x i j).re)
      (fun x : PairEntries n h => (normalizedFactor n h s x i j).im)
      (pairGaussianLaw n h) := by
  have hind := indepFun_prod
    (μ := gaussianProductLaw (Fin n × Fin h))
    (ν := gaussianProductLaw (Fin n × Fin h))
    (X := fun x : Entries n h => x (i,j) / Real.sqrt (2 * (h : ℝ)))
    (Y := fun x : Entries n h => sign s * x (i,j) / Real.sqrt (2 * (h : ℝ)))
    (by fun_prop) (by fun_prop)
  have hre (x : PairEntries n h) : (normalizedFactor n h s x i j).re =
      x.1 (i,j) / Real.sqrt (2 * (h : ℝ)) := by
    simp only [normalizedFactor_apply, normalizedCoordinate, Complex.div_ofReal_re,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  have him (x : PairEntries n h) : (normalizedFactor n h s x i j).im =
      sign s * x.2 (i,j) / Real.sqrt (2 * (h : ℝ)) := by
    simp only [normalizedFactor_apply, normalizedCoordinate, Complex.div_ofReal_im,
      Complex.add_im, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  simp_rw [hre, him]
  exact hind

/-- Exact variance for an arbitrary scalar multiple of either real copy. -/
theorem pairGaussianLaw_scaled_coordinate (n h : ℕ) (i : Fin n × Fin h)
    (b : Bool) (c : ℝ) :
    (pairGaussianLaw n h).map (fun x => c * selectCopy b x i) =
      gaussianReal 0 ⟨c^2, sq_nonneg c⟩ := by
  change (pairGaussianLaw n h).map ((fun x : Entries n h => c * x i) ∘ selectCopy b) = _
  rw [← Measure.map_map (by fun_prop) (measurable_selectCopy n h b),
    pairGaussianLaw_map_selectCopy, gaussianProductLaw_scaled_coordinate]

theorem normalizedFactor_real_coordinate_law (n h : ℕ) (hh : 0 < h)
    (s : Bool) (i : Fin n) (j : Fin h) :
    (pairGaussianLaw n h).map (fun x => (normalizedFactor n h s x i j).re) =
      gaussianReal 0 ⟨1 / (2 * (h : ℝ)), by positivity⟩ := by
  have he : (fun x : PairEntries n h => (normalizedFactor n h s x i j).re) =
      (fun x => (1 / Real.sqrt (2 * (h : ℝ))) * selectCopy false x (i,j)) := by
    funext x
    simp only [normalizedFactor_apply, normalizedCoordinate, selectCopy, Bool.false_eq_true,
      ↓reduceIte, Complex.div_ofReal_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  rw [he, pairGaussianLaw_scaled_coordinate]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, div_pow, one_pow, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ 2 * (h : ℝ))]

theorem normalizedFactor_imag_coordinate_law (n h : ℕ) (hh : 0 < h)
    (s : Bool) (i : Fin n) (j : Fin h) :
    (pairGaussianLaw n h).map (fun x => (normalizedFactor n h s x i j).im) =
      gaussianReal 0 ⟨1 / (2 * (h : ℝ)), by positivity⟩ := by
  have he : (fun x : PairEntries n h => (normalizedFactor n h s x i j).im) =
      (fun x => (sign s / Real.sqrt (2 * (h : ℝ))) * selectCopy true x (i,j)) := by
    funext x
    simp only [normalizedFactor_apply, normalizedCoordinate, selectCopy,
      ↓reduceIte, Complex.div_ofReal_im, Complex.add_im, Complex.ofReal_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  rw [he, pairGaussianLaw_scaled_coordinate]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, div_pow, sign_sq, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ 2 * (h : ℝ))]

/-- The two whole complex Gaussian factors are independent for every fixed
pair of signs, directly from the four-real Gaussian construction. -/
theorem normalizedFactors_independent (n h : ℕ) (s t : Bool) (i : Fin n) :
    IndepFun (fun x : FourEntries n h => normalizedFactor n h s x.1 i)
      (fun x => normalizedFactor n h t x.2 i) (fourGaussianLaw n h) := by
  exact indepFun_prod (μ := pairGaussianLaw n h) (ν := pairGaussianLaw n h)
    (X := fun x => normalizedFactor n h s x i)
    (Y := fun x => normalizedFactor n h t x i)
    (by unfold normalizedFactor normalizedCoordinate; fun_prop)
    (by unfold normalizedFactor normalizedCoordinate; fun_prop)

/-- Any injective finite coordinate subfamily has its literal iid Gaussian law. -/
theorem gaussian_subfamily_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) :
    (gaussianProductLaw ι).map (fun x : ι → ℝ => fun k : κ => x (f k)) =
      gaussianProductLaw κ := by
  have hi := gaussianProductLaw_iIndepFun (ι := ι) |>.precomp hf
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun k : κ => (measurable_pi_apply (f k)).aemeasurable)).mp hi
  have hcoord : (fun k : κ => (gaussianProductLaw ι).map (fun x : ι → ℝ => x (f k))) =
      (fun _ : κ => gaussianReal 0 1) := by
    funext k
    exact gaussianProductLaw_coordinate (f k)
  rw [hcoord] at hm
  exact hm

/-- Exact bridge from the flattened real/imaginary coordinates used by the
complex Wick proof to the pair-of-real-Gaussians source construction. -/
theorem gaussian_bool_split_preserving {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun x : (ι × Bool) → ℝ =>
      (fun i : ι => x (i,false), fun i : ι => x (i,true)))
      (gaussianProductLaw (ι × Bool))
      ((gaussianProductLaw ι).prod (gaussianProductLaw ι)) := by
  let f : ι ⊕ ι → ι × Bool := Sum.elim (fun i => (i,false)) (fun i => (i,true))
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f]
  have hsel : MeasurePreserving (fun x : (ι × Bool) → ℝ => fun k : ι ⊕ ι => x (f k))
      (gaussianProductLaw (ι × Bool)) (gaussianProductLaw (ι ⊕ ι)) :=
    ⟨by fun_prop, gaussian_subfamily_map f hf⟩
  exact (measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)).comp hsel

theorem gaussian_bool_split_map (n h : ℕ) :
    (gaussianProductLaw ((Fin n × Fin h) × Bool)).map
      (fun x => (fun ij => x (ij,false), fun ij => x (ij,true))) = pairGaussianLaw n h :=
  gaussian_bool_split_preserving.map_eq

#print axioms gaussian_bool_split_preserving

#print axioms normalizedFactor_integrable_norm_sq
#print axioms normalizedFactor_expected_norm_sq
#print axioms normalizedFactor_real_coordinate_law
#print axioms normalizedFactor_imag_coordinate_law
#print axioms normalizedFactor_coordinate_parts_independent
#print axioms normalizedFactors_independent
end AHHGaussian
