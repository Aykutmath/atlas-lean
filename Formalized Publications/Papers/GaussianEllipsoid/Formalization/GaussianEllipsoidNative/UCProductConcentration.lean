import BMFiniteProductReplacement
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-! Dimension-free bounded-differences concentration on an actual finite iid
product, proved by row integration and Hoeffding's lemma. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace GaussianEllipsoid.UCProductConcentration
variable {X : Type*} [MeasurableSpace X] [Nonempty X]

abbrev productLaw (μ : Measure X) (n : ℕ) := Measure.pi (fun _ : Fin n => μ)

def boundedDifferences {n : ℕ} (f : (Fin n → X) → ℝ) (c : ℝ) : Prop :=
  ∀ x i y, |f (Function.update x i y)-f x| ≤ c

 theorem measurable_cons (n : ℕ) : Measurable (fun z : X × (Fin n → X) => (Fin.cons z.1 z.2 : Fin (n+1) → X)) := by
  apply measurable_pi_iff.mpr
  intro i
  cases i using Fin.cases
  · simpa using (measurable_fst : Measurable (fun z : X × (Fin n → X) => z.1))
  · rename_i j
    simpa only [Fin.cons_succ, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_snd : Measurable (fun z : X × (Fin n → X) => z.2))

 theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)

 theorem centered_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) (t : ℝ) :
    Integrable (fun x => Real.exp (t*(f x-∫ y, f y ∂μ))) μ :=
  (hasSubgaussianMGF_of_mem_Icc hf.aemeasurable
    (ae_of_all _ fun x => abs_le.mp (hM x))).integrable_exp_mul t

 theorem integral_abs_le_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : |∫ x, f x ∂μ| ≤ M := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using hM x)

/-- Finite-product MGF estimate. Its non-sharp universal constant is enough
for the exact exponential-in-n UC failure rate. -/
theorem product_centered_mgf (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M c : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : 0 ≤ c) (hbd : boundedDifferences f c)
    (t : ℝ) :
    (∫ x, Real.exp (t*(f x-∫ y, f y ∂productLaw μ n)) ∂productLaw μ n) ≤
      Real.exp ((n:ℝ)*c^2*t^2/2) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i : Fin 0 => Fin.elim0 i) := by
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp
  | succ n ih =>
    let F : X × (Fin n → X) → ℝ := fun z => f (Fin.cons z.1 z.2)
    have hmF : Measurable F := hf.comp (measurable_cons n)
    have hiF : Integrable F (μ.prod (productLaw μ n)) :=
      integrable_of_abs_bound hmF (fun z => hM _)
    let g : (Fin n → X) → ℝ := fun u => ∫ x, f (Fin.cons x u) ∂μ
    have hmg : Measurable g := hmF.stronglyMeasurable.integral_prod_left'.measurable
    have hgM : ∀ u, |g u| ≤ M := fun u => integral_abs_le_const fun x => hM _
    have hig : Integrable g (productLaw μ n) := integrable_of_abs_bound hmg hgM
    have hmf (u : Fin n → X) : Measurable (fun x => f (Fin.cons x u)) :=
      hmF.comp (measurable_id.prodMk measurable_const)
    have hif (u : Fin n → X) : Integrable (fun x => f (Fin.cons x u)) μ :=
      integrable_of_abs_bound (hmf u) (fun x => hM _)
    have hgbd : boundedDifferences g c := by
      intro u i y
      change |(∫ x, f (Fin.cons x (Function.update u i y)) ∂μ)-
        ∫ x, f (Fin.cons x u) ∂μ| ≤ c
      rw [← integral_sub (hif _) (hif _)]
      apply integral_abs_le_const
      intro x
      have he : Fin.cons x (Function.update u i y) = Function.update (Fin.cons x u : Fin (n+1) → X) i.succ y := by
        simpa only [Fin.insertNth_zero', Fin.succAbove_zero] using
          (Fin.insertNth_update (α := fun _ : Fin (n+1) => X) (0 : Fin (n+1)) x i y u)
      rw [he]
      exact hbd _ _ _
    have hmean : (∫ x, f x ∂productLaw μ (n+1)) = ∫ u, g u ∂productLaw μ n := by
      simpa only [Fin.insertNth_zero', g] using
        BMFiniteProductReplacement.integral_pi_insertNth μ (0 : Fin (n+1)) f
          (integrable_of_abs_bound hf hM)
    have hslice (u : Fin n → X) :
        (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ) ≤ Real.exp (c^2*t^2/2) := by
      let a : X := Classical.choice inferInstance
      let Z := fun x => f (Fin.cons x u)-f (Fin.cons a u)
      have hmZ : Measurable Z := (hmf u).sub_const _
      have hbZ : ∀ x, Z x ∈ Set.Icc (-c) c := by
        intro x
        apply abs_le.mp
        have hh := hbd (Fin.cons a u) (0 : Fin (n+1)) x
        simpa only [Z, ← Fin.insertNth_zero', Fin.update_insertNth] using hh
      have hs := hasSubgaussianMGF_of_mem_Icc hmZ.aemeasurable (ae_of_all μ hbZ)
      have he : (fun x => Z x-∫ y, Z y ∂μ) = fun x => f (Fin.cons x u)-g u := by
        funext x
        dsimp [Z, g]
        rw [integral_sub (hif u) (integrable_const _)]
        simp
      have hh := hs.mgf_le t
      rw [he] at hh
      simpa only [mgf, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat,
        Real.norm_eq_abs, show c- -c=2*c by ring, abs_of_nonneg (show 0 ≤ 2*c by positivity),
        show 2*c/2=c by ring] using hh
    have hiExp := centered_exp_integrable (μ := productLaw μ (n+1)) hf hM t
    have hExp : (∫ x, Real.exp (t*(f x-∫ y, f y ∂productLaw μ (n+1)))
        ∂productLaw μ (n+1)) =
      ∫ u, ∫ x, Real.exp (t*(f (Fin.cons x u)-∫ y, g y ∂productLaw μ n)) ∂μ
        ∂productLaw μ n := by
      rw [BMFiniteProductReplacement.integral_pi_insertNth μ (0 : Fin (n+1)) _ hiExp]
      simp only [Fin.insertNth_zero', hmean]
    have hfactor (u : Fin n → X) :
        (∫ x, Real.exp (t*(f (Fin.cons x u)-∫ y, g y ∂productLaw μ n)) ∂μ) =
      (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ)*
        Real.exp (t*(g u-∫ y, g y ∂productLaw μ n)) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all μ fun x => by dsimp only; rw [← Real.exp_add]; congr 1; ring
    rw [hExp]
    simp_rw [hfactor]
    have hiProd : Integrable (fun u =>
        (∫ x, Real.exp (t*(f (Fin.cons x u)-g u)) ∂μ)*
          Real.exp (t*(g u-∫ y, g y ∂productLaw μ n))) (productLaw μ n) := by
      have hi' : Integrable (fun z : X × (Fin n → X) =>
          Real.exp (t*(f (Fin.cons z.1 z.2)-∫ y, g y ∂productLaw μ n)))
          (μ.prod (productLaw μ n)) := by
        apply integrable_exp_mul_of_mem_Icc ((hmF.sub_const _).aemeasurable)
        apply ae_of_all
        intro z
        show F z - (∫ y, g y ∂productLaw μ n) ∈
          Set.Icc (-M-(∫ y, g y ∂productLaw μ n)) (M-(∫ y, g y ∂productLaw μ n))
        exact ⟨sub_le_sub_right (abs_le.mp (hM _)).1 _,
          sub_le_sub_right (abs_le.mp (hM _)).2 _⟩
      have hr := hi'.integral_prod_right
      simpa only [hfactor] using hr
    calc
      _ ≤ ∫ u, Real.exp (c^2*t^2/2)*Real.exp (t*(g u-∫ y, g y ∂productLaw μ n))
          ∂productLaw μ n :=
        integral_mono hiProd ((centered_exp_integrable hmg hgM t).const_mul _)
          (fun u => mul_le_mul_of_nonneg_right (hslice u) (Real.exp_nonneg _))
      _ = Real.exp (c^2*t^2/2)*
          (∫ u, Real.exp (t*(g u-∫ y, g y ∂productLaw μ n)) ∂productLaw μ n) := by
        rw [integral_const_mul]
      _ ≤ Real.exp (c^2*t^2/2)*Real.exp ((n:ℝ)*c^2*t^2/2) :=
        mul_le_mul_of_nonneg_left (ih g hmg hgM hgbd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

/-- Bounded differences produce a genuine sub-Gaussian MGF under the iid law. -/
theorem product_hasSubgaussianMGF (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M c : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : 0 ≤ c) (hbd : boundedDifferences f c) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂productLaw μ n)
      ⟨(n:ℝ)*c^2, by positivity⟩ (productLaw μ n) where
  integrable_exp_mul := centered_exp_integrable hf hM
  mgf_le := product_centered_mgf μ n f hf M c hM hc hbd

/-- Actual lower-tail bound; no concentration or conditional-law hypothesis. -/
theorem product_lower_tail (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M c : ℝ) (hM : ∀ x, |f x| ≤ M) (hc : 0 ≤ c) (hbd : boundedDifferences f c)
    (t : ℝ) (ht : 0 ≤ t) :
    (productLaw μ n).real {x | f x < (∫ y, f y ∂productLaw μ n)-t} ≤
      Real.exp (-t^2/(2*((n:ℝ)*c^2))) := by
  have h := (product_hasSubgaussianMGF μ n f hf M c hM hc hbd).neg.measure_ge_le ht
  apply le_trans (measureReal_mono (μ := productLaw μ n) ?_) h
  intro x hx
  change t ≤ -(f x-∫ y, f y ∂productLaw μ n)
  change f x < (∫ y, f y ∂productLaw μ n)-t at hx
  linarith

/-- The 1/n coordinate sensitivity used by normalized bounded free energy
has exponentially small deviations at rate n. -/
theorem normalized_product_lower_tail (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (hbd : boundedDifferences f (1/(n:ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    (productLaw μ n).real {x | f x < (∫ y, f y ∂productLaw μ n)-t} ≤
      Real.exp (-(n:ℝ)*t^2/2) := by
  have h := product_lower_tail μ n f hf M (1/(n:ℝ)) hM (by positivity) hbd t ht
  apply h.trans_eq
  congr 1
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  <;> ring

#print axioms normalized_product_lower_tail

#print axioms product_centered_mgf
end GaussianEllipsoid.UCProductConcentration
