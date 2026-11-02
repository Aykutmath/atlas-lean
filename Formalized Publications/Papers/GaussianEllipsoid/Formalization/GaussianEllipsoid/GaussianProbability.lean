/-
Kernel-checked finite product Gaussian measures. Independence and
restriction are proved from the pinned mathlib product-measure API.
This file does not assert measurability of either existential fitting event.
-/
import GaussianEllipsoid.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Standard Gaussian coordinates on the actual vector space used by the paper. -/
def gaussianVectorLaw (d : Nat) : Measure (Vector d) :=
  Measure.pi (fun _ : Fin d => gaussianReal 0 1)

/-- Independent Gaussian rows, with the exact finite sample indexing. -/
def gaussianSampleLaw (d n : Nat) : Measure (Sample d n) :=
  Measure.pi (fun _ : Fin n => gaussianVectorLaw d)

instance gaussianVectorLaw_isProbability (d : Nat) :
    IsProbabilityMeasure (gaussianVectorLaw d) := by
  unfold gaussianVectorLaw
  infer_instance

instance gaussianSampleLaw_isProbability (d n : Nat) :
    IsProbabilityMeasure (gaussianSampleLaw d n) := by
  unfold gaussianSampleLaw
  infer_instance

theorem gaussianCoordinate_measurePreserving {d : Nat} (j : Fin d) :
    MeasurePreserving (fun x : Vector d => x j)
      (gaussianVectorLaw d) (gaussianReal 0 1) := by
  exact measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j

theorem gaussianRow_measurePreserving {d n : Nat} (i : Fin n) :
    MeasurePreserving (fun x : Sample d n => x i)
      (gaussianSampleLaw d n) (gaussianVectorLaw d) := by
  exact measurePreserving_eval (fun _ : Fin n => gaussianVectorLaw d) i

theorem gaussianCoordinate_map {d : Nat} (j : Fin d) :
    (gaussianVectorLaw d).map (fun x => x j) = gaussianReal 0 1 :=
  (gaussianCoordinate_measurePreserving j).map_eq

theorem gaussianRow_map {d n : Nat} (i : Fin n) :
    (gaussianSampleLaw d n).map (fun x => x i) = gaussianVectorLaw d :=
  (gaussianRow_measurePreserving i).map_eq

theorem gaussianCoordinates_independent (d : Nat) :
    iIndepFun (fun j : Fin d => fun x : Vector d => x j)
      (gaussianVectorLaw d) := by
  exact iIndepFun_pi (X := fun _ : Fin d => (id : Real -> Real))
    (fun _ => aemeasurable_id)

theorem gaussianRows_independent (d n : Nat) :
    iIndepFun (fun i : Fin n => fun x : Sample d n => x i)
      (gaussianSampleLaw d n) := by
  exact iIndepFun_pi (X := fun _ : Fin n => (id : Vector d -> Vector d))
    (fun _ => aemeasurable_id)

/-- Injectivity is essential: duplicated rows are not an independent sample. -/
theorem gaussianSample_restrict_map {d n m : Nat} (f : Fin m -> Fin n)
    (hf : Function.Injective f) :
    (gaussianSampleLaw d n).map (fun x i => x (f i)) =
      gaussianSampleLaw d m := by
  have hind : iIndepFun (fun i : Fin m => fun x : Sample d n => x (f i))
      (gaussianSampleLaw d n) :=
    iIndepFun.precomp hf (gaussianRows_independent d n)
  have hmap := iIndepFun.map_fun_eq_pi_map
    (fun i : Fin m => (measurable_pi_apply (f i)).aemeasurable) hind
  simp only [gaussianRow_map] at hmap
  simpa only [gaussianSampleLaw] using hmap

/-- Change of variables for a real function of one coordinate. -/
theorem integral_gaussianCoordinate {d : Nat} (j : Fin d)
    (f : Real -> Real) (hf : Measurable f) :
    integral (gaussianVectorLaw d) (fun x => f (x j)) =
      integral (gaussianReal 0 1) f := by
  calc
    _ = integral ((gaussianVectorLaw d).map (fun x => x j)) f :=
      (integral_map_of_stronglyMeasurable
        (measurable_pi_apply j) hf.stronglyMeasurable).symm
    _ = _ := by rw [gaussianCoordinate_map]

/-- Change of variables for a measurable real function of one sample row. -/
theorem integral_gaussianRow {d n : Nat} (i : Fin n)
    (f : Vector d -> Real) (hf : Measurable f) :
    integral (gaussianSampleLaw d n) (fun x => f (x i)) =
      integral (gaussianVectorLaw d) f := by
  calc
    _ = integral ((gaussianSampleLaw d n).map (fun x => x i)) f :=
      (integral_map_of_stronglyMeasurable
        (measurable_pi_apply i) hf.stronglyMeasurable).symm
    _ = _ := by rw [gaussianRow_map]

/-- MGF of the squared standard Gaussian: `E[exp(tZ^2)] = (1-2t)^{-1/2}`
for `t < 1/2`, by completing the square against `integral_gaussian`. -/
theorem mgf_sq_gaussianReal {t : Real} (ht : t < 1 / 2) :
    integral (gaussianReal 0 1) (fun x => Real.exp (t * x ^ 2)) =
      1 / Real.sqrt (1 - 2 * t) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hmeas : AEMeasurable (gaussianPDF (0 : Real) 1) volume :=
    (ENNReal.continuous_ofReal.measurable.comp
      (measurable_gaussianPDFReal 0 1)).aemeasurable
  have htop : ∀ᵐ x ∂(volume : Measure Real),
      gaussianPDF (0 : Real) 1 x < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas htop]
  have hpt : ∀ x : Real, ((gaussianPDF (0 : Real) 1 x).toReal
      • Real.exp (t * x ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹
        * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    have hnn := gaussianPDFReal_nonneg (0 : Real) 1 x
    rw [gaussianPDF, ENNReal.toReal_ofReal hnn, smul_eq_mul,
      gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_const_mul, integral_gaussian]
  have hu : (0 : Real) < 1 - 2 * t := by linarith
  have h2t : (0 : Real) < 1 / 2 - t := by linarith
  have hA : (0 : Real) < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hBC : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t)
      = Real.sqrt (2 * Real.pi) := by
    have hsq : (Real.sqrt (Real.pi / (1 / 2 - t))
        * Real.sqrt (1 - 2 * t)) ^ 2
        = (Real.sqrt (2 * Real.pi)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg Real.pi_pos.le h2t.le),
        Real.sq_sqrt hu.le,
        Real.sq_sqrt (by positivity : (0 : Real) ≤ 2 * Real.pi)]
      field_simp
    exact (sq_eq_sq₀ (by positivity) hA.le).mp hsq
  have hA' : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hA
  have hC' : Real.sqrt (1 - 2 * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hB : Real.sqrt (Real.pi / (1 / 2 - t))
      = Real.sqrt (2 * Real.pi) / Real.sqrt (1 - 2 * t) := by
    rw [← hBC]
    field_simp
  rw [hB]
  field_simp

/-- The tilted exponential is integrable under the standard Gaussian
(the computed MGF value is nonzero, ruling out `integral_undef`). -/
theorem integrable_exp_sq_gaussianReal {t : Real} (ht : t < 1 / 2) :
    Integrable (fun x => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  by_contra hni
  have hval := mgf_sq_gaussianReal ht
  rw [integral_undef hni] at hval
  have hu : (0 : Real) < 1 - 2 * t := by linarith
  have hpos : (0 : Real) < 1 / Real.sqrt (1 - 2 * t) :=
    div_pos one_pos (Real.sqrt_pos.mpr hu)
  linarith

/-- Lintegral form of the squared-Gaussian MGF. -/
theorem lintegral_exp_sq_gaussianReal {t : Real} (ht : t < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x ^ 2)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (1 / Real.sqrt (1 - 2 * t)) := by
  have hint := integrable_exp_sq_gaussianReal ht
  have hnn : 0 ≤ᵐ[gaussianReal 0 1] (fun x => Real.exp (t * x ^ 2)) :=
    Filter.Eventually.of_forall fun x => Real.exp_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
    mgf_sq_gaussianReal ht]

/-- Chernoff tail for the squared standard Gaussian. -/
theorem chernoff_sq_gaussian {t u : Real} (ht0 : 0 < t) (ht : t < 1 / 2)
    (_hu : 0 ≤ u) :
    (gaussianReal 0 1) {x | u ≤ x ^ 2}
      ≤ ENNReal.ofReal (Real.exp (-t * u) / Real.sqrt (1 - 2 * t)) := by
  have hu2 : (0 : Real) < 1 - 2 * t := by linarith
  have hfm : AEMeasurable
      (fun x : Real => ENNReal.ofReal (Real.exp (t * x ^ 2)))
      (gaussianReal 0 1) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2)))).measurable.aemeasurable
  have he0 : ENNReal.ofReal (Real.exp (t * u)) ≠ 0 := by positivity
  have heTop : ENNReal.ofReal (Real.exp (t * u)) ≠ ∞ :=
    ne_of_lt ENNReal.ofReal_lt_top
  have hset : {x : Real | ENNReal.ofReal (Real.exp (t * u))
        ≤ ENNReal.ofReal (Real.exp (t * x ^ 2))} = {x | u ≤ x ^ 2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _),
      Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h ht0,
      fun h => mul_le_mul_of_nonneg_left h ht0.le⟩
  have hexp : Real.exp (t * u) ≠ 0 := (Real.exp_pos _).ne'
  have hsqrt : Real.sqrt (1 - 2 * t) ≠ 0 :=
    (Real.sqrt_pos.mpr hu2).ne'
  calc (gaussianReal 0 1) {x | u ≤ x ^ 2}
      = (gaussianReal 0 1) {x | ENNReal.ofReal (Real.exp (t * u))
          ≤ ENNReal.ofReal (Real.exp (t * x ^ 2))} := by rw [hset]
    _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (t * x ^ 2))
          ∂(gaussianReal 0 1))
          / ENNReal.ofReal (Real.exp (t * u)) :=
        meas_ge_le_lintegral_div hfm he0 heTop
    _ = ENNReal.ofReal (Real.exp (-t * u) / Real.sqrt (1 - 2 * t)) := by
        rw [lintegral_exp_sq_gaussianReal ht,
          ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
        congr 1
        rw [neg_mul, Real.exp_neg]
        field_simp

/-- Chi-square MGF: `E[exp(t‖x‖²)] = (1-2t)^{-d/2}` by coordinate
independence. -/
theorem mgf_normSq_gaussianVector {d : Nat} {t : Real} (ht : t < 1 / 2) :
    mgf (fun x : Vector d => ∑ j, (x j) ^ 2) (gaussianVectorLaw d) t
      = (1 / Real.sqrt (1 - 2 * t)) ^ d := by
  have hindep : iIndepFun (fun (j : Fin d) (x : Vector d) => (x j) ^ 2)
      (gaussianVectorLaw d) := by
    have h := (gaussianCoordinates_independent d).comp
      (fun _ : Fin d => (fun z : Real => z ^ 2))
      (fun _ => show Measurable (fun z : Real => z ^ 2)
        from measurable_id'.pow_const 2)
    exact h
  have hmeas : ∀ j : Fin d,
      Measurable (fun x : Vector d => (x j) ^ 2) :=
    fun j => (measurable_pi_apply j).pow_const 2
  have hsum : (∑ j ∈ Finset.univ, fun x : Vector d => (x j) ^ 2)
      = fun x : Vector d => ∑ j, (x j) ^ 2 := by
    funext x
    rw [Finset.sum_apply]
  have hsingle : ∀ j : Fin d,
      mgf (fun x : Vector d => (x j) ^ 2) (gaussianVectorLaw d) t
        = 1 / Real.sqrt (1 - 2 * t) := by
    intro j
    have hfm : Measurable (fun z : Real => Real.exp (t * z ^ 2)) :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2))).measurable
    calc mgf (fun x : Vector d => (x j) ^ 2) (gaussianVectorLaw d) t
        = integral (gaussianVectorLaw d)
          (fun x => (fun z : Real => Real.exp (t * z ^ 2)) (x j)) := rfl
      _ = integral (gaussianReal 0 1)
          (fun z => Real.exp (t * z ^ 2)) :=
          integral_gaussianCoordinate j _ hfm
      _ = 1 / Real.sqrt (1 - 2 * t) := mgf_sq_gaussianReal ht
  rw [← hsum, iIndepFun.mgf_sum hindep hmeas Finset.univ]
  rw [Finset.prod_congr rfl (fun j _ => hsingle j)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The chi-square exponential is integrable under the Gaussian vector
law, by independence plus the one-dimensional case. -/
theorem integrable_exp_normSq_gaussianVector {d : Nat} {t : Real}
    (ht : t < 1 / 2) :
    Integrable (fun x : Vector d => Real.exp (t * ∑ j, (x j) ^ 2))
      (gaussianVectorLaw d) := by
  have hindep : iIndepFun (fun (j : Fin d) (x : Vector d) => (x j) ^ 2)
      (gaussianVectorLaw d) := by
    have h := (gaussianCoordinates_independent d).comp
      (fun _ : Fin d => (fun z : Real => z ^ 2))
      (fun _ => show Measurable (fun z : Real => z ^ 2)
        from measurable_id'.pow_const 2)
    exact h
  have hmeas : ∀ j : Fin d,
      Measurable (fun x : Vector d => (x j) ^ 2) :=
    fun j => (measurable_pi_apply j).pow_const 2
  have hsum : (∑ j ∈ Finset.univ, fun x : Vector d => (x j) ^ 2)
      = fun x : Vector d => ∑ j, (x j) ^ 2 := by
    funext x
    rw [Finset.sum_apply]
  have h_int : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x : Vector d => Real.exp (t * (x j) ^ 2))
        (gaussianVectorLaw d) := by
    intro j _
    have hg := integrable_exp_sq_gaussianReal (t := t) ht
    have hf := gaussianCoordinate_measurePreserving (d := d) j
    have h := MeasurePreserving.integrable_comp_of_integrable hf hg
    exact h
  have h := hindep.integrable_exp_mul_sum hmeas (s := Finset.univ) h_int
  rw [hsum] at h
  exact h

/-- Lintegral form of the chi-square MGF. -/
theorem lintegral_exp_normSq_gaussianVector {d : Nat} {t : Real}
    (ht : t < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * ∑ j, (x j) ^ 2))
        ∂(gaussianVectorLaw d)
      = ENNReal.ofReal ((1 / Real.sqrt (1 - 2 * t)) ^ d) := by
  have hint := integrable_exp_normSq_gaussianVector (d := d) ht
  have hnn : 0 ≤ᵐ[gaussianVectorLaw d]
      (fun x : Vector d => Real.exp (t * ∑ j, (x j) ^ 2)) :=
    Filter.Eventually.of_forall fun x => Real.exp_nonneg _
  have hval : integral (gaussianVectorLaw d)
      (fun x : Vector d => Real.exp (t * ∑ j, (x j) ^ 2))
      = (1 / Real.sqrt (1 - 2 * t)) ^ d :=
    mgf_normSq_gaussianVector ht
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- Chernoff tail for the chi-square norm under the Gaussian vector law. -/
theorem chernoff_normSq_gaussianVector {d : Nat} {t v : Real}
    (ht0 : 0 < t) (ht : t < 1 / 2) (_hv : 0 ≤ v) :
    (gaussianVectorLaw d) {x | v ≤ ∑ j, (x j) ^ 2}
      ≤ ENNReal.ofReal
        (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
  have hcont : Continuous
      (fun x : Vector d => t * ∑ j, (x j) ^ 2) :=
    continuous_const.mul
      (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2)
  have hfm : AEMeasurable
      (fun x : Vector d =>
        ENNReal.ofReal (Real.exp (t * ∑ j, (x j) ^ 2)))
      (gaussianVectorLaw d) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp hcont)).measurable.aemeasurable
  have he0 : ENNReal.ofReal (Real.exp (t * v)) ≠ 0 := by positivity
  have heTop : ENNReal.ofReal (Real.exp (t * v)) ≠ ∞ :=
    ne_of_lt ENNReal.ofReal_lt_top
  have hset : {x : Vector d | ENNReal.ofReal (Real.exp (t * v))
        ≤ ENNReal.ofReal (Real.exp (t * ∑ j, (x j) ^ 2))}
      = {x | v ≤ ∑ j, (x j) ^ 2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _),
      Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h ht0,
      fun h => mul_le_mul_of_nonneg_left h ht0.le⟩
  have hexp : Real.exp (t * v) ≠ 0 := (Real.exp_pos _).ne'
  calc (gaussianVectorLaw d) {x | v ≤ ∑ j, (x j) ^ 2}
      = (gaussianVectorLaw d) {x | ENNReal.ofReal (Real.exp (t * v))
          ≤ ENNReal.ofReal (Real.exp (t * ∑ j, (x j) ^ 2))} := by rw [hset]
    _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (t * ∑ j, (x j) ^ 2))
          ∂(gaussianVectorLaw d))
          / ENNReal.ofReal (Real.exp (t * v)) :=
        meas_ge_le_lintegral_div hfm he0 heTop
    _ = ENNReal.ofReal
        (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
        rw [lintegral_exp_normSq_gaussianVector ht,
          ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
        congr 1
        rw [neg_mul, Real.exp_neg]
        field_simp

/-- Single-row chi-square Chernoff tail under the sample law. -/
theorem rowNormSq_single_tail {d n : Nat} (j : Fin n) {t v : Real}
    (ht0 : 0 < t) (ht : t < 1 / 2) (hv : 0 ≤ v) :
    (gaussianSampleLaw d n) {x | v < ∑ k, ((x j) k) ^ 2}
      ≤ ENNReal.ofReal
        (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
  have hmeas : MeasurableSet {z : Vector d | v < ∑ k, (z k) ^ 2} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun k _ =>
        (measurable_pi_apply k).pow_const 2)
  have hpre : {x : Sample d n | v < ∑ k, ((x j) k) ^ 2}
      = (fun x => x j) ⁻¹' {z : Vector d | v < ∑ k, (z k) ^ 2} := rfl
  rw [hpre, ← MeasureTheory.Measure.map_apply (measurable_pi_apply j)
    hmeas, gaussianRow_map j]
  have hsub : {z : Vector d | v < ∑ k, (z k) ^ 2}
      ⊆ {z : Vector d | v ≤ ∑ k, (z k) ^ 2} :=
    fun z hz => show v ≤ ∑ k, (z k) ^ 2 from le_of_lt hz
  exact le_trans (measure_mono hsub)
    (chernoff_normSq_gaussianVector ht0 ht hv)

/-- Union bound for large row norms (chi-square Chernoff per row). -/
theorem rowNormSq_union_tail {d n : Nat} {t v : Real} (ht0 : 0 < t)
    (ht : t < 1 / 2) (hv : 0 ≤ v) :
    ((gaussianSampleLaw d n)
        (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})).toReal
      ≤ (n : ℝ)
        * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
  have hbound_nn : (0 : ℝ)
      ≤ Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d :=
    mul_nonneg (Real.exp_nonneg _)
      (pow_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have hEj : ∀ j : Fin n,
      (gaussianSampleLaw d n) {x | v < ∑ k, ((x j) k) ^ 2}
        ≤ ENNReal.ofReal
          (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
    fun j => rowNormSq_single_tail j ht0 ht hv
  have hunion : (gaussianSampleLaw d n)
        (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})
      ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ENNReal.ofReal
          (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
    have h1 : (gaussianSampleLaw d n)
          (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})
        ≤ ∑' j : Fin n,
          (gaussianSampleLaw d n) {x | v < ∑ k, ((x j) k) ^ 2} :=
      measure_iUnion_le
        (fun j : Fin n => {x : Sample d n | v < ∑ k, ((x j) k) ^ 2})
    rw [tsum_fintype] at h1
    exact le_trans h1 (Finset.sum_le_sum fun j _ => hEj j)
  have hfin : (∑ j ∈ (Finset.univ : Finset (Fin n)),
      ENNReal.ofReal
        (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d)) ≠ ∞ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hbound_nn)]
    exact ENNReal.ofReal_ne_top
  calc ((gaussianSampleLaw d n)
          (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})).toReal
      ≤ (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ENNReal.ofReal
            (Real.exp (-t * v)
              * (1 / Real.sqrt (1 - 2 * t)) ^ d)).toReal :=
        ENNReal.toReal_mono hfin hunion
    _ = ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (ENNReal.ofReal
          (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d)).toReal :=
        ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)
    _ = ∑ _j ∈ (Finset.univ : Finset (Fin n)),
        (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
        Finset.sum_congr rfl fun j _ =>
          ENNReal.toReal_ofReal hbound_nn
    _ = (n : ℝ)
        * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GaussianEllipsoid
