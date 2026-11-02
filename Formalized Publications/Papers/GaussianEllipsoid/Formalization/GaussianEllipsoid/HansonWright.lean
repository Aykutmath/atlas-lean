import GaussianEllipsoid.RotAssemble
import GaussianEllipsoid.HuberDischarge
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.GaussianMoments
import GaussianEllipsoid.EllipticCorrect
import GaussianEllipsoid.BelowObjects
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix Topology

/-- Rotation invariance of the standard Gaussian vector law, as an explicit
hypothesis (the only unproved input of this file). -/
def hwROT : Prop :=
  ∀ (d : Nat) (Q : Matrix (Fin d) (Fin d) ℝ), Qᵀ * Q = 1 →
    Measure.map (fun x => Q *ᵥ x) (gaussianVectorLaw d) = gaussianVectorLaw d

/-- Hanson–Wright rate from the box upper edge. -/
def hwRate (hi : ℝ) : ℝ := min (1 / (16 * hi ^ 2)) (1 / (16 * hi))

theorem hwRate_pos {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) :
    0 < hwRate hi := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hle
  unfold hwRate
  apply lt_min
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos hhi 2))
  · exact div_pos (by norm_num) (mul_pos (by norm_num) hhi)

theorem hwRate_nonneg {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) :
    0 ≤ hwRate hi :=
  le_of_lt (hwRate_pos hlo hle)

/-- Order from squared order for nonnegative reals (manual, robust). -/
theorem hw_sq_le_to_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hcon
  have hlt : b < a := lt_of_not_ge hcon
  have hpos : (0 : ℝ) < (a - b) * (a + b) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  have hexp : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
  linarith [h, hpos, hexp]

/-- Key 1D estimate: `(1-2θ)·e^{2θ+8θ²} ≥ 1` for `|θ| ≤ 1/8`,
from `1+y ≤ e^y` plus polynomial identities. -/
theorem hw_key_exp {θ : ℝ} (hθ : |θ| ≤ 1 / 8) :
    1 ≤ (1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2) := by
  have hθhi : θ ≤ 1 / 8 := (abs_le.mp hθ).2
  have hD : (0 : ℝ) < 1 - 2 * θ := by linarith
  rcases le_total θ 0 with hneg | hpos0
  · have he : (2 * θ + 8 * θ ^ 2) + 1 ≤ Real.exp (2 * θ + 8 * θ ^ 2) :=
      Real.add_one_le_exp _
    have hmul : (1 - 2 * θ) * ((2 * θ + 8 * θ ^ 2) + 1)
        ≤ (1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2) :=
      mul_le_mul_of_nonneg_left he (le_of_lt hD)
    have hexpand : (1 - 2 * θ) * ((2 * θ + 8 * θ ^ 2) + 1)
        = 1 + (4 * θ ^ 2 - 16 * θ ^ 3) := by ring
    have h34 : (0 : ℝ) ≤ 4 * θ ^ 2 - 16 * θ ^ 3 := by
      have h1 : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
      have h3 : θ ^ 3 ≤ 0 := by
        calc θ ^ 3 = θ * θ ^ 2 := by ring
          _ ≤ 0 * θ ^ 2 := mul_le_mul_of_nonneg_right hneg (sq_nonneg θ)
          _ = 0 := zero_mul _
      linarith [h1, h3]
    calc (1 : ℝ) = 1 + 0 := by ring
      _ ≤ 1 + (4 * θ ^ 2 - 16 * θ ^ 3) := by linarith [h34]
      _ = (1 - 2 * θ) * ((2 * θ + 8 * θ ^ 2) + 1) := hexpand.symm
      _ ≤ (1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2) := hmul
  · have he1 : (1 : ℝ) + θ ≤ Real.exp θ := by
      have h := Real.add_one_le_exp θ
      linarith
    have he2 : (1 : ℝ) + 8 * θ ^ 2 ≤ Real.exp (8 * θ ^ 2) := by
      have h := Real.add_one_le_exp (8 * θ ^ 2)
      linarith
    have hsq : (1 + θ) ^ 2 ≤ (Real.exp θ) ^ 2 := by
      have hP : (0 : ℝ)
          ≤ (Real.exp θ - (1 + θ)) * (Real.exp θ + (1 + θ)) :=
        mul_nonneg (sub_nonneg.mpr he1)
          (add_nonneg (Real.exp_nonneg θ) (by linarith))
      have hexp : (Real.exp θ - (1 + θ)) * (Real.exp θ + (1 + θ))
          = (Real.exp θ) ^ 2 - (1 + θ) ^ 2 := by ring
      linarith [hP, hexp]
    have hexp2 : Real.exp (2 * θ + 8 * θ ^ 2)
        = (Real.exp θ) ^ 2 * Real.exp (8 * θ ^ 2) := by
      have e1 : (Real.exp θ) ^ 2 = Real.exp (2 * θ) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      calc Real.exp (2 * θ + 8 * θ ^ 2)
          = Real.exp (2 * θ) * Real.exp (8 * θ ^ 2) := by rw [Real.exp_add]
        _ = (Real.exp θ) ^ 2 * Real.exp (8 * θ ^ 2) := by rw [e1]
    have hprod : ((1 + θ) ^ 2) * (1 + 8 * θ ^ 2)
        ≤ (Real.exp θ) ^ 2 * Real.exp (8 * θ ^ 2) := by
      have hc : (0 : ℝ) ≤ 1 + 8 * θ ^ 2 := by
        have h := sq_nonneg θ
        linarith
      calc ((1 + θ) ^ 2) * (1 + 8 * θ ^ 2)
          ≤ (Real.exp θ) ^ 2 * (1 + 8 * θ ^ 2) :=
            mul_le_mul_of_nonneg_right hsq hc
        _ ≤ (Real.exp θ) ^ 2 * Real.exp (8 * θ ^ 2) :=
            mul_le_mul_of_nonneg_left he2 (sq_nonneg _)
    have hchain : (1 - 2 * θ) * (((1 + θ) ^ 2) * (1 + 8 * θ ^ 2))
        ≤ (1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2) := by
      rw [hexp2]
      exact mul_le_mul_of_nonneg_left hprod (le_of_lt hD)
    have hexpand : (1 - 2 * θ) * (((1 + θ) ^ 2) * (1 + 8 * θ ^ 2)) - 1
        = θ ^ 2 * (5 - 2 * θ - 24 * θ ^ 2 - 16 * θ ^ 3) := by ring
    have hA : θ ^ 2 ≤ θ / 8 := by
      have hp : (0 : ℝ) ≤ θ * (1 / 8 - θ) := mul_nonneg hpos0 (by linarith)
      have he : θ / 8 - θ ^ 2 = θ * (1 / 8 - θ) := by ring
      linarith [hp, he]
    have hB : θ ^ 3 ≤ θ ^ 2 / 8 := by
      have hle : θ * θ ^ 2 ≤ (1 / 8) * θ ^ 2 :=
        mul_le_mul_of_nonneg_right hθhi (sq_nonneg θ)
      have he : θ ^ 3 = θ * θ ^ 2 := by ring
      have he2 : θ ^ 2 / 8 = (1 / 8) * θ ^ 2 := by ring
      linarith [hle, he, he2]
    have hinner : (0 : ℝ) ≤ 5 - 2 * θ - 24 * θ ^ 2 - 16 * θ ^ 3 := by
      have h2 : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
      linarith [hA, hB, hθhi, hpos0, h2]
    have hnn : (0 : ℝ) ≤ θ ^ 2 * (5 - 2 * θ - 24 * θ ^ 2 - 16 * θ ^ 3) :=
      mul_nonneg (sq_nonneg θ) hinner
    calc (1 : ℝ) = 1 + 0 := by ring
      _ ≤ 1 + (θ ^ 2 * (5 - 2 * θ - 24 * θ ^ 2 - 16 * θ ^ 3)) := by
          linarith [hnn]
      _ = (1 - 2 * θ) * (((1 + θ) ^ 2) * (1 + 8 * θ ^ 2)) := by
          linarith [hexpand]
      _ ≤ (1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2) := hchain

/-- 1D centered chi-square MGF bound. -/
theorem hw_mgf_centered_sq {θ : ℝ} (hθ : |θ| ≤ 1 / 8) :
    ∫ x, Real.exp (θ * (x ^ 2 - 1)) ∂(gaussianReal 0 1)
      ≤ Real.exp (4 * θ ^ 2) := by
  have hθhi : θ ≤ 1 / 8 := (abs_le.mp hθ).2
  have h12 : θ < 1 / 2 := by linarith
  have hD : (0 : ℝ) < 1 - 2 * θ := by linarith
  have hval : ∫ x, Real.exp (θ * (x ^ 2 - 1)) ∂(gaussianReal 0 1)
      = Real.exp (-θ) * (1 / Real.sqrt (1 - 2 * θ)) := by
    have hpt : ∀ x : ℝ, Real.exp (θ * (x ^ 2 - 1))
        = Real.exp (-θ) * Real.exp (θ * x ^ 2) := by
      intro x
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [hpt, integral_const_mul, mgf_sq_gaussianReal (t := θ) h12,
      one_div]
  have hkey := hw_key_exp hθ
  have hle : (Real.exp (-θ) * (1 / Real.sqrt (1 - 2 * θ))) ^ 2
      ≤ (Real.exp (4 * θ ^ 2)) ^ 2 := by
    have hsq : Real.sqrt (1 - 2 * θ) ^ 2 = 1 - 2 * θ :=
      Real.sq_sqrt (le_of_lt hD)
    have e1 : (Real.exp (-θ)) ^ 2 = Real.exp (-2 * θ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have e2 : (Real.exp (4 * θ ^ 2)) ^ 2 = Real.exp (8 * θ ^ 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-2 * θ) ≤ (1 - 2 * θ) * Real.exp (8 * θ ^ 2) := by
      have hm := mul_le_mul_of_nonneg_right hkey (Real.exp_nonneg (-2 * θ))
      have r1 : (1 : ℝ) * Real.exp (-2 * θ) = Real.exp (-2 * θ) := one_mul _
      have r2 : ((1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2)) * Real.exp (-2 * θ)
          = (1 - 2 * θ) * Real.exp (8 * θ ^ 2) := by
        have ee : Real.exp (2 * θ + 8 * θ ^ 2) * Real.exp (-2 * θ)
            = Real.exp (8 * θ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc ((1 - 2 * θ) * Real.exp (2 * θ + 8 * θ ^ 2)) * Real.exp (-2 * θ)
            = (1 - 2 * θ)
              * (Real.exp (2 * θ + 8 * θ ^ 2) * Real.exp (-2 * θ)) := by ring
          _ = (1 - 2 * θ) * Real.exp (8 * θ ^ 2) := by rw [ee]
      rw [r1, r2] at hm
      exact hm
    calc (Real.exp (-θ) * (1 / Real.sqrt (1 - 2 * θ))) ^ 2
        = Real.exp (-2 * θ) / (1 - 2 * θ) := by
          rw [mul_pow, e1, one_div, inv_pow, hsq, ← div_eq_mul_inv]
      _ ≤ Real.exp (8 * θ ^ 2) := by
          rw [div_le_iff₀ hD]
          calc Real.exp (-2 * θ) ≤ (1 - 2 * θ) * Real.exp (8 * θ ^ 2) := h2
            _ = Real.exp (8 * θ ^ 2) * (1 - 2 * θ) := by ring
      _ = (Real.exp (4 * θ ^ 2)) ^ 2 := e2.symm
  have ha : (0 : ℝ) ≤ Real.exp (-θ) * (1 / Real.sqrt (1 - 2 * θ)) :=
    mul_nonneg (Real.exp_nonneg _)
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hb : (0 : ℝ) ≤ Real.exp (4 * θ ^ 2) := Real.exp_nonneg _
  rw [hval]
  exact hw_sq_le_to_le ha hb hle

/-- Quadratic form as a trace against the rank-one matrix. -/
theorem hw_quad_eq_trace {d : ℕ} (S : Square d) (z : Vector d) :
    quadratic S z = (S * Matrix.vecMulVec z z).trace := by
  unfold quadratic
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rank-one quadratic form is a squared inner product. -/
theorem hw_quad_vecMulVec {d : ℕ} (z v : Vector d) :
    quadratic (Matrix.vecMulVec z z) v = (v ⬝ᵥ z) ^ 2 := by
  have hcomm : z ⬝ᵥ v = v ⬝ᵥ z := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hEv : (Matrix.vecMulVec z z *ᵥ v) = fun i => z i * (z ⬝ᵥ v) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfactor : (∑ i ∈ Finset.univ, v i * (z i * (z ⬝ᵥ v)))
      = (v ⬝ᵥ z) * (z ⬝ᵥ v) := by
    have h1 : (∑ i ∈ Finset.univ, v i * (z i * (z ⬝ᵥ v)))
        = (∑ i ∈ Finset.univ, (v i * z i)) * (z ⬝ᵥ v) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1]
    have hconv : (∑ i ∈ Finset.univ, (v i * z i)) = (v ⬝ᵥ z) := by
      simp [dotProduct]
    rw [hconv]
  unfold quadratic
  rw [hEv]
  trans ∑ i ∈ Finset.univ, v i * (z i * (z ⬝ᵥ v))
  · show (∑ i, v i * (z i * (z ⬝ᵥ v)))
        = ∑ i ∈ Finset.univ, v i * (z i * (z ⬝ᵥ v))
    have hconv2 : (∑ i, v i * (z i * (z ⬝ᵥ v)))
        = ∑ i ∈ Finset.univ, v i * (z i * (z ⬝ᵥ v)) := by simp
    rw [hconv2]
  · rw [hfactor, hcomm, pow_two]

/-- Generic Chernoff bound from an MGF upper bound. -/
theorem hw_chernoff {d : ℕ} {Y : Vector d → ℝ} (hYc : Continuous Y)
    {φ u B : ℝ} (hφ : 0 < φ)
    (hint : Integrable (fun z => Real.exp (φ * Y z)) (gaussianVectorLaw d))
    (hmgf : ∫ z, Real.exp (φ * Y z) ∂(gaussianVectorLaw d) ≤ B) :
    (gaussianVectorLaw d) {z | u ≤ Y z}
      ≤ ENNReal.ofReal (Real.exp (-φ * u) * B) := by
  have hcont : Continuous (fun z : Vector d => φ * Y z) :=
    continuous_const.mul hYc
  have hfm : AEMeasurable
      (fun z : Vector d => ENNReal.ofReal (Real.exp (φ * Y z)))
      (gaussianVectorLaw d) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp hcont)).measurable.aemeasurable
  have he0 : ENNReal.ofReal (Real.exp (φ * u)) ≠ 0 := by positivity
  have heTop : ENNReal.ofReal (Real.exp (φ * u)) ≠ ∞ :=
    ne_of_lt ENNReal.ofReal_lt_top
  have hset : {z : Vector d |
        ENNReal.ofReal (Real.exp (φ * u))
          ≤ ENNReal.ofReal (Real.exp (φ * Y z))}
      = {z | u ≤ Y z} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _), Real.exp_le_exp]
    exact ⟨fun h => le_of_mul_le_mul_left h hφ,
      fun h => mul_le_mul_of_nonneg_left h hφ.le⟩
  have hlin : (∫⁻ z, ENNReal.ofReal (Real.exp (φ * Y z))
      ∂(gaussianVectorLaw d))
      ≤ ENNReal.ofReal B := by
    have hnn : 0 ≤ᵐ[gaussianVectorLaw d] (fun z => Real.exp (φ * Y z)) :=
      Filter.Eventually.of_forall fun z => Real.exp_nonneg _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_le_ofReal hmgf
  calc (gaussianVectorLaw d) {z | u ≤ Y z}
      = (gaussianVectorLaw d) {z |
          ENNReal.ofReal (Real.exp (φ * u))
            ≤ ENNReal.ofReal (Real.exp (φ * Y z))} := by rw [hset]
    _ ≤ (∫⁻ z, ENNReal.ofReal (Real.exp (φ * Y z))
          ∂(gaussianVectorLaw d))
          / ENNReal.ofReal (Real.exp (φ * u)) :=
        meas_ge_le_lintegral_div hfm he0 heTop
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal (Real.exp (φ * u)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right hlin ?_
        apply zero_le
    _ = ENNReal.ofReal (Real.exp (-φ * u) * B) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
        congr 1
        rw [neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm]

/-- Fixed-matrix Hanson–Wright tail (from ROT). -/
theorem hw_fixed_tail {d : ℕ} (S : Square d) {lo hi : ℝ}
    (hS : S ∈ spectralBox d lo hi) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hROT : hwROT) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianVectorLaw d)
        {z | t < |(quadratic S z - S.trace) / Real.sqrt (d : ℝ)|}
      ≤ ENNReal.ofReal
        (2 * Real.exp (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hle
  have hRate0 : 0 ≤ hwRate hi := hwRate_nonneg hlo hle
  have hRate_le1 : hwRate hi ≤ 1 / (16 * hi ^ 2) := by
    unfold hwRate
    apply min_le_left
  have hRate_le2 : hwRate hi ≤ 1 / (16 * hi) := by
    unfold hwRate
    apply min_le_right
  by_cases hd0 : d = 0
  · subst hd0
    have hempty : {z : Vector 0 |
          t < |(quadratic S z - S.trace) / Real.sqrt ((0 : ℕ) : ℝ)|} = ∅ := by
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, abs_zero]
      exact Set.eq_empty_iff_forall_notMem.mpr (fun z hz => by
        simp only [Set.mem_ofPred_eq] at hz
        linarith [ht])
    rw [hempty, measure_empty]
    apply zero_le
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
  have hsqpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  set u : ℝ := t * Real.sqrt (d : ℝ) with hu_def
  have hu : 0 ≤ u := mul_nonneg ht (Real.sqrt_nonneg _)
  set hH : S.IsHermitian := isHermitian_of_mem_box hS with hhH
  set U : Square d := ↑hH.eigenvectorUnitary with hUdef
  set Q : Square d := Uᵀ with hQdef
  set F2 : ℝ := ∑ i ∈ Finset.univ, (hH.eigenvalues i) ^ 2 with hF2def
  have hmemfree : ∀ (f : Fin d → ℝ),
      (∑ i ∈ Finset.univ, f i) = ∑ i, f i := by
    intro f
    simp
  have hle : ∀ i : Fin d, hH.eigenvalues i ≤ hi := fun i => by
    rw [hhH]
    exact eigenvalues_le_of_mem_box hS i
  have hge : ∀ i : Fin d, lo ≤ hH.eigenvalues i := fun i => by
    rw [hhH]
    exact eigenvalues_ge_of_mem_box hS i
  have htr : S.trace = ∑ j, hH.eigenvalues j := by
    rw [hhH]
    exact trace_eq_sum_eigenvalues_box hS
  have habs : ∀ i : Fin d, |hH.eigenvalues i| ≤ hi := by
    intro i
    rw [abs_le]
    constructor
    · have h1 := hge i
      linarith [h1, hlo, hhi]
    · exact hle i
  have hF2nn : 0 ≤ F2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF2le : F2 ≤ (d : ℝ) * hi ^ 2 := by
    have hterm : ∀ i : Fin d, (hH.eigenvalues i) ^ 2 ≤ hi ^ 2 := by
      intro i
      have hP : (0 : ℝ)
          ≤ (hi - hH.eigenvalues i) * (hi + hH.eigenvalues i) :=
        mul_nonneg (by linarith [hle i]) (by linarith [hge i, hlo, hhi])
      have hexp : (hi - hH.eigenvalues i) * (hi + hH.eigenvalues i)
          = hi ^ 2 - (hH.eigenvalues i) ^ 2 := by ring
      linarith [hP, hexp]
    calc F2 = ∑ i ∈ Finset.univ, (hH.eigenvalues i) ^ 2 := hF2def
      _ ≤ ∑ _i ∈ Finset.univ, hi ^ 2 :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (d : ℝ) * hi ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hcol : ∀ i l : Fin d, U l i = ⇑(hH.eigenvectorBasis i) l :=
    fun i l => hH.eigenvectorUnitary_apply l i
  have hspec : ∀ z : Vector d, quadratic S z - S.trace
      = ∑ i ∈ Finset.univ,
        hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1) := by
    intro z
    have hexpand :=
      trace_hermitian_mul_expand (S := S) (E := Matrix.vecMulVec z z) hH
    have hq := hw_quad_eq_trace S z
    have hQapply : ∀ i : Fin d, (Q *ᵥ z) i
        = (⇑(hH.eigenvectorBasis i) : Vector d) ⬝ᵥ z := by
      intro i
      rw [hQdef]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hcol i j]
    have hterm : ∀ i : Fin d,
        hH.eigenvalues i
            * quadratic (Matrix.vecMulVec z z) ⇑(hH.eigenvectorBasis i)
          - hH.eigenvalues i
        = hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1) := by
      intro i
      have hqi : quadratic (Matrix.vecMulVec z z) ⇑(hH.eigenvectorBasis i)
          = ((Q *ᵥ z) i) ^ 2 := by
        rw [hw_quad_vecMulVec, hQapply i]
      rw [hqi]
      ring
    calc quadratic S z - S.trace
        = (∑ i ∈ Finset.univ, hH.eigenvalues i
            * quadratic (Matrix.vecMulVec z z) ⇑(hH.eigenvectorBasis i))
          - (∑ i ∈ Finset.univ, hH.eigenvalues i) := by
          rw [hq, hexpand, htr]
          try simp only [hmemfree]
      _ = ∑ i ∈ Finset.univ, (hH.eigenvalues i
            * quadratic (Matrix.vecMulVec z z) ⇑(hH.eigenvectorBasis i)
          - hH.eigenvalues i) := by rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.univ,
            hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
  have hQorth : Qᵀ * Q = 1 := by
    have hUU : U * star U = 1 := by
      rw [hUdef]
      exact Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.property
    have hstar : star U = Uᵀ := by
      ext a b
      rw [Matrix.star_apply, Matrix.transpose_apply]
      apply star_trivial
    calc Qᵀ * Q = U * star U := by
          rw [hQdef, Matrix.transpose_transpose, ← hstar]
      _ = 1 := hUU
  have hQmeas : Measurable (fun z : Vector d => Q *ᵥ z) :=
    (((show Continuous fun _ : Vector d => Q from continuous_const).matrix_mulVec
      continuous_id)).measurable
  have hmap : Measure.map (fun z : Vector d => Q *ᵥ z) (gaussianVectorLaw d)
      = gaussianVectorLaw d :=
    hROT d Q hQorth
  have hindep : iIndepFun
      (fun (i : Fin d) (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
      (gaussianVectorLaw d) :=
    (gaussianCoordinates_independent d).comp
      (fun (i : Fin d) (z : ℝ) => hH.eigenvalues i * (z ^ 2 - 1))
      (fun (i : Fin d) => (continuous_const.mul
        ((continuous_id.pow 2).sub continuous_const)).measurable)
  have hmeas : ∀ (i : Fin d),
      Measurable
        (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1)) := by
    intro i
    exact measurable_const.mul
      (((measurable_pi_apply i).pow_const 2).sub measurable_const)
  have hsum : (∑ i ∈ Finset.univ,
        fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
      = fun w => ∑ i ∈ Finset.univ,
        hH.eigenvalues i * ((w i) ^ 2 - 1) := by
    funext w
    rw [Finset.sum_apply]
  have hφlam : ∀ (φ : ℝ), |φ| ≤ 1 / (8 * hi) →
      ∀ (i : Fin d), |φ * hH.eigenvalues i| ≤ 1 / 8 := by
    intro φ hφ i
    have h1 : |φ| * |hH.eigenvalues i| ≤ (1 / (8 * hi)) * hi := by
      have h8hi : (0 : ℝ) ≤ 1 / (8 * hi) :=
        one_div_nonneg.mpr (le_of_lt (mul_pos (by norm_num) hhi))
      calc |φ| * |hH.eigenvalues i|
          ≤ (1 / (8 * hi)) * |hH.eigenvalues i| :=
            mul_le_mul_of_nonneg_right hφ (abs_nonneg _)
        _ ≤ (1 / (8 * hi)) * hi :=
            mul_le_mul_of_nonneg_left (habs i) h8hi
    have h2 : (1 / (8 * hi)) * hi = 1 / 8 := by
      have hhi' : hi ≠ 0 := ne_of_gt hhi
      have h8hi : (8 : ℝ) * hi ≠ 0 := mul_ne_zero (by norm_num) hhi'
      field_simp
      try ring
    calc |φ * hH.eigenvalues i| = |φ| * |hH.eigenvalues i| := abs_mul _ _
      _ ≤ (1 / (8 * hi)) * hi := h1
      _ = 1 / 8 := h2
  have hsingle : ∀ (i : Fin d) (φ : ℝ),
      mgf (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
        (gaussianVectorLaw d) φ
      = ∫ t, Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1))
        ∂(gaussianReal 0 1) := by
    intro i φ
    have hfm : Measurable
        (fun t : ℝ => Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1))) :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((continuous_id.pow 2).sub continuous_const))).measurable
    calc mgf (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
          (gaussianVectorLaw d) φ
        = ∫ w, Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1)))
            ∂(gaussianVectorLaw d) := rfl
      _ = ∫ w, (fun t : ℝ =>
            Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1))) (w i)
            ∂(gaussianVectorLaw d) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun w => by
            show Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1)))
              = Real.exp ((φ * hH.eigenvalues i) * ((w i) ^ 2 - 1))
            congr 1
            ring)
      _ = ∫ t, Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1))
            ∂(gaussianReal 0 1) :=
          integral_gaussianCoordinate i _ hfm
  have hprod : ∀ (φ : ℝ), |φ| ≤ 1 / (8 * hi) →
      mgf (fun (w : Vector d) =>
          ∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1))
        (gaussianVectorLaw d) φ
        ≤ Real.exp (4 * φ ^ 2 * F2) := by
    intro φ hφ
    have hmgf := iIndepFun.mgf_sum hindep hmeas Finset.univ (t := φ)
    have hle : ∀ i ∈ Finset.univ,
        mgf (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
          (gaussianVectorLaw d) φ
          ≤ Real.exp (4 * (φ * hH.eigenvalues i) ^ 2) := by
      intro i _
      rw [hsingle i φ]
      exact hw_mgf_centered_sq (hφlam φ hφ i)
    have hnn : ∀ i ∈ Finset.univ, (0 : ℝ) ≤
        mgf (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
          (gaussianVectorLaw d) φ := by
      intro i _
      show (0 : ℝ) ≤ ∫ w, Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1)))
        ∂(gaussianVectorLaw d)
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun w => Real.exp_nonneg _)
    calc mgf (fun (w : Vector d) =>
            ∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1))
          (gaussianVectorLaw d) φ
        = ∏ i ∈ Finset.univ,
            mgf (fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1))
              (gaussianVectorLaw d) φ := by
          rw [← hsum]
          exact hmgf
      _ ≤ ∏ i ∈ Finset.univ, Real.exp (4 * (φ * hH.eigenvalues i) ^ 2) :=
          Finset.prod_le_prod hnn hle
      _ = Real.exp (4 * φ ^ 2 * F2) := by
          rw [← Real.exp_sum]
          congr 1
          have hterm : ∀ i : Fin d,
              4 * (φ * hH.eigenvalues i) ^ 2
                = (4 * φ ^ 2) * (hH.eigenvalues i) ^ 2 := by
            intro i
            ring
          simp only [hterm]
          rw [← Finset.mul_sum, hF2def]
  have hMGF : ∀ (φ : ℝ), |φ| ≤ 1 / (8 * hi) →
      ∫ z, Real.exp (φ * (quadratic S z - S.trace)) ∂(gaussianVectorLaw d)
        ≤ Real.exp (4 * φ ^ 2 * F2) := by
    intro φ hφ
    have hYcont : Continuous
        (fun (w : Vector d) =>
          ∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1)) := by
      apply continuous_finsetSum
      intro i _
      exact continuous_const.mul
        (((continuous_apply i).pow 2).sub continuous_const)
    have hg : StronglyMeasurable
        (fun (w : Vector d) =>
          Real.exp
            (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1)))) :=
      (Real.continuous_exp.comp
        (continuous_const.mul hYcont)).measurable.stronglyMeasurable
    have hpt : ∀ z : Vector d, φ * (quadratic S z - S.trace)
        = φ * (∑ i ∈ Finset.univ,
          hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1)) := by
      intro z
      rw [hspec z]
    calc ∫ z, Real.exp (φ * (quadratic S z - S.trace)) ∂(gaussianVectorLaw d)
        = ∫ z, (fun (w : Vector d) =>
            Real.exp
              (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1))))
            (Q *ᵥ z)
            ∂(gaussianVectorLaw d) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z => by
            show Real.exp (φ * (quadratic S z - S.trace))
              = Real.exp
                (φ * (∑ i ∈ Finset.univ,
                  hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1)))
            rw [hpt z])
      _ = ∫ w, Real.exp
            (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1)))
            ∂(Measure.map (fun z : Vector d => Q *ᵥ z)
              (gaussianVectorLaw d)) := by
          exact (integral_map hQmeas.aemeasurable hg.aestronglyMeasurable).symm
      _ = ∫ w, Real.exp
            (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1)))
            ∂(gaussianVectorLaw d) := by
          rw [hmap]
      _ ≤ Real.exp (4 * φ ^ 2 * F2) := hprod φ hφ
  have hInt : ∀ (φ : ℝ), |φ| ≤ 1 / (8 * hi) →
      Integrable
        (fun (z : Vector d) => Real.exp (φ * (quadratic S z - S.trace)))
        (gaussianVectorLaw d) := by
    intro φ hφ
    have h1 : ∀ i ∈ Finset.univ,
        Integrable
          (fun (w : Vector d) =>
            Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1))))
          (gaussianVectorLaw d) := by
      intro i _
      have hθ : φ * hH.eigenvalues i < 1 / 2 := by
        have h := hφlam φ hφ i
        have h2 := abs_le.mp h
        linarith [h2.1, h2.2]
      have hgR : Integrable
          (fun (t : ℝ) => Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1)))
          (gaussianReal 0 1) := by
        have hbase :=
          integrable_exp_sq_gaussianReal (t := φ * hH.eigenvalues i) hθ
        have hpt : (fun (t : ℝ) =>
              Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1)))
            = fun t => Real.exp (-(φ * hH.eigenvalues i))
              * Real.exp ((φ * hH.eigenvalues i) * t ^ 2) := by
          funext t
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hpt]
        exact hbase.const_mul (c := Real.exp (-(φ * hH.eigenvalues i)))
      have hmp := gaussianCoordinate_measurePreserving i
      have heq : (fun (w : Vector d) =>
            Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1))))
          = (fun (t : ℝ) => Real.exp ((φ * hH.eigenvalues i) * (t ^ 2 - 1)))
            ∘ (fun (w : Vector d) => w i) := by
        funext w
        show Real.exp (φ * (hH.eigenvalues i * ((w i) ^ 2 - 1)))
          = Real.exp ((φ * hH.eigenvalues i) * ((w i) ^ 2 - 1))
        congr 1
        ring
      rw [heq]
      exact MeasurePreserving.integrable_comp_of_integrable hmp hgR
    have h2 := hindep.integrable_exp_mul_sum hmeas (s := Finset.univ) h1
    have h3 : Integrable
        (fun (w : Vector d) =>
          Real.exp
            (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1))))
        (gaussianVectorLaw d) := by
      have h2' : (fun (ω : Vector d) => Real.exp (φ *
            ((∑ i ∈ Finset.univ,
              fun (w : Vector d) => hH.eigenvalues i * ((w i) ^ 2 - 1)) ω)))
          = fun (w : Vector d) =>
            Real.exp
              (φ * (∑ i ∈ Finset.univ,
                hH.eigenvalues i * ((w i) ^ 2 - 1))) := by
        funext ω
        rw [Finset.sum_apply]
      rw [← h2']
      exact h2
    have hQmp : MeasurePreserving (fun (z : Vector d) => Q *ᵥ z)
        (gaussianVectorLaw d) (gaussianVectorLaw d) := by
      have h0 : MeasurePreserving (fun (z : Vector d) => Q *ᵥ z)
          (gaussianVectorLaw d)
          (Measure.map (fun (z : Vector d) => Q *ᵥ z)
            (gaussianVectorLaw d)) :=
        ⟨hQmeas, rfl⟩
      rwa [hmap] at h0
    have hcomp := MeasurePreserving.integrable_comp_of_integrable hQmp h3
    have heq : (fun (z : Vector d) =>
          Real.exp (φ * (quadratic S z - S.trace)))
        = (fun (w : Vector d) =>
            Real.exp
              (φ * (∑ i ∈ Finset.univ, hH.eigenvalues i * ((w i) ^ 2 - 1))))
          ∘ (fun (z : Vector d) => Q *ᵥ z) := by
      funext z
      show Real.exp (φ * (quadratic S z - S.trace))
        = Real.exp (φ * (∑ i ∈ Finset.univ,
          hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1)))
      rw [hspec z]
    rw [heq]
    exact hcomp
  have hquadS : Continuous (quadratic S) := by
    have heq : quadratic S
        = fun v => ∑ i ∈ Finset.univ, (v i * (S *ᵥ v) i) := by
      unfold quadratic
      funext v
      simp only [dotProduct, hmemfree]
    rw [heq]
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).mul ((continuous_apply i).comp
      ((show Continuous fun _ : Vector d => S from continuous_const).matrix_mulVec
        continuous_id)))
  have hYcont : Continuous (fun (z : Vector d) => quadratic S z - S.trace) :=
    hquadS.sub continuous_const
  have hsub : {z : Vector d |
        t < |(quadratic S z - S.trace) / Real.sqrt (d : ℝ)|}
      ⊆ {z | u ≤ |quadratic S z - S.trace|} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have habs : |(quadratic S z - S.trace) / Real.sqrt (d : ℝ)|
        = |quadratic S z - S.trace| / Real.sqrt (d : ℝ) := by
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [habs, lt_div_iff₀ hsqpos] at hz
    rw [hu_def]
    exact le_of_lt hz
  by_cases hu0 : u = 0
  · have hmul0 : t * Real.sqrt (d : ℝ) = 0 := by
      rw [← hu_def]
      exact hu0
    have ht0 : t = 0 :=
      (mul_eq_zero.mp hmul0).resolve_right (ne_of_gt hsqpos)
    have hmin0 : min (t ^ 2) (t * Real.sqrt (d : ℝ)) = 0 := by
      rw [ht0, zero_pow two_ne_zero, zero_mul, min_self]
    calc (gaussianVectorLaw d)
          {z | t < |(quadratic S z - S.trace) / Real.sqrt (d : ℝ)|}
        ≤ 1 := by apply prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by norm_num)
      _ = ENNReal.ofReal
          (2 * Real.exp
            (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) := by
          rw [hmin0, mul_zero, Real.exp_zero, mul_one]
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  by_cases hF0 : F2 = 0
  · have hlam0 : ∀ i : Fin d, hH.eigenvalues i = 0 := by
      intro i
      have h1 : (hH.eigenvalues i) ^ 2
          ≤ ∑ j ∈ Finset.univ, (hH.eigenvalues j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [← hF2def, hF0] at h1
      have hsq0 : (hH.eigenvalues i) ^ 2 = 0 :=
        le_antisymm h1 (sq_nonneg _)
      have hmul0 : hH.eigenvalues i * hH.eigenvalues i = 0 := by
        rw [← pow_two]
        exact hsq0
      rcases mul_eq_zero.mp hmul0 with h | h <;> exact h
    have hY0 : ∀ z : Vector d, quadratic S z - S.trace = 0 := by
      intro z
      rw [hspec z]
      have hzero : (∑ i ∈ Finset.univ,
            hH.eigenvalues i * (((Q *ᵥ z) i) ^ 2 - 1)) = 0 := by
        rw [← Finset.sum_const_zero (s := Finset.univ (α := Fin d))]
        apply Finset.sum_congr rfl
        intro i _
        rw [hlam0 i, zero_mul]
      rw [hzero]
    have hempty : {z : Vector d | u ≤ |quadratic S z - S.trace|} = ∅ := by
      simp only [hY0, abs_zero]
      exact Set.eq_empty_iff_forall_notMem.mpr (fun z hz => by
        simp only [Set.mem_ofPred_eq] at hz
        linarith [hupos])
    calc (gaussianVectorLaw d)
          {z | t < |(quadratic S z - S.trace) / Real.sqrt (d : ℝ)|}
        ≤ (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|} :=
          measure_mono hsub
      _ = 0 := by rw [hempty, measure_empty]
      _ ≤ ENNReal.ofReal
          (2 * Real.exp
            (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) := by
          apply zero_le
  have hF2pos : 0 < F2 := lt_of_le_of_ne hF2nn (Ne.symm hF0)
  set φ : ℝ := min (u / (8 * F2)) (1 / (8 * hi)) with hφdef
  have hφpos : 0 < φ :=
    lt_min (div_pos hupos (mul_pos (by norm_num) hF2pos))
      (div_pos one_pos (mul_pos (by norm_num) hhi))
  have hφbound : |φ| ≤ 1 / (8 * hi) := by
    rw [abs_of_nonneg (le_of_lt hφpos)]
    apply min_le_right
  have hcherY : (gaussianVectorLaw d) {z | u ≤ quadratic S z - S.trace}
      ≤ ENNReal.ofReal (Real.exp (-φ * u) * Real.exp (4 * φ ^ 2 * F2)) :=
    hw_chernoff hYcont hφpos (hInt φ hφbound) (hMGF φ hφbound)
  have hNYcont : Continuous
      (fun (z : Vector d) => -(quadratic S z - S.trace)) :=
    hYcont.neg
  have hintN : Integrable
      (fun (z : Vector d) => Real.exp (φ * (-(quadratic S z - S.trace))))
      (gaussianVectorLaw d) := by
    have heq : (fun (z : Vector d) =>
          Real.exp (φ * (-(quadratic S z - S.trace))))
        = fun z => Real.exp ((-φ) * (quadratic S z - S.trace)) := by
      funext z
      congr 1
      ring
    rw [heq]
    exact hInt (-φ) (by rw [abs_neg]; exact hφbound)
  have hmgfN : ∫ z, Real.exp (φ * (-(quadratic S z - S.trace)))
      ∂(gaussianVectorLaw d)
      ≤ Real.exp (4 * φ ^ 2 * F2) := by
    have heq : (fun (z : Vector d) =>
          Real.exp (φ * (-(quadratic S z - S.trace))))
        = fun z => Real.exp ((-φ) * (quadratic S z - S.trace)) := by
      funext z
      congr 1
      ring
    rw [heq]
    have h := hMGF (-φ) (by rw [abs_neg]; exact hφbound)
    have hsq : (-φ) ^ 2 = φ ^ 2 := by ring
    rw [hsq] at h
    exact h
  have hcherN : (gaussianVectorLaw d) {z | u ≤ -(quadratic S z - S.trace)}
      ≤ ENNReal.ofReal (Real.exp (-φ * u) * Real.exp (4 * φ ^ 2 * F2)) :=
    hw_chernoff hNYcont hφpos hintN hmgfN
  have hunion : (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
      ≤ ENNReal.ofReal (2 * Real.exp (-φ * u + 4 * φ ^ 2 * F2)) := by
    have hsubU : {z : Vector d | u ≤ |quadratic S z - S.trace|}
        ⊆ {z | u ≤ quadratic S z - S.trace}
          ∪ {z | u ≤ -(quadratic S z - S.trace)} := by
      intro z hz
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hz ⊢
      by_cases h : 0 ≤ quadratic S z - S.trace
      · left
        rwa [abs_of_nonneg h] at hz
      · right
        have hneg : quadratic S z - S.trace < 0 := lt_of_not_ge h
        rwa [abs_of_neg hneg] at hz
    calc (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
        ≤ (gaussianVectorLaw d) {z | u ≤ quadratic S z - S.trace}
          + (gaussianVectorLaw d) {z | u ≤ -(quadratic S z - S.trace)} :=
          le_trans (measure_mono hsubU) (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Real.exp (-φ * u) * Real.exp (4 * φ ^ 2 * F2))
          + ENNReal.ofReal (Real.exp (-φ * u) * Real.exp (4 * φ ^ 2 * F2)) :=
          add_le_add hcherY hcherN
      _ = ENNReal.ofReal (2 * Real.exp (-φ * u + 4 * φ ^ 2 * F2)) := by
          have hnn : (0 : ℝ)
              ≤ Real.exp (-φ * u) * Real.exp (4 * φ ^ 2 * F2) :=
            mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
          rw [← ENNReal.ofReal_add hnn hnn]
          congr 1
          rw [← Real.exp_add]
          ring
  have hexp_le : -φ * u + 4 * φ ^ 2 * F2
      ≤ -(min (u ^ 2 / (16 * F2)) (u / (16 * hi))) := by
    have hmin : φ = u / (8 * F2) ∨ φ = 1 / (8 * hi) := by apply min_choice
    rcases hmin with hA | hB
    · have heq : -φ * u + 4 * φ ^ 2 * F2 = -(u ^ 2 / (16 * F2)) := by
        rw [hA]
        have hF2' : F2 ≠ 0 := ne_of_gt hF2pos
        have h8F2 : (8 : ℝ) * F2 ≠ 0 := mul_ne_zero (by norm_num) hF2'
        have h16F2 : (16 : ℝ) * F2 ≠ 0 := mul_ne_zero (by norm_num) hF2'
        field_simp
        try ring
      rw [heq]
      exact neg_le_neg (by apply min_le_left)
    · have h1 : (1 : ℝ) / (8 * hi) ≤ u / (8 * F2) := by
        rw [← hB]
        apply min_le_left
      have hFu : F2 ≤ u * hi := by
        have h8hi : (0 : ℝ) < 8 * hi := mul_pos (by norm_num) hhi
        have h8F2 : (0 : ℝ) < 8 * F2 := mul_pos (by norm_num) hF2pos
        rw [div_le_iff₀ h8hi] at h1
        have ee : (u / (8 * F2)) * (8 * hi) = u * hi / F2 := by
          have hF2' : F2 ≠ 0 := ne_of_gt hF2pos
          have h8F2' : (8 : ℝ) * F2 ≠ 0 := mul_ne_zero (by norm_num) hF2'
          field_simp
          try ring
        rw [ee] at h1
        rw [le_div_iff₀ hF2pos, one_mul] at h1
        exact h1
      have heq : -φ * u + 4 * φ ^ 2 * F2
          = -(u / (8 * hi)) + F2 / (16 * hi ^ 2) := by
        rw [hB]
        have hhi' : hi ≠ 0 := ne_of_gt hhi
        have h8hi : (8 : ℝ) * hi ≠ 0 := mul_ne_zero (by norm_num) hhi'
        have h16hi2 : (16 : ℝ) * hi ^ 2 ≠ 0 :=
          mul_ne_zero (by norm_num) (ne_of_gt (pow_pos hhi 2))
        field_simp
        try ring
      have hle2 : F2 / (16 * hi ^ 2) ≤ u / (16 * hi) := by
        have h16 : (0 : ℝ) < 16 * hi ^ 2 :=
          mul_pos (by norm_num) (pow_pos hhi 2)
        rw [div_le_iff₀ h16]
        have ee : (u / (16 * hi)) * (16 * hi ^ 2) = u * hi := by
          have hhi' : hi ≠ 0 := ne_of_gt hhi
          have h16hi : (16 : ℝ) * hi ≠ 0 := mul_ne_zero (by norm_num) hhi'
          field_simp
          try ring
        rw [ee]
        exact hFu
      calc -φ * u + 4 * φ ^ 2 * F2
          = -(u / (8 * hi)) + F2 / (16 * hi ^ 2) := heq
        _ ≤ -(u / (8 * hi)) + u / (16 * hi) := by linarith [hle2]
        _ = -(u / (16 * hi)) := by
            have hhi' : hi ≠ 0 := ne_of_gt hhi
            have h8hi : (8 : ℝ) * hi ≠ 0 := mul_ne_zero (by norm_num) hhi'
            have h16hi : (16 : ℝ) * hi ≠ 0 := mul_ne_zero (by norm_num) hhi'
            field_simp
            try ring
        _ ≤ -(min (u ^ 2 / (16 * F2)) (u / (16 * hi))) :=
            neg_le_neg (by apply min_le_right)
  have hmulmin : hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ))
      = min (hwRate hi * t ^ 2) (hwRate hi * (t * Real.sqrt (d : ℝ))) := by
    rcases le_total (t ^ 2) (t * Real.sqrt (d : ℝ)) with h | h
    · have e1 : min (t ^ 2) (t * Real.sqrt (d : ℝ)) = t ^ 2 := by
        apply min_eq_left
        exact h
      have e2 : min (hwRate hi * t ^ 2)
            (hwRate hi * (t * Real.sqrt (d : ℝ))) = hwRate hi * t ^ 2 := by
        apply min_eq_left
        exact mul_le_mul_of_nonneg_left h hRate0
      rw [e1, e2]
    · have e1 : min (t ^ 2) (t * Real.sqrt (d : ℝ))
          = t * Real.sqrt (d : ℝ) := by
        apply min_eq_right
        exact h
      have e2 : min (hwRate hi * t ^ 2)
            (hwRate hi * (t * Real.sqrt (d : ℝ)))
          = hwRate hi * (t * Real.sqrt (d : ℝ)) := by
        apply min_eq_right
        exact mul_le_mul_of_nonneg_left h hRate0
      rw [e1, e2]
  have hA : hwRate hi * t ^ 2 ≤ u ^ 2 / (16 * F2) := by
    have hu2 : u ^ 2 = t ^ 2 * d := by
      rw [hu_def, mul_pow, Real.sq_sqrt hdR.le]
    have h1 : hwRate hi * t ^ 2 ≤ (1 / (16 * hi ^ 2)) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hRate_le1 (sq_nonneg _)
    have h2 : (1 / (16 * hi ^ 2)) * t ^ 2 ≤ u ^ 2 / (16 * F2) := by
      rw [hu2]
      have h16F2 : (0 : ℝ) < 16 * F2 := mul_pos (by norm_num) hF2pos
      rw [le_div_iff₀ h16F2]
      have ee : ((1 / (16 * hi ^ 2)) * t ^ 2) * (16 * F2)
          = t ^ 2 * (F2 / hi ^ 2) := by
        have hhi' : hi ≠ 0 := ne_of_gt hhi
        have h16hi2 : (16 : ℝ) * hi ^ 2 ≠ 0 :=
          mul_ne_zero (by norm_num) (ne_of_gt (pow_pos hhi 2))
        have hhi2' : hi ^ 2 ≠ 0 := ne_of_gt (pow_pos hhi 2)
        field_simp
        try ring
      rw [ee]
      have h3 : F2 / hi ^ 2 ≤ d := by
        have hhi2 : (0 : ℝ) < hi ^ 2 := pow_pos hhi 2
        rw [div_le_iff₀ hhi2]
        exact hF2le
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    exact le_trans h1 h2
  have hB : hwRate hi * (t * Real.sqrt (d : ℝ)) ≤ u / (16 * hi) := by
    rw [hu_def]
    have h1 : hwRate hi * (t * Real.sqrt (d : ℝ))
        ≤ (1 / (16 * hi)) * (t * Real.sqrt (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hRate_le2
        (mul_nonneg ht (Real.sqrt_nonneg _))
    have h2 : (1 / (16 * hi)) * (t * Real.sqrt (d : ℝ))
        ≤ (t * Real.sqrt (d : ℝ)) / (16 * hi) := by
      have heq : (t * Real.sqrt (d : ℝ)) / (16 * hi)
          = (1 / (16 * hi)) * (t * Real.sqrt (d : ℝ)) := by
        rw [div_eq_mul_inv, one_div, mul_comm]
      exact le_of_eq heq.symm
    exact le_trans h1 h2
  have huni : hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ))
      ≤ min (u ^ 2 / (16 * F2)) (u / (16 * hi)) := by
    rw [hmulmin]
    refine min_le_min ?_ ?_
    · exact hA
    · exact hB
  have htail : (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
      ≤ ENNReal.ofReal
        (2 * Real.exp (-(min (u ^ 2 / (16 * F2)) (u / (16 * hi))))) := by
    calc (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
        ≤ ENNReal.ofReal (2 * Real.exp (-φ * u + 4 * φ ^ 2 * F2)) := hunion
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-(min (u ^ 2 / (16 * F2)) (u / (16 * hi))))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          exact hexp_le
  have hfinal : (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
      ≤ ENNReal.ofReal
        (2 * Real.exp
          (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) := by
    calc (gaussianVectorLaw d) {z | u ≤ |quadratic S z - S.trace|}
        ≤ ENNReal.ofReal
          (2 * Real.exp (-(min (u ^ 2 / (16 * F2)) (u / (16 * hi))))) :=
          htail
      _ ≤ ENNReal.ofReal
          (2 * Real.exp
            (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          have hneg : -(min (u ^ 2 / (16 * F2)) (u / (16 * hi)))
              ≤ -hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)) := by
            rw [neg_mul]
            exact neg_le_neg huni
          exact hneg
  exact le_trans (measure_mono hsub) hfinal

/-- The Hanson–Wright chaos bound, from rotation invariance. -/
theorem hansonWrightChaos_of_ROT
    (ROT : ∀ (d : Nat) (Q : Matrix (Fin d) (Fin d) ℝ), Qᵀ * Q = 1 →
      Measure.map (fun x => Q *ᵥ x) (gaussianVectorLaw d) = gaussianVectorLaw d) :
    hansonWrightChaos := by
  intro lo hi hlo hle
  refine ⟨hwRate hi, hwRate_pos hlo hle,
    fun d n j Sdel hmeas hbox hloc t ht => ?_⟩
  have hn0 : n ≠ 0 := by
    have h := j.isLt
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ⟨k, hk⟩
  set σ : Fin (k + 1) ≃ Fin (k + 1) := Equiv.swap j 0 with hσdef
  set R : Sample d (k + 1) → Sample d (k + 1) := fun x i => x (σ i)
    with hRdef
  set Sdel0 : Sample d (k + 1) → Square d :=
    fun y => Sdel (fun i => y (σ.symm i)) with hSdel0def
  set E0 : Set (Sample d (k + 1)) :=
    {y : Sample d (k + 1) |
      t < |(quadratic (Sdel0 y) (y 0) - (Sdel0 y).trace) / Real.sqrt (d : ℝ)|}
    with hE0def
  set B : ℝ :=
    2 * Real.exp (-hwRate hi * min (t ^ 2) (t * Real.sqrt (d : ℝ)))
    with hBdef
  have hRapply : ∀ x i, R x i = x (σ i) := fun x i => rfl
  have hSdel0apply : ∀ y, Sdel0 y = Sdel (fun i => y (σ.symm i)) :=
    fun y => rfl
  have hσ0 : σ 0 = j := by
    rw [hσdef]
    exact Equiv.swap_apply_right j 0
  have hSdel0R : ∀ x, Sdel0 (R x) = Sdel x := by
    intro x
    simp only [hSdel0apply, hRapply]
    congr 1
    funext i
    rw [Equiv.apply_symm_apply]
  have hR0 : ∀ x, R x 0 = x j := by
    intro x
    rw [hRapply, hσ0]
  have hSdel0meas : Measurable Sdel0 := by
    have hf : Measurable
        (fun (y : Sample d (k + 1)) => fun i => y (σ.symm i)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (σ.symm i))
    rw [hSdel0def]
    exact hmeas.comp hf
  have hSdel0box : ∀ y, Sdel0 y ∈ spectralBox d lo hi := by
    intro y
    rw [hSdel0apply]
    exact hbox _
  have hSdel0loc : ∀ (y y' : Sample d (k + 1)),
      (∀ i, i ≠ 0 → y i = y' i) → Sdel0 y = Sdel0 y' := by
    intro y y' hagree
    rw [hSdel0apply, hSdel0apply]
    apply hloc
    intro i hi
    show y (σ.symm i) = y' (σ.symm i)
    apply hagree
    intro hcon
    apply hi
    have h1 : σ (σ.symm i) = σ 0 := by rw [hcon]
    rw [Equiv.apply_symm_apply, hσ0] at h1
    exact h1
  have hRmeas : Measurable R := by
    rw [hRdef]
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
  have hE0meas : MeasurableSet E0 := by
    rw [hE0def]
    have hch : Measurable (fun (y : Sample d (k + 1)) =>
        (quadratic (Sdel0 y) (y 0) - (Sdel0 y).trace) / Real.sqrt (d : ℝ)) :=
      measurable_chaos 0 Sdel0 hSdel0meas
    have habs : Measurable (fun (y : Sample d (k + 1)) =>
        |(quadratic (Sdel0 y) (y 0) - (Sdel0 y).trace) / Real.sqrt (d : ℝ)|) :=
      continuous_abs.measurable.comp hch
    exact measurableSet_lt measurable_const habs
  have hEeq : {x : Sample d (k + 1) |
        t < |(quadratic (Sdel x) (x j) - (Sdel x).trace) / Real.sqrt (d : ℝ)|}
      = R ⁻¹' E0 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hE0def, hR0, hSdel0R]
  have hmapR : Measure.map R (gaussianSampleLaw d (k + 1))
      = gaussianSampleLaw d (k + 1) :=
    gaussianSample_restrict_map (d := d) (⇑σ) σ.injective
  have hμE : (gaussianSampleLaw d (k + 1))
        {x : Sample d (k + 1) |
          t < |(quadratic (Sdel x) (x j) - (Sdel x).trace) / Real.sqrt (d : ℝ)|}
      = (gaussianSampleLaw d (k + 1)) E0 := by
    rw [hEeq, ← Measure.map_apply hRmeas hE0meas, hmapR]
  set e0 : Sample d (k + 1) ≃ᵐ (Vector d × (Fin k → Vector d)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Vector d) 0
    with he0def
  have he0fst : ∀ x : Sample d (k + 1), (e0 x).1 = x 0 := by
    intro x
    show ((Fin.insertNthEquiv (fun _ : Fin (k + 1) => Vector d) 0).symm x).1
      = x 0
    rw [Fin.insertNthEquiv_zero]
    rfl
  have he0snd : ∀ x : Sample d (k + 1), (e0 x).2 = Fin.tail x := by
    intro x
    show ((Fin.insertNthEquiv (fun _ : Fin (k + 1) => Vector d) 0).symm x).2
      = Fin.tail x
    rw [Fin.insertNthEquiv_zero]
    rfl
  have he0apply : ∀ x : Sample d (k + 1), e0 x = (x 0, Fin.tail x) := by
    intro x
    have h1 := he0fst x
    have h2 := he0snd x
    calc e0 x = ((e0 x).1, (e0 x).2) := rfl
      _ = (x 0, Fin.tail x) := by rw [h1, h2]
  set e' : Sample d (k + 1) ≃ᵐ ((Fin k → Vector d) × Vector d) :=
    e0.trans MeasurableEquiv.prodComm with he'def
  have he'apply : ∀ x : Sample d (k + 1), e' x = (Fin.tail x, x 0) := by
    intro x
    have he : e0 x = (x 0, Fin.tail x) := he0apply x
    show Prod.swap (e0 x) = (Fin.tail x, x 0)
    rw [he]
    rfl
  have hmap' : Measure.map ⇑e' (gaussianSampleLaw d (k + 1))
      = (Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d) := by
    have hmp0 := measurePreserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => gaussianVectorLaw d) 0
    have hcomp : ⇑e' = Prod.swap ∘ ⇑e0 := rfl
    rw [hcomp, ← Measure.map_map measurable_swap e0.measurable]
    have hmp0' : Measure.map ⇑e0 (gaussianSampleLaw d (k + 1))
        = (gaussianVectorLaw d).prod
          (Measure.pi fun _ : Fin k => gaussianVectorLaw d) :=
      hmp0.map_eq
    rw [hmp0']
    exact Measure.prod_swap
  have hWmeas : MeasurableSet (e' '' E0) := by
    have himg : e' '' E0 = e'.symm ⁻¹' E0 := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        show e'.symm (e' x) ∈ E0
        have hsym : e'.toEquiv.symm (e'.toEquiv x) = x := by simp
        rw [show e'.symm (e' x) = e'.toEquiv.symm (e'.toEquiv x) from rfl,
          hsym]
        exact hx
      · intro hy
        refine ⟨e'.symm y, hy, ?_⟩
        have happ : e'.toEquiv (e'.toEquiv.symm y) = y := by simp
        show e' (e'.symm y) = y
        rw [show e' (e'.symm y) = e'.toEquiv (e'.toEquiv.symm y) from rfl]
        exact happ
    rw [himg]
    exact e'.symm.measurable hE0meas
  have hE0eq : (gaussianSampleLaw d (k + 1)) E0
      = ((Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d)) (e' '' E0) := by
    rw [← hmap', Measure.map_apply e'.measurable hWmeas,
      Set.preimage_image_eq _ e'.injective]
  set g : (Fin k → Vector d) → Square d :=
    fun r => Sdel0 (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) 0 r)
    with hgdef
  have hagree : ∀ (z w : Vector d) (r : Fin k → Vector d) (i : Fin (k + 1)),
      i ≠ 0 →
      (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) z r) i
        = (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) w r) i := by
    intro z w r i
    refine Fin.cases
      (motive := fun i : Fin (k + 1) => i ≠ 0 →
        (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) z r) i
          = (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) w r) i) ?_
      (fun kk => ?_) i
    · intro h
      exact absurd rfl h
    · intro _
      rw [Fin.cons_succ, Fin.cons_succ]
  have hgSdel0 : ∀ (z : Vector d) (r : Fin k → Vector d),
      Sdel0 (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) z r) = g r := by
    intro z r
    have hloc0 := hSdel0loc _ _ (hagree z 0 r)
    have hgr : g r
        = Sdel0 (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) 0 r) := rfl
    rw [hgr]
    exact hloc0
  have hgrbox : ∀ r, g r ∈ spectralBox d lo hi := fun r =>
    hSdel0box (Fin.cons (α := fun _ : Fin (k + 1) => Vector d) 0 r)
  have hsec : ∀ r : Fin k → Vector d,
      Prod.mk r ⁻¹' (e' '' E0)
        = {z : Vector d |
          t < |(quadratic (g r) z - (g r).trace) / Real.sqrt (d : ℝ)|} := by
    intro r
    ext z
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq, hE0def]
    constructor
    · rintro ⟨x, hxE, hxx'⟩
      have he := he'apply x
      rw [he] at hxx'
      simp only [Prod.mk.injEq] at hxx'
      have h2 := hxx'
      have htail : Fin.tail x = r := h2.1
      have hx0 : x 0 = z := h2.2
      have hxrw : x = Fin.cons (α := fun _ : Fin (k + 1) => Vector d) z r := by
        have h := Fin.cons_self_tail x
        rw [hx0, htail] at h
        exact h.symm
      rw [hx0, hxrw, hgSdel0] at hxE
      exact hxE
    · intro hz
      refine ⟨Fin.cons (α := fun _ : Fin (k + 1) => Vector d) z r, ?_, ?_⟩
      · rw [Fin.cons_zero, hgSdel0]
        exact hz
      · rw [he'apply, Fin.tail_cons, Fin.cons_zero]
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hint : (∫⁻ r, (gaussianVectorLaw d)
        (Prod.mk r ⁻¹' (e' '' E0))
        ∂(Measure.pi fun _ : Fin k => gaussianVectorLaw d))
      ≤ ENNReal.ofReal B := by
    have hle : (∫⁻ r, (gaussianVectorLaw d)
          (Prod.mk r ⁻¹' (e' '' E0))
          ∂(Measure.pi fun _ : Fin k => gaussianVectorLaw d))
        ≤ ∫⁻ _ : (Fin k → Vector d), ENNReal.ofReal B
          ∂(Measure.pi fun _ : Fin k => gaussianVectorLaw d) := by
      apply MeasureTheory.lintegral_mono_ae
      exact Filter.Eventually.of_forall (fun r => by
        rw [hsec r]
        exact hw_fixed_tail (g r) (hgrbox r) hlo hle ROT t ht)
    have hconst : (∫⁻ _ : (Fin k → Vector d), ENNReal.ofReal B
        ∂(Measure.pi fun _ : Fin k => gaussianVectorLaw d))
        = ENNReal.ofReal B := by
      rw [lintegral_const]
      have hu1 : (Measure.pi fun _ : Fin k => gaussianVectorLaw d) Set.univ
          = 1 := by
        apply measure_univ
      rw [hu1, mul_one]
    rw [hconst] at hle
    exact hle
  have hprod_eq : ((Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d)) (e' '' E0)
      = ∫⁻ r, (gaussianVectorLaw d) (Prod.mk r ⁻¹' (e' '' E0))
        ∂(Measure.pi fun _ : Fin k => gaussianVectorLaw d) :=
    Measure.prod_apply hWmeas
  have hleE0 : ((Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d)) (e' '' E0)
      ≤ ENNReal.ofReal B := by
    rw [hprod_eq]
    exact hint
  have hfin : ((Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d)) (e' '' E0) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hleE0 ENNReal.ofReal_lt_top)
  have hBtoReal : (ENNReal.ofReal B).toReal = B :=
    ENNReal.toReal_ofReal hBnn
  calc ((gaussianSampleLaw d (k + 1))
        {x : Sample d (k + 1) |
          t < |(quadratic (Sdel x) (x j) - (Sdel x).trace) / Real.sqrt (d : ℝ)|}).toReal
      = (((Measure.pi fun _ : Fin k => gaussianVectorLaw d).prod
        (gaussianVectorLaw d)) (e' '' E0)).toReal := by
        rw [hμE, hE0eq]
    _ ≤ (ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hleE0
    _ = B := hBtoReal



/-- Unconditional Hanson-Wright chaos: rotation is discharged by
RotAssemble. -/
theorem hansonWrightChaos_theorem : hansonWrightChaos :=
  hansonWrightChaos_of_ROT
    (fun d Q hQ => gaussianVectorLaw_rotation_uncond d Q hQ)

end GaussianEllipsoid
