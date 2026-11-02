import NuclearEntropy
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianEllipsoid

/-- Actual finite-cover probability transfer. No measurability of an
uncountable minimizer/selector is needed for this outer-measure bound. -/
theorem nuclear_smallball_of_finite_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (r : ℕ)
    (Y : Ω → FrobeniusMatrix r r) (M : FrobeniusMatrix r r)
    {R ε p : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hp : 0 ≤ p)
    (hball : ∀ C : FrobeniusMatrix r r,
      μ.real {ω | ‖Y ω - C‖ ≤ ε} ≤ p) :
    μ.real {ω | spectralNuclearNorm (Y ω - M) ≤ R} ≤
      Real.exp (256 * r * R^2 / ε^2) * p := by
  classical
  obtain ⟨s, hcard, hcover⟩ := exists_nuclear_frobenius_cover r hR hε
  have hsub : {ω | spectralNuclearNorm (Y ω - M) ≤ R} ⊆
      ⋃ C ∈ s, {ω | ‖Y ω - (M+C)‖ ≤ ε} := by
    intro ω hω
    obtain ⟨C, hC, hc⟩ := hcover (Y ω - M) hω
    refine Set.mem_iUnion.2 ⟨C, Set.mem_iUnion.2 ⟨hC, ?_⟩⟩
    change ‖Y ω - (M+C)‖ ≤ ε
    simpa only [sub_sub] using hc
  calc
    _ ≤ μ.real (⋃ C ∈ s, {ω | ‖Y ω - (M+C)‖ ≤ ε}) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ C ∈ s, μ.real {ω | ‖Y ω - (M+C)‖ ≤ ε} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ C ∈ s, p := Finset.sum_le_sum (fun C _ => hball (M+C))
    _ = (s.card : ℝ)*p := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hp

/-- The numerical constant used in the polynomial nuclear small-ball bound. -/
theorem nuclear_probability_constant_le :
    64 * Real.sqrt 2 * Real.exp (1/2 : ℝ) ≤ 160 := by
  have hs : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : Real.exp (1/2 : ℝ)^2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he3 : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hn : 0 ≤ 64 * Real.sqrt 2 * Real.exp (1/2 : ℝ) := by positivity
  have hsq : (64 * Real.sqrt 2 * Real.exp (1/2 : ℝ))^2 < (160:ℝ)^2 := by
    rw [mul_pow, mul_pow, hs, he]
    nlinarith
  nlinarith

/-- The exact polynomial nuclear small-ball conclusion from an actual
arbitrary-center Frobenius small-ball estimate and the proved C256 cover. -/
theorem nuclear_smallball_polynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (r : ℕ) (hr : 0 < r)
    (Y : Ω → FrobeniusMatrix r r)
    (hball : ∀ (C : FrobeniusMatrix r r) (t : ℝ), 0 < t →
      μ.real {ω | ‖Y ω - C‖ ≤ t * Real.sqrt r} ≤ (4*t)^(r*r))
    (M : FrobeniusMatrix r r) {ν : ℝ} (hν : 0 < ν) :
    μ.real {ω | spectralNuclearNorm (Y ω - M) ≤ ν*r} ≤
      (160*ν)^(r*r) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hs : Real.sqrt (r:ℝ)^2 = r := Real.sq_sqrt hrR.le
  have h2 : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  let t : ℝ := 16 * Real.sqrt 2 * ν
  have ht : 0 < t := by dsimp [t]; positivity
  have hh := nuclear_smallball_of_finite_radius μ r Y M
    (R := ν*r) (ε := t*Real.sqrt r) (p := (4*t)^(r*r))
    (by positivity) (by positivity) (by positivity) (fun C => hball C t ht)
  have hexponent : 256 * (r:ℝ) * (ν*r)^2 / (t*Real.sqrt r)^2 =
      ((r*r:ℕ):ℝ)/2 := by
    dsimp [t]
    simp only [mul_pow, hs, h2]
    push_cast
    field_simp [ne_of_gt hν, ne_of_gt hrR]
    <;> ring
  rw [hexponent] at hh
  have hexp : Real.exp (((r*r:ℕ):ℝ)/2 : ℝ) = Real.exp (1/2:ℝ)^(r*r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp, ← mul_pow] at hh
  have hbase : Real.exp (1/2:ℝ)*(4*t) ≤ 160*ν := by
    calc
      _ = (64*Real.sqrt 2*Real.exp (1/2:ℝ))*ν := by dsimp [t]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right nuclear_probability_constant_le hν.le
  exact hh.trans (pow_le_pow_left₀ (by positivity) hbase _)

/-- Conservative fixed-radius specialization used by every multiscale block. -/
theorem nuclear_smallball_unit_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (r : ℕ) (hr : 0 < r)
    (Y : Ω → FrobeniusMatrix r r)
    (hball : ∀ (C : FrobeniusMatrix r r) (t : ℝ), 0 < t →
      μ.real {ω | ‖Y ω - C‖ ≤ t * Real.sqrt r} ≤ (4*t)^(r*r))
    (M : FrobeniusMatrix r r) :
    μ.real {ω | spectralNuclearNorm (Y ω - M) ≤ (r:ℝ)/1024} ≤
      Real.exp (-((r*r:ℕ):ℝ)) := by
  have h := nuclear_smallball_polynomial μ r hr Y hball M
    (ν := (1/1024:ℝ)) (by norm_num)
  have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hb : 160 * (1/1024:ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 160*(1/1024:ℝ)) hb (r*r)
  rw [← Real.exp_nat_mul] at hp
  have heq : ((r*r:ℕ):ℝ)*(-1) = -((r*r:ℕ):ℝ) := by ring
  rw [heq] at hp
  simpa only [one_div_mul_eq_div] using h.trans hp

#print axioms nuclear_smallball_unit_exp
#print axioms nuclear_smallball_of_finite_radius
#print axioms nuclear_probability_constant_le
#print axioms nuclear_smallball_polynomial
end GaussianEllipsoid
