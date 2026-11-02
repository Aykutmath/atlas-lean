import Mathlib

/- Reconstructed from the exact logarithmic level and consumer call sites.
   This is a new source, not a recovered original. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianEllipsoid

def paperLogLevel (c : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (4/c) * Real.sqrt (Real.log (d:ℝ))

theorem paperLogLevel_eventually (c K : ℝ) (hc : 0 < c) :
    ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧ K+1 ≤ paperLogLevel c d ∧
      paperLogLevel c d ≤ Real.sqrt (d:ℝ) := by
  have hnat : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlevel : Tendsto (paperLogLevel c) atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      (Real.sqrt_pos.mpr (by positivity : 0 < 4/c))
      (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hnat))
  have hsmall := ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hnat).eventually
    (eventually_le_nhds (show (0:ℝ) < c/4 by positivity))
  filter_upwards [eventually_ge_atTop 1,hlevel.eventually (eventually_ge_atTop (K+1)),hsmall]
    with d hd hl hs
  refine ⟨hd,hl,?_⟩
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hlog : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hlogle : Real.log (d:ℝ) ≤ c/4*(d:ℝ) := (div_le_iff₀ hdR).mp hs
  have hsq : (paperLogLevel c d)^2 = (4/c)*Real.log (d:ℝ) := by
    simp only [paperLogLevel,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 4/c),Real.sq_sqrt hlog]
  have hmul := mul_le_mul_of_nonneg_left hlogle (show 0 ≤ 4/c by positivity)
  have hcancel : (4/c)*(c/4*(d:ℝ)) = d := by field_simp [hc.ne']
  rw [hcancel] at hmul
  have hdSq := Real.sq_sqrt hdR.le
  have hnonneg : 0 ≤ paperLogLevel c d := by unfold paperLogLevel; positivity
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

theorem paper_log_hw_min (c : ℝ) (d : ℕ)
    (h : paperLogLevel c d ≤ Real.sqrt (d:ℝ)) :
    min ((paperLogLevel c d)^2) (paperLogLevel c d * Real.sqrt (d:ℝ)) =
      (paperLogLevel c d)^2 := by
  apply min_eq_left
  have ht : 0 ≤ paperLogLevel c d := by unfold paperLogLevel; positivity
  nlinarith

theorem paper_log_union_tendsto (n : ℕ → ℕ) (α c : ℝ) (hc : 0 < c)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α)) :
    Tendsto (fun d => (n d:ℝ)*(2*Real.exp (-c*(paperLogLevel c d)^2))) atTop (𝓝 0) := by
  have hinv := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have ht := hconv.mul (hinv.const_mul 2)
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hlog : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hsq : (paperLogLevel c d)^2 = (4/c)*Real.log (d:ℝ) := by
    simp only [paperLogLevel,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 4/c),Real.sq_sqrt hlog]
  have hexponent : -c*(paperLogLevel c d)^2 = -(4*Real.log (d:ℝ)) := by
    rw [hsq]
    field_simp [hc.ne']
    <;> ring
  have hexp : Real.exp (-c*(paperLogLevel c d)^2) = ((d:ℝ)^4)⁻¹ := by
    have hlog4 : Real.log ((d:ℝ)^4) = 4*Real.log (d:ℝ) := by
      simpa using Real.log_pow (d:ℝ) 4
    rw [hexponent, ← hlog4, Real.exp_neg, Real.exp_log (pow_pos hdR 4)]
  rw [hexp]
  field_simp [hdR.ne']
  <;> ring

end GaussianEllipsoid
#print axioms GaussianEllipsoid.paperLogLevel_eventually
#print axioms GaussianEllipsoid.paper_log_union_tendsto
