import BMHighProbabilityBox

noncomputable section
set_option synthInstance.maxSize 512
open MeasureTheory ProbabilityTheory GaussianTensorMoments Filter
open GaussianEllipsoid BMGeometry
open scoped BigOperators InnerProductSpace Matrix Topology
namespace BMSpectralBridge

/-- Radius enlargement preserves every feasible witness, with no probabilistic event loss. -/
theorem actualConeFeasible_mono_radius {n d : ℕ} {κ R R' : ℝ} (hRR' : R ≤ R')
    {z : Fin n → Fin (d*d) → ℝ} (hz : actualConeFeasible n d κ R z) :
    actualConeFeasible n d κ R' z := by
  obtain ⟨S,hS,hR,hfeas⟩ := hz
  exact ⟨S,hS,hR.trans (mul_le_mul_of_nonneg_right hRR' (Real.sqrt_nonneg _)),hfeas⟩

/-- The identity is an explicit matrix in every Loewner box that contains the scalar 1. -/
theorem identity_mem_spectralBox (d : ℕ) {lo hi : ℝ} (hlo : lo ≤ 1) (hhi : 1 ≤ hi) :
    (1 : Matrix (Fin d) (Fin d) ℝ) ∈ BMRescaling.spectralBox d lo hi := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  constructor
  · convert BMRescaling.posSemidef_smul (Matrix.PosSemidef.one :
      (1 : Matrix (Fin d) (Fin d) ℝ).PosSemidef) (sub_nonneg.mpr hlo) using 1 <;> module
  · convert BMRescaling.posSemidef_smul (Matrix.PosSemidef.one :
      (1 : Matrix (Fin d) (Fin d) ℝ).PosSemidef) (sub_nonneg.mpr hhi) using 1 <;> module

/-- Explicit deterministic nonemptiness and positive endpoint parameters. -/
theorem enlarged_box_parameters {κ R a : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a) (haquarter : a < 1/4) :
    0 < Real.sqrt a/(32*κ) ∧ Real.sqrt a/(32*κ) ≤ 1 ∧
      1 ≤ κ*max R 1 ∧ ∀ d, (1 : Matrix (Fin d) (Fin d) ℝ) ∈
        BMRescaling.spectralBox d (Real.sqrt a/(32*κ)) (κ*max R 1) := by
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hs : Real.sqrt a < 1 := by
    have hsq := Real.sq_sqrt ha.le
    have hn := Real.sqrt_nonneg a
    nlinarith
  have hlo : Real.sqrt a/(32*κ) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hκpos)).mpr
    nlinarith
  have hhi : 1 ≤ κ*max R 1 := by
    calc
      1 = 1*1 := by norm_num
      _ ≤ κ*max R 1 := mul_le_mul hκ (le_max_right R 1) (by norm_num) hκpos.le
  exact ⟨fixed_box_lower_positive ha hκpos,hlo,hhi,fun d => identity_mem_spectralBox d hlo hhi⟩

/-- A safe final-assembly version: enlarge the source radius to max R 1 first, making
I a deterministic box witness and the upper operator cap positive. -/
theorem actual_box_probability_tendsto_one_enlarged (n : ℕ → ℕ) {κ R a : ℝ}
    (hκ : 1 ≤ κ) (ha : 0 < a)
    (haspect : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ n d)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualConeFeasible (n d) d κ R z}) atTop (𝓝 1)) :
    Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualBoxFeasible (n d) d (Real.sqrt a/(32*κ)) (κ*max R 1) z}) atTop (𝓝 1) := by
  have hcone' : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualConeFeasible (n d) d κ (max R 1) z}) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hcone tendsto_const_nhds
    · intro d
      exact measureReal_mono (fun z hz => actualConeFeasible_mono_radius (le_max_left R 1) hz)
    · intro d
      exact measureReal_le_one
  exact actual_box_probability_tendsto_one_of_cone_probability n
    (lt_of_lt_of_le (by norm_num) hκ) (le_trans (by norm_num) (le_max_right R 1)) ha haspect hcone'

end BMSpectralBridge
