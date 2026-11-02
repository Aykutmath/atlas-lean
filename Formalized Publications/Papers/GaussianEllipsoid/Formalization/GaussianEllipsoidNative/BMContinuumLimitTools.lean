import BMExpectationLimits

noncomputable section
open Filter
namespace BMContinuumLimitTools

theorem exponential_sample_decay (n : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (hn : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ)) :
    Tendsto (fun d => Real.exp (-((n d+1 : ℕ):ℝ))) atTop (nhds 0) := by
  have hlinear : Tendsto (fun d : ℕ => a*(d:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
  have hN : Tendsto (fun d => ((n d+1 : ℕ):ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hlinear
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hsq : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsq ha.le).trans (hn d hd)
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hN)

/-- The mesh size is sent to zero only after the dimension limit at each fixed
mesh size. This avoids any hidden simultaneous-limit rate requirement. -/
theorem tendsto_zero_of_resolution (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ d, 0 ≤ f d) (hC : 0 ≤ C)
    (hcompare : ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ,
      Tendsto e atTop (nhds 0) ∧ ∀ᶠ d in atTop, f d ≤ e d+C*η) :
    Tendsto f atTop (nhds 0) := by
  apply BMExpectationLimits.tendsto_zero_of_temperature_comparison f C hf hC
  intro β hβ
  obtain ⟨e,he,hbound⟩ := hcompare (1/β) (one_div_pos.mpr hβ)
  exact ⟨e,he,by simpa only [div_eq_mul_inv,one_mul] using hbound⟩

/-- Three-piece comparison of continuum energies through a common finite net. -/
theorem continuum_gap_le_net_gaps (cW cG nW nG : ℝ) :
    |cW-cG| ≤ |nW-cW|+|nW-nG|+|nG-cG| := by
  calc
    _ = |(cW-nW)+(nW-nG)+(nG-cG)| := by congr 1; ring
    _ ≤ |cW-nW|+|nW-nG|+|nG-cG| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = _ := by rw [abs_sub_comm cW nW]

#print axioms exponential_sample_decay
#print axioms tendsto_zero_of_resolution
end BMContinuumLimitTools
