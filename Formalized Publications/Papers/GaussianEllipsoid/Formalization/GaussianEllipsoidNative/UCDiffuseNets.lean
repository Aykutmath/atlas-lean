import UCContinuityGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Actual internal finite covers of the diffuse PSD class and finite-rank
nuisance subspaces. Fixed nuisance rank has vanishing entropy per sample, so
its rank does not enter the temperature/operator-cap constants. -/
noncomputable section
open Module Filter Set MeasureTheory
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCDiffuseNets
open UCContinuityGeometry

 def diffuseClass (d : ℕ) (τ : ℝ) : Set (SymFrob d) :=
  {A | (matrix A).PosSemidef ∧ ‖A‖ = 1 ∧ matrixOpNorm (matrix A) ≤ τ}

/-- Matrix net centers remain in the exact diffuse PSD class. -/
theorem exists_diffuse_net (d : ℕ) (τ r : ℝ) (hr : 0 < r) :
    ∃ s : Finset (SymFrob d), (∀ A ∈ s, A ∈ diffuseClass d τ) ∧
      (s.card:ℝ) ≤ (1+2/r)^(d*d) ∧
      ∀ A ∈ diffuseClass d τ, ∃ B ∈ s, ‖A-B‖ < r := by
  obtain ⟨s, hs, hc, hn, _⟩ := exists_internal_net (diffuseClass d τ)
    (R := 1) (ε := r) (by norm_num) hr (fun A hA => hA.2.1.le)
  refine ⟨s, hs, ?_, ?_⟩
  · simp only [mul_one] at hc
    have hb : (1:ℝ) ≤ 1+2/r := le_add_of_nonneg_right (by positivity)
    exact hc.trans (pow_le_pow_right₀ hb (symFrob_finrank_le d))
  · intro A hA
    simpa only [dist_eq_norm] using hn A hA

/-- A Euclidean nuisance mesh of radius s also has averaged-l1 error at
most s. Its entropy is only O_M(log n) when the nuisance rank is fixed. -/
theorem exists_nuisance_net (n M : ℕ) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hL : finrank ℝ L ≤ M) (B s : ℝ) (hB : 0 ≤ B) (hs : 0 < s) :
    ∃ t : Finset L, (∀ v ∈ t, ‖v‖ ≤ B*n) ∧
      (t.card:ℝ) ≤ (1+2*B*n/s)^M ∧
      ∀ v : L, ‖v‖ ≤ B*n → ∃ w ∈ t, ‖v-w‖ < s := by
  obtain ⟨t, ht, hc, hn, _⟩ := exists_internal_net
    {v : L | ‖v‖ ≤ B*n} (R := B*n) (ε := s) (by positivity) hs (fun v hv => hv)
  refine ⟨t, ht, ?_, ?_⟩
  · have hb : (1:ℝ) ≤ 1+2*(B*n)/s := le_add_of_nonneg_right (by positivity)
    have hh := hc.trans (pow_le_pow_right₀ hb hL)
    simpa only [mul_assoc] using hh
  · intro v hv
    simpa only [dist_eq_norm] using hn v hv

/-- The nuisance covering entropy per observation vanishes for each fixed
rank M, with constants independent of M in the eventual bound. -/
theorem nuisance_entropy_eventually (M : ℕ) (B s : ℝ) (hB : 0 ≤ B) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, (M:ℝ)*Real.log (1+2*B*n/s) ≤ n := by
  let C : ℝ := 1+2*B/s
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have hcst : Tendsto (fun n : ℕ => Real.log C/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun n : ℕ => (M:ℝ)*(Real.log C/(n:ℝ)+Real.log (n:ℝ)/(n:ℝ)))
      atTop (𝓝 0) := by simpa using (hcst.add hlog).const_mul (M:ℝ)
  filter_upwards [hg.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop 1] with n hg hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hb : 0 < 1+2*B*n/s := by positivity
  have hbase : 1+2*B*n/s ≤ C*n := by
    dsimp [C]
    simp only [div_eq_mul_inv]
    nlinarith
  have hl := Real.log_le_log hb hbase
  rw [Real.log_mul hC.ne' hn0.ne'] at hl
  have hh : ((M:ℝ)*Real.log (1+2*B*n/s))/(n:ℝ) ≤
      (M:ℝ)*(Real.log C/(n:ℝ)+Real.log (n:ℝ)/(n:ℝ)) := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg M)) hn0.le
    exact h.trans_eq (by ring)
  simpa only [one_mul] using ((div_lt_iff₀ hn0).mp (hh.trans_lt hg)).le

/-- Combined finite candidate entropy; the fixed-rank nuisance contributes
at most one to R*, so choosing beta and then tau has no circular rank dependence. -/
theorem combined_entropy {d n M : ℕ} {a r B s : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hB : 0 ≤ B) (hs : 0 < s)
    (haspect : a*(d:ℝ)^2 ≤ n)
    (I J : ℕ) (hI : 0 < I) (hJ : 0 < J)
    (hIc : (I:ℝ) ≤ (1+2/r)^(d*d))
    (hJc : (J:ℝ) ≤ (1+2*B*n/s)^M)
    (hEnt : (M:ℝ)*Real.log (1+2*B*n/s) ≤ n) :
    Real.log ((I*J:ℕ):ℝ) ≤ (Real.log (1+2/r)/a+1)*(n:ℝ) := by
  have hb : 0 < 1+2/r := by positivity
  have hc : 0 < 1+2*B*n/s := by positivity
  have hi0 : (0:ℝ) < I := by exact_mod_cast hI
  have hj0 : (0:ℝ) < J := by exact_mod_cast hJ
  have hli := Real.log_le_log hi0 hIc
  have hlj := Real.log_le_log hj0 hJc
  rw [Real.log_pow] at hli hlj
  have hlognn : 0 ≤ Real.log (1+2/r) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hdr : (d:ℝ)^2 ≤ (n:ℝ)/a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left hdr hlognn
  have hli' : Real.log (I:ℝ) ≤ (d:ℝ)^2*Real.log (1+2/r) := by
    simpa only [Nat.cast_mul, pow_two] using hli
  rw [Nat.cast_mul, Real.log_mul hi0.ne' hj0.ne']
  have hsum : Real.log (I:ℝ)+Real.log (J:ℝ) ≤ (d:ℝ)^2*Real.log (1+2/r)+(n:ℝ) := by
    linarith
  apply hsum.trans
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith

#print axioms exists_diffuse_net
#print axioms exists_nuisance_net
#print axioms nuisance_entropy_eventually
#print axioms combined_entropy
end GaussianEllipsoid.UCDiffuseNets
