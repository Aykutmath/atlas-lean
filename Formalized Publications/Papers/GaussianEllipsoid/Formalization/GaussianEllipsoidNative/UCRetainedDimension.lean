import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace UCEscape

/-- Exact dimension bookkeeping for deleting k rows and imposing M nuisance
constraints; all constants are deterministic aspect-ratio parameters. -/
theorem retained_rank_ge (n d M k : ℕ) (αm αp β δ : ℝ)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hnlo : αm*(d:ℝ)^2 ≤ n) (hnhi : (n:ℝ) ≤ αp*(d:ℝ)^2)
    (hk : (k:ℝ) ≤ δ*n)
    (hM : (M:ℝ) ≤ (αm-δ*αp-β)*(d:ℝ)^2) :
    M+k ≤ n ∧ β*(d:ℝ)^2 ≤ ((n-M-k:ℕ):ℝ) := by
  have hkn := hk.trans (mul_le_mul_of_nonneg_left hnhi hδ)
  have hsum : (M:ℝ)+(k:ℝ) ≤ n := by nlinarith [mul_nonneg hβ (sq_nonneg (d:ℝ))]
  have hnat : M+k ≤ n := by exact_mod_cast hsum
  refine ⟨hnat,?_⟩
  rw [Nat.cast_sub (by omega : k ≤ n-M), Nat.cast_sub (by omega : M ≤ n)]
  nlinarith

/-- For a fixed nuisance rank the rank-loss budget is eventually negligible,
with a direct Archimedean witness rather than an asymptotic assumption. -/
theorem fixed_rank_eventually_negligible (M : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ D : ℕ, ∀ d ≥ D, (M:ℝ) ≤ γ*(d:ℝ)^2 := by
  obtain ⟨D,hD⟩ := exists_nat_gt ((M:ℝ)/γ+1)
  refine ⟨D,?_⟩
  intro d hd
  have hdd : (D:ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 ≤ (M:ℝ)/γ := div_nonneg (Nat.cast_nonneg _) hγ.le
  have hd1 : 1 ≤ (d:ℝ) := by linarith
  have hsmall : (M:ℝ)/γ ≤ d := by linarith
  have hlin : (M:ℝ) ≤ γ*(d:ℝ) := by
    have h := (div_le_iff₀ hγ).mp hsmall
    nlinarith
  have hsq : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  exact hlin.trans (mul_le_mul_of_nonneg_left hsq hγ.le)

#print axioms retained_rank_ge
#print axioms fixed_rank_eventually_negligible
end UCEscape
