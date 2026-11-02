import Mathlib.Tactic

/-! Reconstructed scalar helper, fixed by normalized_contraction_le's call site. -/
namespace PaperCavityContraction

theorem paper_scalar_mass_le {β a b c : ℝ}
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a + 6 * β * b * c + 6 * β^2 * b^3 ≤
      6 * (a + β * b * c + β^2 * b^3) := by
  nlinarith

#print axioms paper_scalar_mass_le
end PaperCavityContraction
