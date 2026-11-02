import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

noncomputable section
open Set

namespace GaussianEllipsoid.CappedSimplex

/-- A scalar quadratic with nonpositive quadratic coefficient is concave. -/
theorem concaveOn_quadratic (c b a : ℝ) (ha : 0 ≤ a) :
    ConcaveOn ℝ Set.univ (fun t : ℝ => c + b * t - a * t ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  simp only [smul_eq_mul]
  have hnonneg : 0 ≤ a * p * q * (x - y) ^ 2 := by positivity
  have hid : (c + b * (p * x + q * y) - a * (p * x + q * y) ^ 2) -
      (p * (c + b * x - a * x ^ 2) + q * (c + b * y - a * y ^ 2)) =
      a * p * q * (x - y) ^ 2 := by
    have hqeq : q = 1 - p := by linarith
    rw [hqeq]
    ring
  linarith

/-- The negative integer powers are order reversing on positive inputs. -/
theorem neg_nat_zpow_antitone (s : ℕ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-(s : ℤ)) ≤ x ^ (-(s : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hx s) (pow_le_pow_left₀ (le_of_lt hx) hxy s)

/-- Composing a positive concave scalar function with a negative integer
power is convex. This is enough for even-dimensional determinant moments. -/
theorem convexOn_neg_nat_zpow_of_concave {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ I f) (hpos : ∀ x ∈ I, 0 < f x) (s : ℕ) :
    ConvexOn ℝ I (fun x => f x ^ (-(s : ℤ))) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hxpos := hpos x hx
  have hypos := hpos y hy
  have hmixpos : 0 < p * f x + q * f y := by
    exact (convex_Ioi (0 : ℝ)) hxpos hypos hp hq hpq
  have hconc := hf.2 hx hy hp hq hpq
  have hpow := neg_nat_zpow_antitone s hmixpos hconc
  have hscalar := (convexOn_zpow (𝕜 := ℝ) (-(s : ℤ))).2 hxpos hypos hp hq hpq
  exact hpow.trans hscalar

/-- The inverse powers of a positive concave quadratic are convex on every
convex domain where that quadratic stays positive. -/
theorem convexOn_quadratic_neg_nat_zpow (c b a : ℝ) (ha : 0 ≤ a)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hpos : ∀ t ∈ I, 0 < c + b * t - a * t ^ 2) (s : ℕ) :
    ConvexOn ℝ I (fun t => (c + b * t - a * t ^ 2) ^ (-(s : ℤ))) := by
  apply convexOn_neg_nat_zpow_of_concave _ hpos s
  exact (concaveOn_quadratic c b a ha).subset (Set.subset_univ _) hI

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.convexOn_quadratic_neg_nat_zpow
