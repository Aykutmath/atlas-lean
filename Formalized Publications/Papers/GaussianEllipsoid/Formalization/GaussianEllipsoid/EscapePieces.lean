/-
Deterministic pieces of the Gaussian escape step (no Gordon
comparison/concentration input): the `2(1-a)(1-b)` increment algebra
conditional on the variance formulas, and the sphere-duality
identification `max_{y ∈ S^{r-1}} ⟨g,y⟩ = ‖g‖₂` (Cauchy-Schwarz half +
attaining witness, both zero and nonzero cases).

Mathematical source: paper.tex, lines 3465-3570.
-/
import GaussianEllipsoid.NormBridges

noncomputable section

namespace GaussianEllipsoid

open scoped BigOperators

/-! ### Increment algebra: VX - VY = 2(1-a)(1-b) -/

/-- Conditional variance-difference identity (paper l.3524-3530). -/
theorem escape_variance_difference (VX VY a b : ℝ)
    (hY : VY = 2 * (1 - a * b))
    (hX : VX = 2 * (1 - a) + 2 * (1 - b)) :
    VX - VY = 2 * (1 - a) * (1 - b) := by
  rw [hX, hY]
  ring

/-- The increment gap is nonnegative for `a ∈ [-1,1]`, `b ∈ [0,1]`. -/
theorem escape_increment_gap_nonneg (a b : ℝ)
    (_ha : -1 ≤ a) (_ha' : a ≤ 1) (_hb : 0 ≤ b) (_hb' : b ≤ 1) :
    0 ≤ 2 * (1 - a) * (1 - b) := by
  have h1 : (0 : ℝ) ≤ 1 - a := by linarith
  have h2 : (0 : ℝ) ≤ 1 - b := by linarith
  have := mul_nonneg h1 h2
  linarith

/-- Equality when `D' = D` (`b = 1`, paper l.3532). -/
theorem escape_increment_gap_eq_zero_of_b_eq_one (a : ℝ) :
    2 * (1 - a) * (1 - (1 : ℝ)) = 0 := by
  ring

/-- Equality when `y' = y` (`a = 1`, paper l.3532). -/
theorem escape_increment_gap_eq_zero_of_a_eq_one (b : ℝ) :
    2 * (1 - (1 : ℝ)) * (1 - b) = 0 := by
  ring

/-! ### Sphere duality: sup over S^{r-1} is the Euclidean norm -/

/-- Cauchy-Schwarz direction: `⟨g,y⟩ ≤ ‖g‖₂` for unit `y`. -/
theorem inner_le_euclidNorm_of_unit {r : ℕ} (g y : Fin r → ℝ)
    (hy : ∑ j, (y j) ^ 2 = 1) :
    ∑ j, g j * y j ≤ euclidNorm g := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g y
  rw [hy, mul_one] at hCS
  have h1 : ∑ j, g j * y j ≤ |∑ j, g j * y j| := le_abs_self _
  have h2 : |∑ j, g j * y j| = Real.sqrt ((∑ j, g j * y j) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  calc ∑ j, g j * y j ≤ |∑ j, g j * y j| := h1
    _ = Real.sqrt ((∑ j, g j * y j) ^ 2) := h2
    _ ≤ Real.sqrt (∑ j, (g j) ^ 2) := Real.sqrt_le_sqrt hCS
    _ = euclidNorm g := rfl

/-- The witness `y* = g/‖g‖` is a unit vector when `g ≠ 0`. -/
theorem unitWitness_norm_sq {r : ℕ} (g : Fin r → ℝ) (hg : g ≠ 0) :
    ∑ j, (g j / euclidNorm g) ^ 2 = 1 := by
  have hSpos : 0 < ∑ j, (g j) ^ 2 := by
    have hex : ∃ j, g j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hg (funext hcon)
    obtain ⟨j₀, hj₀⟩ := hex
    have hle : (g j₀) ^ 2 ≤ ∑ j, (g j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ j₀)
    have hpos : (0 : ℝ) < (g j₀) ^ 2 := by positivity
    linarith
  have he : euclidNorm g ≠ 0 := by
    unfold euclidNorm
    exact ne_of_gt (Real.sqrt_pos.mpr hSpos)
  have hdiv : ∀ j : Fin r, (g j / euclidNorm g) ^ 2
      = (g j) ^ 2 / (euclidNorm g) ^ 2 := fun j => div_pow _ _ _
  rw [Finset.sum_congr rfl (fun j _ => hdiv j)]
  rw [← Finset.sum_div]
  have hsq : (euclidNorm g) ^ 2 = ∑ j, (g j) ^ 2 := euclidNorm_sq g
  rw [hsq]
  exact div_self (ne_of_gt hSpos)

/-- The witness attains the bound when `g ≠ 0`. -/
theorem unitWitness_attains {r : ℕ} (g : Fin r → ℝ) (hg : g ≠ 0) :
    ∑ j, g j * (g j / euclidNorm g) = euclidNorm g := by
  have hSpos : 0 < ∑ j, (g j) ^ 2 := by
    have hex : ∃ j, g j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hg (funext hcon)
    obtain ⟨j₀, hj₀⟩ := hex
    have hle : (g j₀) ^ 2 ≤ ∑ j, (g j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ j₀)
    have hpos : (0 : ℝ) < (g j₀) ^ 2 := by positivity
    linarith
  have he : euclidNorm g ≠ 0 := by
    unfold euclidNorm
    exact ne_of_gt (Real.sqrt_pos.mpr hSpos)
  have hmul : ∀ j : Fin r, g j * (g j / euclidNorm g)
      = (g j) ^ 2 / euclidNorm g := by
    intro j
    rw [← mul_div_assoc, ← pow_two]
  rw [Finset.sum_congr rfl (fun j _ => hmul j)]
  rw [← Finset.sum_div]
  have hsq : (euclidNorm g) ^ 2 = ∑ j, (g j) ^ 2 := euclidNorm_sq g
  have hS : ∑ j, (g j) ^ 2 = euclidNorm g * euclidNorm g := by
    rw [← hsq, pow_two]
  rw [hS]
  field_simp

/-- Zero case: both sides vanish. -/
theorem inner_euclidNorm_zero_of_zero {r : ℕ} (y : Fin r → ℝ) :
    ∑ j, (0 : Fin r → ℝ) j * y j = 0 ∧ euclidNorm (0 : Fin r → ℝ) = 0 := by
  constructor
  · simp
  · unfold euclidNorm
    simp

/-! ## Fixed-point escape (UC7 slice C.2): escape margin ⇒ non-membership.

If `x` stays at distance `≥ r` from every point of `E` (the escape margin),
then `x` is not in the `r`-neighborhood of `E`. The escape-through-a-net
argument applies this at each net point; the margin itself comes from the
Gordon/concentration side as an explicit hypothesis upstream.
-/

/-- Escape margin implies non-membership in the r-neighborhood. -/
theorem notMem_of_escapeMargin {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {x : X} {r : ℝ}
    (hesc : ∀ y ∈ E, r ≤ dist x y) :
    x ∉ {z | ∃ y ∈ E, dist z y < r} := by
  intro hcon
  obtain ⟨y, hyE, hlt⟩ := hcon
  exact absurd (lt_of_lt_of_le hlt (hesc y hyE)) (lt_irrefl _)

/-- Ball form: escaping the boundary set keeps `x` out of the
r-neighborhood intersected with any ball. -/
theorem escapeOnBall_of_margin {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {x : X} {r : ℝ} {c : X} {R : ℝ}
    (hesc : ∀ y ∈ E, r ≤ dist x y) :
    x ∉ Metric.ball c R ∩ {z | ∃ y ∈ E, dist z y < r} := by
  intro hcon
  exact notMem_of_escapeMargin hesc hcon.2

end GaussianEllipsoid
