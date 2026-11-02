import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

noncomputable section
open Set Metric MeasureTheory Module
open scoped ENNReal NNReal

namespace GaussianEllipsoid

/-- A finite separated set in a ball obeys the dimension-sharp volumetric bound,
for every real finite-dimensional norm. -/
theorem separated_card_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) :
    (s.card : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε / 2
  let ρ : ℝ := R + δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    have := hsep c hc d hd hcd
    dsimp [δ]
    linarith
  have hA_sub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    simpa [ρ, dist_zero_right, add_comm] using add_le_add_right (hs x hx) δ
  have hvol :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset hd fun c _ => measurableSet_ball]
        simp [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hA_sub
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := μ.addHaar_ball_of_pos _ hρ
  have hvol' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hvol'
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using this
  calc
    (s.card : ℝ) ≤ ρ ^ finrank ℝ E / δ ^ finrank ℝ E :=
      (le_div_iff₀ (pow_pos hδ _)).2 hreal
    _ = (1 + 2 * R / ε) ^ finrank ℝ E := by
      rw [← div_pow]
      congr 1
      dsimp [ρ, δ]
      field_simp
      ring


/-- A uniform bound for finite separated subsets produces an internal finite net.
No completeness or compactness assumption is needed. -/
theorem exists_internal_net_of_packing_bound {E : Type*} [MetricSpace E]
    (T : Set E) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hbound : ∀ s : Finset E, (∀ x ∈ s, x ∈ T) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) → s.card ≤ N) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ T) ∧ s.card ≤ N ∧
      (∀ x ∈ T, ∃ y ∈ s, dist x y < ε) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) := by
  classical
  let P : Set (Finset E) := {s | (∀ x ∈ s, x ∈ T) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y)}
  have hfinite : (Finset.card '' P).Finite := by
    apply (Set.finite_le_nat N).subset
    rintro n ⟨s, hs, rfl⟩
    exact hbound s hs.1 hs.2
  have hnonempty : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨s, hs, hmax⟩ := Set.Finite.exists_maximalFor' Finset.card P hfinite hnonempty
  refine ⟨s, hs.1, hbound s hs.1 hs.2, ?_, hs.2⟩
  intro x hx
  by_contra hn
  have hfar : ∀ y ∈ s, ε ≤ dist x y := by
    simpa only [not_exists, not_and, not_lt] using hn
  have hxs : x ∉ s := by
    intro hxs
    have := hfar x hxs
    exact (not_le_of_gt hε) (by simpa only [dist_self] using this)
  have hinsert : insert x s ∈ P := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hys
      · rcases Finset.mem_insert.mp hz with hzx | hzs
        · exact (hyz (hyx.trans hzx.symm)).elim
        · simpa only [hyx] using hfar z hzs
      · rcases Finset.mem_insert.mp hz with hzx | hzs
        · simpa only [hzx, dist_comm] using hfar y hys
        · exact hs.2 y hys z hzs hyz
  have heq := hmax hinsert (Finset.card_le_card (Finset.subset_insert x s))
  rw [Finset.card_insert_of_notMem hxs] at heq
  omega

/-- Every subset of a finite-dimensional norm ball has an internal ε-net with
at most `(1 + 2R/ε)^dim` centers. The centers remain in the original set. -/
theorem exists_internal_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Set E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hT : ∀ x ∈ T, ‖x‖ ≤ R) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ T) ∧
      (s.card : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E ∧
      (∀ x ∈ T, ∃ y ∈ s, dist x y < ε) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ε ≤ dist x y) := by
  classical
  let B : ℝ := (1 + 2 * R / ε) ^ finrank ℝ E
  obtain ⟨s, hs, _, hnet, hsep⟩ :=
    exists_internal_net_of_packing_bound T hε ⌈B⌉₊ (by
      intro s hs hsep
      have hb := separated_card_le s hR hε (fun x hx => hT x (hs x hx)) hsep
      exact_mod_cast hb.trans (Nat.le_ceil B))
  exact ⟨s, hs, separated_card_le s hR hε (fun x hx => hT x (hs x hx)) hsep,
    hnet, hsep⟩


/-- An internal quarter-net of the unit sphere with at most `9^dim` points. -/
theorem exists_sphere_quarter_net (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 9 ^ n ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 →
        ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 4) := by
  obtain ⟨s, hs, hcard, hnet, _⟩ := exists_internal_net
    {x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1}
    (R := 1) (ε := 1 / 4) (by norm_num) (by norm_num)
    (fun x hx => le_of_eq hx)
  refine ⟨s, hs, ?_, ?_⟩
  · norm_num only [finrank_euclideanSpace_fin, one_div, Nat.cast_ofNat,
      inv_div, inv_one, mul_one, div_inv_eq_mul, mul_one, mul_one,
      show (1 + 2 * 1 / (1 / 4 : ℝ)) = 9 by norm_num] at hcard
    exact_mod_cast hcard
  · intro x hx
    simpa only [dist_eq_norm] using hnet x hx

/-- The dimension of the Euclidean operator space is exactly the product of dimensions. -/
theorem finrank_euclidean_operator (r k : ℕ) :
    finrank ℝ (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r)) = r * k := by
  rw [← (LinearMap.toContinuousLinearMap
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin k))
    (F' := EuclideanSpace ℝ (Fin r))).finrank_eq,
    Module.finrank_linearMap]
  simp [Nat.mul_comm]

/-- An internal operator-norm net, with ambient dimension `r*k` and no spurious
square-root rank factor. Any subset of the operator unit ball is allowed. -/
theorem exists_operator_unit_net (r k : ℕ)
    (T : Set (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r)))
    {ε : ℝ} (hε : 0 < ε) (hT : ∀ A ∈ T, ‖A‖ ≤ 1) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin r)),
      (∀ A ∈ s, A ∈ T) ∧ (s.card : ℝ) ≤ (1 + 2 / ε) ^ (r * k) ∧
      (∀ A ∈ T, ∃ B ∈ s, ‖A - B‖ < ε) := by
  obtain ⟨s, hs, hcard, hnet, _⟩ := exists_internal_net T
    (R := 1) (by norm_num) hε hT
  exact ⟨s, hs, by simpa only [mul_one, finrank_euclidean_operator] using hcard,
    fun A hA => by simpa only [dist_eq_norm] using hnet A hA⟩

end GaussianEllipsoid

#print axioms GaussianEllipsoid.separated_card_le
#print axioms GaussianEllipsoid.exists_internal_net_of_packing_bound
#print axioms GaussianEllipsoid.exists_internal_net

#print axioms GaussianEllipsoid.exists_sphere_quarter_net
#print axioms GaussianEllipsoid.finrank_euclidean_operator
#print axioms GaussianEllipsoid.exists_operator_unit_net
