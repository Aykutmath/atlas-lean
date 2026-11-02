import BMSaddleCoordinates

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace BMSaddle

/-- The inner maximum over the actual unit-Frobenius bounded-condition PSD cone. -/
def rowObjective (n d : ℕ) (κ R : ℝ) (X : Sample n d) (u : Euclid n) : ℝ :=
  conditionedSupport d κ (combine X u) - ⟪u,ones n⟫_ℝ/R

/-- Actual Gaussian saddle statistic; attainment of both extrema is proved below. -/
def statistic (n d : ℕ) (κ R : ℝ) (X : Sample n d) : ℝ :=
  sInf (rowObjective n d κ R X '' Metric.sphere 0 1)

theorem rowObjective_continuous {n d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X : Sample n d) : Continuous (rowObjective n d κ R X) :=
  ((conditionedSupport_lipschitz hd hκ).continuous.comp
    (combineRightLM X).continuous_of_finiteDimensional).sub
    ((continuous_id.inner continuous_const).div_const R)

theorem unitSphere_nonempty {n : ℕ} (hn : 0 < n) : (Metric.sphere (0 : Euclid n) 1).Nonempty := by
  refine ⟨EuclideanSpace.basisFun (Fin n) ℝ ⟨0,hn⟩, ?_⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one ⟨0,hn⟩

theorem statistic_minimum {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X : Sample n d) :
    ∃ u : Euclid n, ‖u‖=1 ∧ statistic n d κ R X = rowObjective n d κ R X u ∧
      ∀ v : Euclid n, ‖v‖=1 → statistic n d κ R X ≤ rowObjective n d κ R X v := by
  obtain ⟨u,hu,hmin⟩ := (isCompact_sphere (0 : Euclid n) 1).exists_isMinOn (unitSphere_nonempty hn)
    (rowObjective_continuous hd hκ R X).continuousOn
  have hleast : IsLeast (rowObjective n d κ R X '' Metric.sphere 0 1) (rowObjective n d κ R X u) := by
    refine ⟨⟨u,hu,rfl⟩, ?_⟩
    rintro z ⟨v,hv,rfl⟩
    exact hmin hv
  have heq : statistic n d κ R X = rowObjective n d κ R X u := hleast.csInf_eq
  refine ⟨u, by simpa only [Metric.mem_sphere,dist_zero_right] using hu, heq, ?_⟩
  intro v hv
  rw [heq]
  apply hmin
  simpa only [Metric.mem_sphere,dist_zero_right] using hv

theorem statistic_le_rowObjective {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X : Sample n d) (u : Euclid n) (hu : ‖u‖=1) :
    statistic n d κ R X ≤ rowObjective n d κ R X u := by
  obtain ⟨v,hv,he,hmin⟩ := statistic_minimum hn hd hκ R X
  exact hmin u hu

theorem rowObjective_lipschitz_bound {n d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X Y : Sample n d) (u : Euclid n) (hu : ‖u‖=1) :
    |rowObjective n d κ R X u - rowObjective n d κ R Y u| ≤ ‖X-Y‖ := by
  have h := (conditionedSupport_lipschitz hd hκ).norm_sub_le (combine X u) (combine Y u)
  simp only [NNReal.coe_one,one_mul,Real.norm_eq_abs] at h
  have hc := combine_norm_le (X-Y) u
  rw [combine_sub_left,hu,mul_one] at hc
  unfold rowObjective
  rw [sub_sub_sub_cancel_right]
  exact h.trans hc

theorem statistic_le_add {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X Y : Sample n d) : statistic n d κ R X ≤ statistic n d κ R Y + ‖X-Y‖ := by
  obtain ⟨u,hu,hy,hmin⟩ := statistic_minimum hn hd hκ R Y
  have hx := statistic_le_rowObjective hn hd hκ R X u hu
  have hdiff := (abs_le.mp (rowObjective_lipschitz_bound hd hκ R X Y u hu)).2
  linarith

/-- The complete inf-max statistic has Gaussian Lipschitz constant exactly one. -/
theorem statistic_lipschitz {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    LipschitzWith 1 (statistic n d κ R) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm]
  apply abs_le.mpr
  have h1 := statistic_le_add hn hd hκ R X Y
  have h2 := statistic_le_add hn hd hκ R Y X
  rw [norm_sub_rev] at h2
  constructor <;> linarith

theorem conditionedSupport_maximum {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (G : HMat d) :
    ∃ S ∈ conditionedUnit d κ, conditionedSupport d κ G = ⟪G,operatorFrobenius S⟫_ℝ := by
  have hc : Continuous (fun S : Op d => ⟪G,operatorFrobenius S⟫_ℝ) :=
    continuous_const.inner (continuous_operatorFrobenius d d)
  obtain ⟨S,hS,hmax⟩ := (conditionedUnit_compact d κ).exists_isMaxOn (conditionedUnit_nonempty hd hκ) hc.continuousOn
  refine ⟨S,hS,?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨S,hS,rfl⟩,?_⟩
  rintro z ⟨T,hT,rfl⟩
  exact hmax hT

/-- The inner extremum is an attained maximum of the literal bilinear Gaussian payoff. -/
theorem rowObjective_maximum {n d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (R : ℝ) (X : Sample n d) (u : Euclid n) :
    ∃ S ∈ conditionedUnit d κ,
      rowObjective n d κ R X u = ⟪X,tensor u (operatorFrobenius S)⟫_ℝ - ⟪u,ones n⟫_ℝ/R ∧
      ∀ T ∈ conditionedUnit d κ,
        ⟪X,tensor u (operatorFrobenius T)⟫_ℝ - ⟪u,ones n⟫_ℝ/R ≤ rowObjective n d κ R X u := by
  obtain ⟨S,hS,heq⟩ := conditionedSupport_maximum hd hκ (combine X u)
  refine ⟨S,hS,?_,?_⟩
  · rw [rowObjective,heq,combine_pairing]
  · intro T hT
    have h := le_conditionedSupport (combine X u) hT
    rw [combine_pairing] at h
    exact sub_le_sub_right h _

/-- Nonnegative saddle value gives an exact standard-Gaussian affine solution.
Equality is allowed because the inner support maximum is genuinely attained. -/
theorem affine_feasible_of_statistic_nonneg {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R : ℝ} (hκ : 1 ≤ κ) (hR : 0 < R) (X : Sample n d)
    (hF : 0 ≤ statistic n d κ R X) :
    ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ ≤ R ∧
      measurement X (operatorFrobenius S) = ones n := by
  apply affine_feasible_of_unit_support hR (measurement X) (ones n)
  intro u hu
  have hrow := hF.trans (statistic_le_rowObjective hn hd hκ R X u hu)
  obtain ⟨S,hS,heq⟩ := conditionedSupport_maximum hd hκ (combine X u)
  refine ⟨S,hS,?_⟩
  rw [rowObjective,heq] at hrow
  rw [measurement_pairing]
  have hquot : ⟪u,ones n⟫_ℝ/R ≤ ⟪combine X u,operatorFrobenius S⟫_ℝ := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hR).mp hquot

end BMSaddle
