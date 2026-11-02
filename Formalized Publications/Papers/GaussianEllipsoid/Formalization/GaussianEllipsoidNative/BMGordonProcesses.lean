import BMGordonGeometry

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace BMGordon

theorem primaryCoefficient_continuous {n d : ℕ} :
    Continuous (fun p : Euclid n × HMat d => primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  rcases i with (i|i)|(i|i)
  · change Continuous (fun p : Euclid n × HMat d => p.1 i.1 * p.2 i.2.2 i.2.1)
    fun_prop
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem auxiliaryCoefficient_continuous {n d : ℕ} :
    Continuous (fun p : Euclid n × HMat d => auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  rcases i with (i|i)|(i|i)
  · exact continuous_const
  · exact continuous_const
  · change Continuous (fun p : Euclid n × HMat d => p.2 i.2 i.1)
    fun_prop
  · change Continuous (fun p : Euclid n × HMat d => p.1 i)
    fun_prop

theorem primary_path_continuous {n d : ℕ} {κ : ℝ} (ω : Space n d) :
    Continuous (fun p : UnitSample n × UnitCone d κ => primary p ω) := by
  exact (primaryCoefficient_continuous.comp
    (continuous_subtype_val.prodMap continuous_subtype_val)).inner continuous_const

theorem auxiliary_path_continuous {n d : ℕ} {κ : ℝ} (ω : Space n d) :
    Continuous (fun p : UnitSample n × UnitCone d κ => auxiliary p ω) := by
  exact (auxiliaryCoefficient_continuous.comp
    (continuous_subtype_val.prodMap continuous_subtype_val)).inner continuous_const

theorem primary_sample_continuous {n d : ℕ} {κ : ℝ} (p : UnitSample n × UnitCone d κ) :
    Continuous (primary p) := continuous_const.inner continuous_id

theorem auxiliary_sample_continuous {n d : ℕ} {κ : ℝ} (p : UnitSample n × UnitCone d κ) :
    Continuous (auxiliary p) := continuous_const.inner continuous_id

theorem primary_increment_integrable {n d : ℕ} {κ : ℝ}
    (p q : UnitSample n × UnitCone d κ) :
    Integrable (fun ω => (primary p ω-primary q ω)^2) (law n d) := by
  simpa only [primary,inner_sub_left] using
    GaussianVariance.euclidean_integrable_inner_sq
      (primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-primaryCoefficient (q.1 : Euclid n) (q.2 : HMat d))

theorem auxiliary_increment_integrable {n d : ℕ} {κ : ℝ}
    (p q : UnitSample n × UnitCone d κ) :
    Integrable (fun ω => (auxiliary p ω-auxiliary q ω)^2) (law n d) := by
  simpa only [auxiliary,inner_sub_left] using
    GaussianVariance.euclidean_integrable_inner_sq
      (auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-auxiliaryCoefficient (q.1 : Euclid n) (q.2 : HMat d))

theorem primary_increment_mean {n d : ℕ} {κ : ℝ}
    (p q : UnitSample n × UnitCone d κ) :
    (∫ ω, (primary p ω-primary q ω)^2 ∂law n d) =
      ‖primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-primaryCoefficient (q.1 : Euclid n) (q.2 : HMat d)‖^2 := by
  simpa only [primary,inner_sub_left] using
    GaussianVariance.euclidean_integral_inner_sq
      (primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-primaryCoefficient (q.1 : Euclid n) (q.2 : HMat d))

theorem auxiliary_increment_mean {n d : ℕ} {κ : ℝ}
    (p q : UnitSample n × UnitCone d κ) :
    (∫ ω, (auxiliary p ω-auxiliary q ω)^2 ∂law n d) =
      ‖auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-auxiliaryCoefficient (q.1 : Euclid n) (q.2 : HMat d)‖^2 := by
  simpa only [auxiliary,inner_sub_left] using
    GaussianVariance.euclidean_integral_inner_sq
      (auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)-auxiliaryCoefficient (q.1 : Euclid n) (q.2 : HMat d))

theorem increment_same_row {n d : ℕ} {κ : ℝ}
    (u : UnitSample n) (S T : UnitCone d κ) :
    (∫ ω, (auxiliary (u,S) ω-auxiliary (u,T) ω)^2 ∂law n d) =
      ∫ ω, (primary (u,S) ω-primary (u,T) ω)^2 ∂law n d := by
  rw [auxiliary_increment_mean,primary_increment_mean,coefficient_increment_same_row]

theorem increment_comparison {n d : ℕ} {κ : ℝ}
    (u v : UnitSample n) (S T : UnitCone d κ) :
    (∫ ω, (primary (u,S) ω-primary (v,T) ω)^2 ∂law n d) ≤
      ∫ ω, (auxiliary (u,S) ω-auxiliary (v,T) ω)^2 ∂law n d := by
  rw [primary_increment_mean,auxiliary_increment_mean]
  exact coefficient_increment_comparison u v S T

theorem primary_abs_le {n d : ℕ} {κ : ℝ}
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) : |primary p ω| ≤ 2*‖ω‖ := by
  have hn : ‖primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)‖ ≤ 2 := by
    have h := primaryCoefficient_norm_sq p.1 p.2
    nlinarith [norm_nonneg (primaryCoefficient (p.1 : Euclid n) (p.2 : HMat d))]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem auxiliary_abs_le {n d : ℕ} {κ : ℝ}
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) : |auxiliary p ω| ≤ 2*‖ω‖ := by
  have hn : ‖auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d)‖ ≤ 2 := by
    have h := auxiliaryCoefficient_norm_sq p.1 p.2
    nlinarith [norm_nonneg (auxiliaryCoefficient (p.1 : Euclid n) (p.2 : HMat d))]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- A single integrable envelope controls every finite restriction, independently of its size. -/
theorem envelope_integrable (n d : ℕ) : Integrable (fun ω : Space n d => 2*‖ω‖) (law n d) :=
  GaussianVariance.euclidean_integrable_norm.const_mul 2

def rowDrift {n : ℕ} (R : ℝ) (u : UnitSample n) : ℝ := -⟪(u : Euclid n),ones n⟫_ℝ/R

theorem rowDrift_continuous {n : ℕ} (R : ℝ) : Continuous (rowDrift (n := n) R) := by
  exact (continuous_subtype_val.inner continuous_const).neg.div_const R

theorem rowDrift_abs_le {n : ℕ} (R : ℝ) (u : UnitSample n) :
    |rowDrift R u| ≤ Real.sqrt n / |R| := by
  rw [rowDrift,abs_div,abs_neg]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [unitSample_norm,ones_norm,one_mul] using abs_real_inner_le_norm (u : Euclid n) (ones n)

end BMGordon
