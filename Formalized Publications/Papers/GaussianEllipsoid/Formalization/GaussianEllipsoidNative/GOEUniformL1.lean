import GOEContinuousRows

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory Real Set BMUniformMoment
open scoped BigOperators ENNReal
namespace BMGOEUniform

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)

/-- A measurable uniform homogeneous L1 event under the actual independent
full-entry GOE sample law, with explicit finite-dimensional entropy. -/
theorem exists_goe_uniform_L1_event {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (t : ℝ) (ht : 0 < t) :
    ∃ E : Set (Fin n → (Fin (d*d) → ℝ)), MeasurableSet E ∧
      (∀ z ∈ E, ∀ T : SymOp d, (∑ i, |goeRow (z i) T|) ≤ (2*t*n)*‖T‖) ∧
      (goeSampleLaw d n).real Eᶜ ≤ (5:ℝ)^(d*d)*(8*exp 1/t)^n := by
  classical
  obtain ⟨s, hs, hcard, hnet⟩ := exists_symmetric_operator_half_net d
  let F : SymOp d → (Fin n → (Fin (d*d) → ℝ)) → ℝ :=
    fun T z => ∑ i, |goeRow (z i) T|
  let E : Set (Fin n → (Fin (d*d) → ℝ)) := {z | ∀ T ∈ s, F T z ≤ t*n}
  have hm (T : SymOp d) : Measurable (F T) :=
    Finset.measurable_sum _ (fun i _ =>
      (((continuous_goeRow T).measurable.comp (measurable_pi_apply i)).abs))
  have hE : MeasurableSet E := measurableSet_finset_forall_le s F (t*n) hm
  refine ⟨E, hE, ?_, ?_⟩
  · intro z hz T
    have h := goe_empirical_sum_le_of_half_net z s hnet (t*n) (by positivity) hz T
    simpa only [mul_assoc] using h
  · have hc : Eᶜ = ⋃ T ∈ s, {z | t*n < ∑ i, |goeRow (z i) T|} := by
      ext z
      simp [E, F]
    rw [hc]
    calc
      _ ≤ ∑ T ∈ s, (goeSampleLaw d n).real {z | t*n < ∑ i, |goeRow (z i) T|} :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _T ∈ s, (8*exp 1/t)^n := by
        apply Finset.sum_le_sum
        intro T hT
        exact goeRow_empirical_tail hd hn T (hs T hT).le t ht
      _ = (s.card:ℝ)*(8*exp 1/t)^n := by simp
      _ ≤ (5:ℝ)^(d*d)*(8*exp 1/t)^n := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- Actual GOE uniform empirical L1 control, already homogeneous in the test
operator. Only the positive lower d² aspect ratio is needed; n has no upper
restriction. The exceptional probability is at most exp(-n). -/
theorem exists_goe_uniform_L1_constant (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ d n : ℕ, 0 < d → 0 < n → a*(d:ℝ)^2 ≤ n →
      ∃ E : Set (Fin n → (Fin (d*d) → ℝ)), MeasurableSet E ∧
        (∀ z ∈ E, ∀ T : SymOp d, (∑ i, |goeRow (z i) T|) ≤ K*n*‖T‖) ∧
        (goeSampleLaw d n).real Eᶜ ≤ exp (-(n:ℝ)) := by
  let c : ℝ := 1+log 5/a
  let t : ℝ := 8*exp 1*exp c
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨2*t, by positivity, ?_⟩
  intro d n hd hn hlow
  obtain ⟨E, hE, hgood, hbad⟩ := exists_goe_uniform_L1_event hd hn t ht
  refine ⟨E, hE, hgood, hbad.trans ?_⟩
  have hratio : 8*exp 1/t = exp (-c) := by
    dsimp [t]
    rw [Real.exp_neg]
    field_simp
  rw [hratio]
  have hfive : (5:ℝ)^(d*d) = exp ((d:ℝ)^2*log 5) := by
    rw [show (d:ℝ)^2 = (d*d:ℕ) by push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hfive, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ log 5 := Real.log_nonneg (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hlow (div_nonneg hlog ha.le)
  dsimp [c]
  have hcancel : (log 5/a)*(a*(d:ℝ)^2) = log 5*(d:ℝ)^2 := by field_simp
  rw [hcancel] at hh
  nlinarith

#print axioms exists_goe_uniform_L1_event
#print axioms exists_goe_uniform_L1_constant
end BMGOEUniform
