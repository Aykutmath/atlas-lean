import BMNetGroundExtension
import GOEUniformL1

/-!
# Actual GOE expectation-level operator-net ground extension

This specializes the proved generic continuum-ground extension to the actual
full-entry GOE sample law and the proved uniform empirical L1 event.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory BMUniformMoment BMGOEUniform BMNetGroundExtension GaussianTensorMoments
open scoped BigOperators

namespace BMGOENetGroundExtension

/-- Difference of actual expected net and continuum energies is bounded by the
expected absolute gap, with both integrability obligations discharged here. -/
theorem abs_expected_net_sub_ground_le_integral_abs
    {V Ω ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) (ell : Ω → ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφcont : Continuous φ) {M : ℝ} (hφbound : ∀ u, |φ u| ≤ M)
    (hell : ∀ i x, Continuous (fun ω => ell ω i x))
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty) :
    |(∫ ω, netGround t ht (energy d (ell ω) φ) ∂μ)-
      (∫ ω, ground B (energy d (ell ω) φ) ∂μ)| ≤
      ∫ ω, |netGround t ht (energy d (ell ω) φ)-ground B (energy d (ell ω) φ)| ∂μ := by
  have hiG := integrable_energy_ground μ d ell φ hφcont hφbound hell B hB
  have hiN := integrable_netGround_of_continuous_bounded μ t ht
    (fun ω => energy d (ell ω) φ)
    (fun x _ => continuous_energy_in_rows d ell φ hφcont hell x)
    (fun ω x _ => abs_energy_le d (ell ω) φ hφbound x)
  rw [← integral_sub hiN hiG]
  exact abs_integral_le_integral_abs

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (goeSampleLaw d n) := by
  unfold goeSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianProductLaw (Fin (d*d))) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))

/-- Sample-coordinate continuity of the literal GOE trace-pairing row. -/
theorem continuous_goeRow_sample {d n : ℕ} (i : Fin n) (T : SymOp d) :
    Continuous (fun z : Fin n → (Fin (d*d) → ℝ) => goeRow (z i) T) :=
  (continuous_goeRow T).comp (continuous_apply i)

/-- Actual GOE continuum-ground integrability under every finite sample law. -/
theorem integrable_goe_energy_ground {d n : ℕ}
    (μ : Measure (Fin n → (Fin (d*d) → ℝ))) [IsFiniteMeasure μ]
    (φ : ℝ → ℝ) (hφcont : Continuous φ) {M : ℝ} (hφbound : ∀ u, |φ u| ≤ M)
    (B : Set (SymOp d)) (hB : B.Nonempty) :
    Integrable (fun z => ground B
      (energy (V := SymOp d) (ι := Fin n) d (fun i => goeRow (z i)) φ)) μ := by
  exact integrable_energy_ground (V := SymOp d) (ι := Fin n) μ d
    (fun z i => goeRow (z i)) φ hφcont hφbound continuous_goeRow_sample B hB

/-- Full GOE expected operator-net gap, with a dimension-uniform constant on
any fixed positive n/d² window. Both minima and the continuum infimum are actual
objects; their integrability and the exceptional-event probability are proved. -/
theorem exists_goe_expected_net_ground_bound
    (a A : ℝ) (ha : 0 < a) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ d n : ℕ, 0 < d → 0 < n →
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ φ : ℝ → ℝ, ∀ L M : ℝ, 0 ≤ L → 0 ≤ M →
      Continuous φ → (∀ u v, |φ u-φ v| ≤ L*|u-v|) →
      (∀ u, 0 ≤ φ u) → (∀ u, |φ u| ≤ M) →
      ∀ B : Set (SymOp d), B.Nonempty →
      ∀ (t : Finset (SymOp d)) (ht : t.Nonempty), (∀ T ∈ t, T ∈ B) →
      ∀ η : ℝ, 0 ≤ η → (∀ T ∈ B, ∃ U ∈ t, ‖T-U‖ ≤ η) →
      (∫ z, |netGround t ht
          (energy (V := SymOp d) (ι := Fin n) d (fun i => goeRow (z i)) φ)-
        ground B (energy (V := SymOp d) (ι := Fin n) d (fun i => goeRow (z i)) φ)|
          ∂goeSampleLaw d n) ≤ L*C*η+2*A*M*Real.exp (-(n:ℝ)) := by
  obtain ⟨K,hK,hEvent⟩ := exists_goe_uniform_L1_constant a ha
  refine ⟨K*A, mul_pos hK (by linarith),?_⟩
  intro d n hd hn hlow hhigh φ L M hL hM hφcont hφ hφnonneg hφbound B hB t ht hsub η hη hnet
  obtain ⟨good,hgood,hq,hbad⟩ := hEvent d n hd hn hlow
  have hL1 : ∀ z ∉ goodᶜ, ∀ H : SymOp d,
      (∑ i, |goeRow (z i) H|) ≤ (K*n)*‖H‖ := by
    intro z hz
    exact hq z (by simpa using hz)
  have hmean := integral_abs_net_energy_ground_le (V := SymOp d) (ι := Fin n)
    (goeSampleLaw d n) d hd (fun z i => goeRow (z i)) φ hL
    (by positivity : 0 ≤ K*(n:ℝ)) hη hφcont hφ hφbound
    continuous_goeRow_sample B hB t ht hsub hnet goodᶜ hgood.compl hL1
  simp only [Fintype.card_fin] at hmean
  apply hmean.trans
  have hd2 : 0 < (d:ℝ)^2 := by positivity
  have hfirst : L*(K*(n:ℝ))*η/(d:ℝ)^2 ≤ L*(K*A)*η := by
    apply (div_le_iff₀ hd2).2
    have hm := mul_le_mul_of_nonneg_left hhigh
      (mul_nonneg (mul_nonneg hL hK.le) hη)
    nlinarith
  have hsecond : (n:ℝ)*M/(d:ℝ)^2 ≤ A*M := by
    apply (div_le_iff₀ hd2).2
    nlinarith [mul_le_mul_of_nonneg_right hhigh hM]
  have hpnonneg : 0 ≤ (goeSampleLaw d n).real goodᶜ := ENNReal.toReal_nonneg
  have hm1 := mul_le_mul_of_nonneg_right hsecond hpnonneg
  have hm2 := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ A*M)
  nlinarith

#print axioms abs_expected_net_sub_ground_le_integral_abs
#print axioms continuous_goeRow_sample
#print axioms integrable_goe_energy_ground
#print axioms exists_goe_expected_net_ground_bound

end BMGOENetGroundExtension
