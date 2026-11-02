import NuclearEntropy
import PolarDuality
import Mathlib.Topology.MetricSpace.CoveringNumbers

noncomputable section
open Finset Set
open scoped NNReal ENNReal
namespace GaussianEllipsoid

/-- The genuine nuclear ball in the Frobenius matrix metric. -/
def paperNuclearBall (r : ℕ) (R : ℝ) : Set (FrobeniusMatrix r r) :=
  {A | spectralNuclearNorm A ≤ R}

/-- Existing finite covers are covers in Mathlib's closed-ball convention,
with arbitrary external centers exactly as in the paper. -/
theorem nuclear_finite_cover_isCover (r : ℕ) {R ε : ℝ} (hε : 0 ≤ ε)
    (s : Finset (FrobeniusMatrix r r))
    (hs : ∀ A : FrobeniusMatrix r r, spectralNuclearNorm A ≤ R → ∃ B ∈ s, ‖A-B‖ ≤ ε) :
    Metric.IsCover (⟨ε,hε⟩ : ℝ≥0) (paperNuclearBall r R) (s : Set (FrobeniusMatrix r r)) := by
  apply Metric.isCover_iff_subset_iUnion_closedBall.mpr
  intro A hA
  obtain ⟨B,hB,hAB⟩ := hs A hA
  exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB,
    by
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖A-B‖ ≤ ε
      exact hAB⟩⟩

/-- The external covering number is finite and positive, so toNat loses no
information and its real logarithm is the ordinary finite covering entropy. -/
theorem paper_nuclear_external_covering_finite_pos (r : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R) < ⊤ ∧
    0 < Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R) := by
  obtain ⟨s,_,hs⟩ := exists_nuclear_frobenius_cover r hR hε
  have hc := (nuclear_finite_cover_isCover r hε.le s hs).externalCoveringNumber_le_encard
  have hcard : Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R) ≤ (s.card:ℕ∞) := by
    simpa using hc
  refine ⟨hcard.trans_lt (ENat.natCast_lt_top _), ?_⟩
  apply Metric.externalCoveringNumber_pos_iff.mpr
  exact ⟨0,by simpa [paperNuclearBall] using hR⟩

/-- Literal external log-covering-number statement of paper Lemma5.6, C=256.
Metric.externalCoveringNumber uses arbitrary centers and closed balls. -/
theorem paper_nuclear_ball_entropy (r : ℕ) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    Real.log ((Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0)
      (paperNuclearBall r R)).toNat : ℝ) ≤ 256*(r:ℝ)*R^2/ε^2 := by
  obtain ⟨s,hlog,hs⟩ := exists_nuclear_frobenius_log_cover r hR hε
  have hfinite := paper_nuclear_external_covering_finite_pos r hR hε
  have hc := (nuclear_finite_cover_isCover r hε.le s hs).externalCoveringNumber_le_encard
  have hcard : Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R) ≤ (s.card:ℕ∞) := by
    simpa using hc
  have hp : 0 < (Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R)).toNat :=
    ENat.toNat_pos hfinite.2.ne' (ne_of_lt hfinite.1)
  have hn : (Metric.externalCoveringNumber (⟨ε,hε.le⟩ : ℝ≥0) (paperNuclearBall r R)).toNat ≤ s.card := by
    exact_mod_cast (ENat.natCast_toNat_le_self _).trans hcard
  exact (Real.log_le_log (Nat.cast_pos.mpr hp) (Nat.cast_le.mpr hn)).trans hlog

/-- The displayed R=nu*r, epsilon=t*sqrt(r) specialization with the same C. -/
theorem paper_nuclear_ball_entropy_scaled (r : ℕ) (hr : 0 < r)
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    Real.log ((Metric.externalCoveringNumber
      (⟨t*Real.sqrt (r:ℝ),by positivity⟩ : ℝ≥0)
      (paperNuclearBall r (ν*(r:ℝ)))).toNat : ℝ) ≤
        256*(ν^2/t^2)*(r:ℝ)^2 := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have h := paper_nuclear_ball_entropy r (mul_nonneg hν hrR.le)
    (mul_pos ht (Real.sqrt_pos.mpr hrR))
  rw [mul_pow, mul_pow, Real.sq_sqrt hrR.le] at h
  convert h using 1 <;> field_simp <;> ring
end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_nuclear_ball_entropy
#print axioms GaussianEllipsoid.paper_nuclear_ball_entropy_scaled
