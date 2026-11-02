import BMSpectralPositive
import BMConditionCone
import SpectralBlocks
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- The deterministic stopping argument. No assertion is made about the fixed K-tail
being diffuse: at some earlier stage the process may already have stopped. -/
theorem energy_decay_stopping (E m : ℕ → ℝ) {τ δ : ℝ} {K : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hE : E 0 ≤ 1)
    (hstep : ∀ j, E (j+1) = E j - (m j)^2)
    (hK : (1-τ^2)^K ≤ δ^2) :
    ∃ j ≤ K, E j ≤ δ^2 ∨ (m j)^2 ≤ τ^2 * E j := by
  by_contra! hn
  have hq : 0 ≤ 1-τ^2 := by nlinarith
  have hdec : ∀ j ≤ K, E j ≤ (1-τ^2)^j := by
    intro j hj
    induction j with
    | zero => simpa using hE
    | succ j ih =>
      have hjK : j ≤ K := by omega
      have hi := ih hjK
      have hm := (hn j hjK).2
      rw [hstep, pow_succ]
      calc
        E j - (m j)^2 ≤ (1-τ^2) * E j := by nlinarith
        _ ≤ (1-τ^2) * (1-τ^2)^j := mul_le_mul_of_nonneg_left hi hq
        _ = (1-τ^2)^j * (1-τ^2) := mul_comm _ _
  exact (not_le.mpr (hn K le_rfl).1) ((hdec K le_rfl).trans hK)

/-- A dimension-independent budget exists for every positive tolerance and cap < 1. -/
theorem exists_peeling_budget {τ δ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (hδ : 0 < δ) : ∃ K : ℕ, (1-τ^2)^K ≤ δ^2 := by
  have hq : 1-τ^2 < 1 := by nlinarith
  exact (exists_pow_lt_of_lt_one (sq_pos_of_pos hδ) hq).imp (fun _ h => h.le)

def spectralTailEnergy {d : ℕ} (a : Fin d → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if j ≤ i.val then (a i)^2 else 0

def paddedEigenvalue {d : ℕ} (a : Fin d → ℝ) (j : ℕ) : ℝ :=
  if h : j < d then a ⟨j,h⟩ else 0

theorem spectralTailEnergy_zero {d : ℕ} (a : Fin d → ℝ) :
    spectralTailEnergy a 0 = ∑ i, (a i)^2 := by simp [spectralTailEnergy]

theorem spectralTailEnergy_nonneg {d : ℕ} (a : Fin d → ℝ) (j : ℕ) :
    0 ≤ spectralTailEnergy a j := by
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem spectralTailEnergy_step {d : ℕ} (a : Fin d → ℝ) (j : ℕ) :
    spectralTailEnergy a (j+1) = spectralTailEnergy a j - (paddedEigenvalue a j)^2 := by
  classical
  have hsplit : spectralTailEnergy a j =
      (∑ i : Fin d, if i.val = j then (a i)^2 else 0) + spectralTailEnergy a (j+1) := by
    rw [spectralTailEnergy, spectralTailEnergy, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> first | omega | simp
  have hsingle : (∑ i : Fin d, if i.val = j then (a i)^2 else 0) =
      (paddedEigenvalue a j)^2 := by
    by_cases hj : j < d
    · rw [paddedEigenvalue, dif_pos hj]
      rw [Finset.sum_eq_single (⟨j,hj⟩ : Fin d)]
      · simp
      · intro i _ hne
        have hne' : i.val ≠ j := by intro h; apply hne; exact Fin.ext h
        simp [hne']
      · simp
    · rw [paddedEigenvalue, dif_neg hj]
      simp only [zero_pow (by omega : 2 ≠ 0)]
      apply Finset.sum_eq_zero
      intro i _
      have hne : i.val ≠ j := by omega
      simp [hne]
  linarith

/-- The scalar spectral stopping index exists before the dimension-independent budget. -/
theorem spectral_sequence_stopping {d : ℕ} (a : Fin d → ℝ) {τ δ : ℝ} {K : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha : ∑ i, (a i)^2 ≤ 1)
    (hK : (1-τ^2)^K ≤ δ^2) :
    ∃ j ≤ K, spectralTailEnergy a j ≤ δ^2 ∨
      (paddedEigenvalue a j)^2 ≤ τ^2 * spectralTailEnergy a j := by
  apply energy_decay_stopping (spectralTailEnergy a) (paddedEigenvalue a) hτ hτ1
  · simpa [spectralTailEnergy_zero] using ha
  · exact spectralTailEnergy_step a
  · exact hK

end BMGeometry
#print axioms BMGeometry.energy_decay_stopping
#print axioms BMGeometry.spectral_sequence_stopping
