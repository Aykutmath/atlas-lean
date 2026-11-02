import SupportedPolar
import OperatorFrobeniusEquiv
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Tactic

open MeasureTheory
open scoped InnerProductSpace

namespace GaussianEllipsoid

instance frobeniusMeasurableSpace (r q : ℕ) : MeasurableSpace (FrobeniusMatrix r q) := borel _
instance frobeniusBorelSpace (r q : ℕ) : BorelSpace (FrobeniusMatrix r q) := ⟨rfl⟩

/-- A Borel operator-contractive half-polar witness for every actual matrix.
A single countable dense sequence of contractions is fixed, and its first
successful member is selected measurably. No measurability of the spectral
basis or exact polar construction is assumed. -/
theorem exists_measurable_half_polar (r q : ℕ) :
    ∃ W : FrobeniusMatrix r q → (Euclid q →L[ℝ] Euclid r),
      Measurable W ∧ (∀ A, ‖W A‖ ≤ 1) ∧
      ∀ A, spectralNuclearNorm A / 2 ≤ ⟪A, operatorFrobenius (W A)⟫_ℝ := by
  classical
  let C := {T : Euclid q →L[ℝ] Euclid r // ‖T‖ ≤ 1}
  letI : Nonempty C := ⟨⟨0, by simp⟩⟩
  letI : SecondCountableTopology C :=
    TopologicalSpace.secondCountableTopology_induced C (Euclid q →L[ℝ] Euclid r) Subtype.val
  obtain ⟨seq, hseq⟩ := TopologicalSpace.exists_dense_seq C
  let p : ℕ → FrobeniusMatrix r q → Prop := fun n A =>
    spectralNuclearNorm A / 2 ≤ ⟪A, operatorFrobenius (seq n).val⟫_ℝ
  have hex : ∀ A : FrobeniusMatrix r q, ∃ n, p n A := by
    intro A
    by_cases hA : A = 0
    · refine ⟨0, ?_⟩
      simp [p, hA]
    · have hn : 0 < spectralNuclearNorm A := by
        have hne : spectralNuclearNorm A ≠ 0 := fun h => hA (spectralNuclear_eq_zero_iff A |>.mp h)
        exact lt_of_le_of_ne (spectralNuclear_nonneg A) (Ne.symm hne)
      let U : Set C := {W | spectralNuclearNorm A / 2 < ⟪A, operatorFrobenius W.val⟫_ℝ}
      have hU : IsOpen U := isOpen_lt continuous_const
        (continuous_const.inner ((continuous_operatorFrobenius r q).comp continuous_subtype_val))
      have hUne : U.Nonempty := by
        refine ⟨⟨polarWitness (frobeniusOperator A), norm_polarWitness_le _⟩, ?_⟩
        change spectralNuclearNorm A / 2 < ⟪A, operatorFrobenius (polarWitness (frobeniusOperator A))⟫_ℝ
        rw [inner_polarWitness_eq_nuclear]
        linarith
      obtain ⟨n, hnmem⟩ := hseq.exists_mem_open hU hUne
      exact ⟨n, le_of_lt hnmem⟩
  have hp : ∀ n, MeasurableSet {A : FrobeniusMatrix r q | p n A} := by
    intro n
    exact measurableSet_le ((continuous_spectralNuclear r q).div_const 2).measurable
      (continuous_id.inner continuous_const).measurable
  let W : FrobeniusMatrix r q → (Euclid q →L[ℝ] Euclid r) :=
    fun A => (seq (Nat.find (hex A))).val
  refine ⟨W, ?_, ?_, ?_⟩
  · have hf : ∀ n, Measurable (fun _A : FrobeniusMatrix r q => (seq n).val) :=
      fun n => measurable_const
    exact Measurable.find hf hp hex
  · intro A
    exact (seq (Nat.find (hex A))).property
  · intro A
    exact Nat.find_spec (hex A)

/-- A fixed measurable choice can be reused for every sample and block. -/
noncomputable def measurableHalfPolar (r q : ℕ) :
    FrobeniusMatrix r q → (Euclid q →L[ℝ] Euclid r) :=
  Classical.choose (exists_measurable_half_polar r q)

theorem measurable_measurableHalfPolar (r q : ℕ) : Measurable (measurableHalfPolar r q) :=
  (Classical.choose_spec (exists_measurable_half_polar r q)).1

theorem norm_measurableHalfPolar_le {r q : ℕ} (A : FrobeniusMatrix r q) :
    ‖measurableHalfPolar r q A‖ ≤ 1 :=
  (Classical.choose_spec (exists_measurable_half_polar r q)).2.1 A

theorem half_nuclear_le_pairing {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralNuclearNorm A / 2 ≤ ⟪A, operatorFrobenius (measurableHalfPolar r q A)⟫_ℝ :=
  (Classical.choose_spec (exists_measurable_half_polar r q)).2.2 A

#print axioms continuous_operatorFrobenius
#print axioms exists_measurable_half_polar
#print axioms measurable_measurableHalfPolar
#print axioms norm_measurableHalfPolar_le
#print axioms half_nuclear_le_pairing

end GaussianEllipsoid
