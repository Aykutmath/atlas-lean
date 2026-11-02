import MultiscaleScalar
import MultiscaleNet
import MultiscaleMGF
import MultiscaleBlocks
import DyadicRegularity
import DyadicPartition
import GreedyRecords

namespace GaussianEllipsoidCandidate

noncomputable def dyadicRecordLevels {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (N : ℕ) : List ℕ :=
  (List.range N).filter fun t => decide ((dyadicBin u amp t).Nonempty)

lemma mem_dyadicRecordLevels {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (N t : ℕ) :
    t ∈ dyadicRecordLevels u amp N ↔ t < N ∧ (dyadicBin u amp t).Nonempty := by
  simp [dyadicRecordLevels]

/-- Actual coefficient bins and greedy support-record selection, assembled.
The resulting groups cover precisely the nonempty dyadic levels, preserve
their order, have the required within-group support bounds, and have doubled
successive record supports. Dynamic range is unrestricted. -/
theorem exists_dyadic_record_decomposition {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, ∃ t ts, g = t :: ts ∧ (dyadicBin u amp t).Nonempty ∧
        ∀ s ∈ ts, (dyadicBin u amp s).card < 2 * (dyadicBin u amp t).card) ∧
      groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card) := by
  obtain ⟨N, hN, hcover, htail⟩ := finite_dyadic_partition u amp ha hcap
  obtain ⟨groups, hgroups⟩ := exists_recordGrouping
    (fun t => (dyadicBin u amp t).card) (dyadicRecordLevels u amp N)
  refine ⟨N, groups, hN, hcover, htail, hgroups.flatten_eq, ?_, hgroups.chain⟩
  intro g hg
  obtain ⟨t, ts, heq, hsmall⟩ := hgroups.regular g hg
  refine ⟨t, ts, heq, ?_, hsmall⟩
  have hflat : t ∈ groups.flatten := List.mem_flatten.mpr ⟨g, hg, by simp [heq]⟩
  rw [hgroups.flatten_eq] at hflat
  exact ((mem_dyadicRecordLevels u amp N t).1 hflat).2

end GaussianEllipsoidCandidate

#print axioms GaussianEllipsoidCandidate.geometric_prefix_mul_le
#print axioms GaussianEllipsoidCandidate.geometric_prefix_le
#print axioms GaussianEllipsoidCandidate.geometric_through_le
#print axioms GaussianEllipsoidCandidate.norm_add_ge_sub
#print axioms GaussianEllipsoidCandidate.norm_ge_from_approximation
#print axioms GaussianEllipsoidCandidate.sum_sq_le_sq_sum
#print axioms GaussianEllipsoidCandidate.retained_tail_absorption
#print axioms GaussianEllipsoidCandidate.coefficientMass_nonneg
#print axioms GaussianEllipsoidCandidate.coefficientMass_smul
#print axioms GaussianEllipsoidCandidate.synthesis_smul
#print axioms GaussianEllipsoidCandidate.synthesis_sub
#print axioms GaussianEllipsoidCandidate.synthesis_norm_le
#print axioms GaussianEllipsoidCandidate.synthesis_lower_of_net
#print axioms GaussianEllipsoidCandidate.synthesis_lower_of_unit_mass
#print axioms GaussianEllipsoidCandidate.exists_mgf_tail_parameter
#print axioms GaussianEllipsoidCandidate.lower_tail_of_mgf_radius
#print axioms GaussianEllipsoidCandidate.measure_many_independent_bad
#print axioms GaussianEllipsoidCandidate.measure_many_independent_bad_two_pow
#print axioms GaussianEllipsoidCandidate.finite_geometric_domination
#print axioms GaussianEllipsoidCandidate.dyadic_omitted_mass
#print axioms GaussianEllipsoidCandidate.dyadic_energy_sum
#print axioms GaussianEllipsoidCandidate.dyadic_mass_sum
#print axioms GaussianEllipsoidCandidate.dyadic_effective_support
#print axioms GaussianEllipsoidCandidate.bin_mass_le
#print axioms GaussianEllipsoidCandidate.bin_energy_le
#print axioms GaussianEllipsoidCandidate.dyadic_bins_upper
#print axioms GaussianEllipsoidCandidate.dyadic_bins_lower
#print axioms GaussianEllipsoidCandidate.exists_dyadic_level
#print axioms GaussianEllipsoidCandidate.dyadic_level_unique
#print axioms GaussianEllipsoidCandidate.mem_dyadicBin
#print axioms GaussianEllipsoidCandidate.dyadicBin_disjoint
#print axioms GaussianEllipsoidCandidate.finite_dyadic_partition
#print axioms GaussianEllipsoidCandidate.exists_recordGrouping
#print axioms GaussianEllipsoidCandidate.RecordGrouping.flatten_eq
#print axioms GaussianEllipsoidCandidate.RecordGrouping.regular
#print axioms GaussianEllipsoidCandidate.RecordGrouping.chain
#print axioms GaussianEllipsoidCandidate.mem_dyadicRecordLevels
#print axioms GaussianEllipsoidCandidate.exists_dyadic_record_decomposition
