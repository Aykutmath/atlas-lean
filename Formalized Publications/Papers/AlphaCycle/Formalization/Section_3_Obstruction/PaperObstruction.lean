import Section_3_Obstruction.Examples

/-! Exact atom-support and named-witness statements used in the paper's
four-variable and lifted examples. -/
noncomputable section

namespace AlphaCycle.FourVariable

theorem odd_support (a b c : Bool) :
    odd a b c ≠ 0 ↔ (c = true ↔ a = b) := by
  cases a <;> cases b <;> cases c <;> norm_num [odd]

theorem odd_parity_probability :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
      if (c = true ↔ a = b) then odd a b c else 0) = 1 := by
  norm_num [Fintype.sum_bool, odd]

theorem independent_marginals (c d : Bool) :
    (∑ j : Bool, independent c j) = 1 / 2 ∧
    (∑ i : Bool, independent i d) = 1 / 2 := by
  norm_num [Fintype.sum_bool, independent]

theorem independent_unequal_probability :
    (∑ c : Bool, ∑ d : Bool, if c ≠ d then independent c d else 0) = 1 / 2 := by
  norm_num [Fintype.sum_bool, independent]

/-- The two parity marginals already force the last two bits to agree on
every atom of positive mass; the third marginal is not needed here. -/
theorem parity_marginals_force_equality
    (q : Bool → Bool → Bool → Bool → ℝ)
    (hn : ∀ a b c d, 0 ≤ q a b c d)
    (h₁ : ∀ a b c, (∑ d : Bool, q a b c d) = odd a b c)
    (h₂ : ∀ a b d, (∑ c : Bool, q a b c d) = odd a b d) :
    ∀ a b c d, c ≠ d → q a b c d = 0 := by
  intro a b c d hcd
  have hfirst := h₁ a b c
  have hsecond := h₂ a b d
  have hn₁ := hn a b c false
  have hn₂ := hn a b c true
  have hn₃ := hn a b false d
  have hn₄ := hn a b true d
  cases a <;> cases b <;> cases c <;> cases d
  all_goals simp only [ne_eq, not_true_eq_false] at hcd
  all_goals norm_num [odd, Fintype.sum_bool] at hfirst hsecond
  all_goals linarith

theorem parity_marginals_unequal_probability_zero
    (q : Bool → Bool → Bool → Bool → ℝ)
    (hn : ∀ a b c d, 0 ≤ q a b c d)
    (h₁ : ∀ a b c, (∑ d : Bool, q a b c d) = odd a b c)
    (h₂ : ∀ a b d, (∑ c : Bool, q a b c d) = odd a b d) :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      if c ≠ d then q a b c d else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  intro d _
  split_ifs with h
  · exact parity_marginals_force_equality q hn h₁ h₂ a b c d h
  · rfl

end AlphaCycle.FourVariable

namespace AlphaCycle.NegativeVertex
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The point constructed from the specified four active vertices has the
claimed strict gap, with every other vertex fixed to one. -/
theorem selected_witness_gap (e : Fin 3 → Finset V) (u v b c : V)
    (hu : u ∈ Geometry.blockA e) (hv : v ∈ Geometry.blockA e)
    (hb : b ∈ Geometry.blockB e) (hc : c ∈ Geometry.blockC e) (huv : u ≠ v) :
    witness e u v b c ∈ allCycleRelaxation e ∧
    witness e u v b c ∉ multilinearPolytope (completedSupport e) := by
  simp only [Geometry.blockA, Geometry.blockB, Geometry.blockC,
    Finset.mem_sdiff, Finset.mem_inter] at hu hv hb hc
  have hub : u ≠ b := fun h => hb.2 (h ▸ hu.1.1)
  have huc : u ≠ c := fun h => hc.2 (h ▸ hu.1.2)
  have hvb : v ≠ b := fun h => hb.2 (h ▸ hv.1.1)
  have hvc : v ≠ c := fun h => hc.2 (h ▸ hv.1.2)
  have hbc : b ≠ c := fun h => hc.2 (h ▸ hb.1.1)
  refine ⟨witness_in_allCycleRelaxation e u v b c huv hu.2 hv.2 hb.2 hc.2, ?_⟩
  exact localMomentVector_not_mem_multilinearPolytope e (locals u v b c)
    (locals_consistent e u v b c hu.2 hv.2 hb.2 hc.2)
    (locals_not_realizable e u v b c huv hub huc hvb hvc hbc
      hu.1.1 hv.1.1 hc.1.1 hu.1.2 hv.1.2 hb.1.1 hb.1.2 hc.1.2)

end AlphaCycle.NegativeVertex

namespace AlphaCycle.Examples

/-- The actual common moment vector of the two odd-parity tables and the
independent table, in the paper's order `012`, `013`, `23`. -/
def fourVector : MomentVector (completedSupport parityFour) :=
  NegativeVertex.witness parityFour 0 1 3 2

theorem fourVector_allCycle_gap :
    fourVector ∈ allCycleRelaxation parityFour ∧
    fourVector ∉ multilinearPolytope (completedSupport parityFour) :=
  NegativeVertex.selected_witness_gap parityFour 0 1 3 2
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem fourVector_CER_gap :
    fourVector ∈ completeEdgeRelaxation parityFour ∧
    fourVector ∉ multilinearPolytope (completedSupport parityFour) :=
  ⟨fourVector_allCycle_gap.1.1, fourVector_allCycle_gap.2⟩

end AlphaCycle.Examples
