import BMRationalLossData
import BMExpectationLimits

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace BMBoundedRiskToL1

/-- Actual bounded empirical ground risk over a constraint set, with the BM
normalization d² and the fixed bounded smooth residual potential. -/
def boundedGround {V : Type*} (B : Set V) (d n : ℕ) (y : V → Fin n → ℝ) : ℝ :=
  sInf ((fun T => (∑ i, BMRationalLossData.potential (y T i))/(d:ℝ)^2) '' B)

theorem boundedGround_nonneg {V : Type*} (B : Set V) (hB : B.Nonempty)
    (d n : ℕ) (y : V → Fin n → ℝ) : 0 ≤ boundedGround B d n y := by
  apply le_csInf (hB.image _)
  rintro _ ⟨T,hT,rfl⟩
  apply div_nonneg _ (sq_nonneg _)
  exact Finset.sum_nonneg fun i _ => BMClippedL1Bridge.smoothLoss_nonneg _

/-- A single dimension-free positive bounded-risk threshold forces an L1-good
candidate on the same constraint set, whenever its uniform residual q-moment
is bounded. The real infimum need not be attained. -/
theorem exists_ground_threshold {K ε a : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (ha : 0 < a) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (V : Type*) (B : Set V), B.Nonempty →
      ∀ d n : ℕ, 0 < d → 0 < n → a*(d:ℝ)^2 ≤ n →
      ∀ y : V → Fin n → ℝ,
        (∀ T ∈ B, (∑ i, |y T i-1|^((6:ℝ)/5)) ≤ K*n) →
        boundedGround B d n y < τ →
        ∃ T ∈ B, (∑ i, |y T i-1|)/(n:ℝ) < ε := by
  obtain ⟨η,hη,hthreshold⟩ := BMRationalLossData.exists_potential_threshold hK hε
  refine ⟨a*η,mul_pos ha hη,?_⟩
  intro V B hB d n hd hn hratio y hmoment hground
  obtain ⟨r,⟨T,hT,rfl⟩,hTenergy⟩ := exists_lt_of_csInf_lt (hB.image
    (fun T => (∑ i, BMRationalLossData.potential (y T i))/(d:ℝ)^2)) hground
  refine ⟨T,hT,hthreshold n hn (y T) (hmoment T hT) ?_⟩
  have hd2 : 0 < (d:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hd)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).2
  have hs := (div_lt_iff₀ hd2).1 hTenergy
  have hr := mul_le_mul_of_nonneg_right hratio hη.le
  nlinarith

/-- The low-L1 failure event is contained in the moment failure event together
with a positive bounded-ground-risk event. No selection theorem is needed. -/
theorem L1_failure_subset {Ω V : Type*} (B : Set V) (hB : B.Nonempty)
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) {a K ε τ : ℝ}
    (hratio : a*(d:ℝ)^2 ≤ n) (y : Ω → V → Fin n → ℝ) (good : Set Ω)
    (hmoment : ∀ ω ∈ good, ∀ T ∈ B, (∑ i, |y ω T i-1|^((6:ℝ)/5)) ≤ K*n)
    (hthreshold : ∀ yy : V → Fin n → ℝ,
      (∀ T ∈ B, (∑ i, |yy T i-1|^((6:ℝ)/5)) ≤ K*n) →
      boundedGround B d n yy < τ → ∃ T ∈ B, (∑ i, |yy T i-1|)/(n:ℝ) < ε) :
    {ω | ¬∃ T ∈ B, (∑ i, |y ω T i-1|)/(n:ℝ) < ε} ⊆
      goodᶜ ∪ {ω | τ ≤ boundedGround B d n (y ω)} := by
  intro ω hω
  by_cases hg : ω ∈ good
  · right
    by_contra hr
    exact hω (hthreshold (y ω) (hmoment ω hg) (lt_of_not_ge hr))
  · exact Or.inl hg

/-- Quantitative probability transfer: the bounded-risk mean plus the actual
uniform-moment exceptional probability control L1 feasibility failure. -/
theorem exists_L1_failure_probability_bound {K ε a : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε) (ha : 0 < a) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (Ω V : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Set V), B.Nonempty →
      ∀ d n : ℕ, 0 < d → 0 < n → a*(d:ℝ)^2 ≤ n →
      ∀ (y : Ω → V → Fin n → ℝ) (good : Set Ω),
        (∀ ω ∈ good, ∀ T ∈ B, (∑ i, |y ω T i-1|^((6:ℝ)/5)) ≤ K*n) →
        Integrable (fun ω => boundedGround B d n (y ω)) μ →
        μ.real {ω | ¬∃ T ∈ B, (∑ i, |y ω T i-1|)/(n:ℝ) < ε} ≤
          μ.real goodᶜ + (∫ ω, boundedGround B d n (y ω) ∂μ)/τ := by
  obtain ⟨τ,hτ,hthreshold⟩ := exists_ground_threshold hK hε ha
  refine ⟨τ,hτ,?_⟩
  intro Ω V _ μ _ B hB d n hd hn hratio y good hmoment hI
  have hsub := L1_failure_subset B hB d n hd hn hratio y good hmoment
    (hthreshold V B hB d n hd hn hratio)
  apply (measureReal_mono hsub).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add_right
  apply (le_div_iff₀ hτ).2
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => boundedGround_nonneg B hB d n (y ω)) hI τ

#print axioms exists_ground_threshold
#print axioms exists_L1_failure_probability_bound
end BMBoundedRiskToL1
