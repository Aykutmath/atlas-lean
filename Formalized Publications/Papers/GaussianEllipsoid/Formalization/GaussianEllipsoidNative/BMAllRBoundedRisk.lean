import BMAllRThreshold
import BMBoundedRiskToL1

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace BMAllRTransfer
open BMBoundedRiskToL1

/-- A single dimension-free positive bounded-risk threshold forces an Lr-good
candidate on the same constraint set, whenever its uniform residual q-moment
is bounded. The real infimum need not be attained. -/
theorem exists_ground_threshold {r K ε a : ℝ} (hr : 1 ≤ r) (hrq : r < (4:ℝ)/3) (hK : 0 ≤ K) (hε : 0 < ε) (ha : 0 < a) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (V : Type*) (B : Set V), B.Nonempty →
      ∀ d n : ℕ, 0 < d → 0 < n → a*(d:ℝ)^2 ≤ n →
      ∀ y : V → Fin n → ℝ,
        (∀ T ∈ B, (∑ i, |y T i-1|^((4:ℝ)/3)) ≤ K*n) →
        boundedGround B d n y < τ →
        ∃ T ∈ B, (∑ i, |y T i-1|^r)/(n:ℝ) < ε := by
  obtain ⟨η,hη,hthreshold⟩ := BMAllRTransfer.exists_potential_threshold hr hrq hK hε
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

/-- The low-Lr failure event is contained in the moment failure event together
with a positive bounded-ground-risk event. No selection theorem is needed. -/
theorem Lr_failure_subset {Ω V : Type*} (B : Set V) (hB : B.Nonempty)
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) {a K ε τ r : ℝ}
    (hratio : a*(d:ℝ)^2 ≤ n) (y : Ω → V → Fin n → ℝ) (good : Set Ω)
    (hmoment : ∀ ω ∈ good, ∀ T ∈ B, (∑ i, |y ω T i-1|^((4:ℝ)/3)) ≤ K*n)
    (hthreshold : ∀ yy : V → Fin n → ℝ,
      (∀ T ∈ B, (∑ i, |yy T i-1|^((4:ℝ)/3)) ≤ K*n) →
      boundedGround B d n yy < τ → ∃ T ∈ B, (∑ i, |yy T i-1|^r)/(n:ℝ) < ε) :
    {ω | ¬∃ T ∈ B, (∑ i, |y ω T i-1|^r)/(n:ℝ) < ε} ⊆
      goodᶜ ∪ {ω | τ ≤ boundedGround B d n (y ω)} := by
  intro ω hω
  by_cases hg : ω ∈ good
  · right
    by_contra hr
    exact hω (hthreshold (y ω) (hmoment ω hg) (lt_of_not_ge hr))
  · exact Or.inl hg

/-- Quantitative probability transfer: the bounded-risk mean plus the actual
uniform-moment exceptional probability control Lr feasibility failure. -/
theorem exists_Lr_failure_probability_bound {r K ε a : ℝ}
    (hr : 1 ≤ r) (hrq : r < (4:ℝ)/3) (hK : 0 ≤ K) (hε : 0 < ε) (ha : 0 < a) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (Ω V : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Set V), B.Nonempty →
      ∀ d n : ℕ, 0 < d → 0 < n → a*(d:ℝ)^2 ≤ n →
      ∀ (y : Ω → V → Fin n → ℝ) (good : Set Ω),
        (∀ ω ∈ good, ∀ T ∈ B, (∑ i, |y ω T i-1|^((4:ℝ)/3)) ≤ K*n) →
        Integrable (fun ω => boundedGround B d n (y ω)) μ →
        μ.real {ω | ¬∃ T ∈ B, (∑ i, |y ω T i-1|^r)/(n:ℝ) < ε} ≤
          μ.real goodᶜ + (∫ ω, boundedGround B d n (y ω) ∂μ)/τ := by
  obtain ⟨τ,hτ,hthreshold⟩ := exists_ground_threshold hr hrq hK hε ha
  refine ⟨τ,hτ,?_⟩
  intro Ω V _ μ _ B hB d n hd hn hratio y good hmoment hI
  have hsub := Lr_failure_subset B hB d n hd hn hratio y good hmoment
    (hthreshold V B hB d n hd hn hratio)
  apply (measureReal_mono hsub).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add_right
  apply (le_div_iff₀ hτ).2
  simpa only [mul_comm] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => boundedGround_nonneg B hB d n (y ω)) hI τ

#print axioms exists_ground_threshold
#print axioms exists_Lr_failure_probability_bound
end BMAllRTransfer
