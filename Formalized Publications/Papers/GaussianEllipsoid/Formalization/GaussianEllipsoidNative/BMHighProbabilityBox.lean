import BMFeasibleSpectralBox

noncomputable section
set_option synthInstance.maxSize 512
open MeasureTheory ProbabilityTheory GaussianTensorMoments Filter
open GaussianEllipsoid BMGeometry
open scoped BigOperators InnerProductSpace Matrix Topology
namespace BMSpectralBridge

def coneFeasible (n d : ℕ) (κ R : ℝ) (G : Fin n → Op d) : Prop :=
  ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ ≤ R*Real.sqrt d ∧
    ∀ i, Matrix.trace (opMatrix (G i) * opMatrix S) = 1

def boxFeasible (n d : ℕ) (lo hi : ℝ) (G : Fin n → Op d) : Prop :=
  ∃ S : Matrix (Fin d) (Fin d) ℝ, S ∈ BMRescaling.spectralBox d lo hi ∧
    ∀ i, Matrix.trace (opMatrix (G i) * S) = 1

/-- Only the explicitly bounded mean-GOE event is lost in the final spectral conversion. -/
theorem box_failure_le_cone_failure {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R a : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : a*(d:ℝ)^2 ≤ n) :
    (Measure.pi (fun _ : Fin n => goeLaw d)).real
      {G | ¬boxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) G} ≤
    (Measure.pi (fun _ : Fin n => goeLaw d)).real {G | ¬coneFeasible n d κ R G} +
      2*Real.exp (-2*(d:ℝ)) := by
  have hsub : {G | ¬boxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) G} ⊆
      {G | ¬coneFeasible n d κ R G} ∪ {G | 32 < ‖meanOp n G‖} := by
    intro G hG
    by_cases hc : coneFeasible n d κ R G
    · right
      by_contra hm
      obtain ⟨S,hS,hR',hfeas⟩ := hc
      apply hG
      exact ⟨opMatrix S, feasible_fixed_spectralBox_thirtytwo hn hd hκ hR ha haspect
        G S hS hR' hfeas (le_of_not_gt hm), hfeas⟩
    · exact Or.inl hc
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add_right (meanGOE_thirtytwo_tail hn hd) _))

/-- The norm-event error vanishes, independently of the sample-count sequence. -/
theorem meanGOE_error_tendsto :
    Tendsto (fun d : ℕ => 2*Real.exp (-2*(d:ℝ))) atTop (𝓝 0) := by
  have hD : Tendsto (fun d : ℕ => 2*(d:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2) tendsto_natCast_atTop_atTop
  have he : Tendsto (fun d : ℕ => Real.exp (-2*(d:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hD
  simpa only [mul_zero] using he.const_mul 2

/-- Dimension-independent spectral endpoints inherit high probability from conditioned
cone feasibility. A positive eventual lower aspect is stated explicitly. -/
theorem box_failure_tendsto_zero (n : ℕ → ℕ) {κ R a : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ n d)
    (hcone : Tendsto (fun d => (Measure.pi (fun _ : Fin (n d) => goeLaw d)).real
      {G | ¬coneFeasible (n d) d κ R G}) atTop (𝓝 0)) :
    Tendsto (fun d => (Measure.pi (fun _ : Fin (n d) => goeLaw d)).real
      {G | ¬boxFeasible (n d) d (Real.sqrt a/(32*κ)) (κ*R) G}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hcone.add meanGOE_error_tendsto)
  filter_upwards [haspect, eventually_gt_atTop 0] with d haD hd
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hn : 0 < n d := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<a*(d:ℝ)^2) haD)
  exact box_failure_le_cone_failure hn hd hκ hR ha haD

/-- Literal original adapter constraints, with no operator realization in the event. -/
def actualBoxFeasible (n d : ℕ) (lo hi : ℝ) (z : Fin n → Fin (d*d) → ℝ) : Prop :=
  ∃ S : Matrix (Fin d) (Fin d) ℝ, S ∈ BMRescaling.spectralBox d lo hi ∧
    ∀ i, Matrix.trace (BMGaussianEquivalent.symmetrizedGaussianMatrix d (z i) * S) = 1

def actualConeFeasible (n d : ℕ) (κ R : ℝ) (z : Fin n → Fin (d*d) → ℝ) : Prop :=
  ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ ≤ R*Real.sqrt d ∧
    ∀ i, Matrix.trace (BMGaussianEquivalent.symmetrizedGaussianMatrix d (z i) * opMatrix S) = 1

/-- Nonasymptotic spectral-box conversion on the actual independent adapter-row source. -/
theorem actual_box_failure_le_cone_failure {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ R a : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : a*(d:ℝ)^2 ≤ n) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualBoxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) z} ≤
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible n d κ R z} + 2*Real.exp (-2*(d:ℝ)) := by
  have hsub : {z | ¬actualBoxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) z} ⊆
      {z | ¬actualConeFeasible n d κ R z} ∪
        {z | 32 < ‖meanOp n (fun i => actualGOEOp d (z i))‖} := by
    intro z hz
    by_cases hc : actualConeFeasible n d κ R z
    · right
      by_contra hm
      obtain ⟨S,hS,hR',hfeas⟩ := hc
      apply hz
      have hfeas' : ∀ i, Matrix.trace (opMatrix (actualGOEOp d (z i))*opMatrix S) = 1 := by
        simpa only [actualGOEOp_matrix] using hfeas
      exact ⟨opMatrix S, feasible_fixed_spectralBox_thirtytwo hn hd hκ hR ha haspect
        _ S hS hR' hfeas' (le_of_not_gt hm), hfeas⟩
    · exact Or.inl hc
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add_right (actualMeanGOE_thirtytwo_tail hn hd) _))

/-- Actual-adapter high-probability version of the BM §3.1.4 completion. -/
theorem actual_box_failure_tendsto_zero (n : ℕ → ℕ) {κ R a : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ n d)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ R z}) atTop (𝓝 0)) :
    Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualBoxFeasible (n d) d (Real.sqrt a/(32*κ)) (κ*R) z}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _
    (by simpa only [add_zero] using hcone.add meanGOE_error_tendsto)
  filter_upwards [haspect, eventually_gt_atTop 0] with d haD hd
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hn : 0 < n d := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<a*(d:ℝ)^2) haD)
  exact actual_box_failure_le_cone_failure hn hd hκ hR ha haD

end BMSpectralBridge

namespace BMSpectralBridge

/-- Vanishing failure probability implies success probability tending to one, even when
measurability of the existential success event has not been needed separately. -/
theorem probability_tendsto_one_of_failure_tendsto_zero
    {Ω : ℕ → Type*} [∀ d, MeasurableSpace (Ω d)]
    (μ : ∀ d, Measure (Ω d)) [∀ d, IsProbabilityMeasure (μ d)] (E : ∀ d, Set (Ω d))
    (h : Tendsto (fun d => (μ d).real (E d)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun d => (μ d).real (E d)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using h.const_sub 1) tendsto_const_nhds
  · intro d
    have hu := measureReal_union_le (μ := μ d) (E d) (E d)ᶜ
    rw [Set.union_compl_self, probReal_univ] at hu
    dsimp only
    linarith
  · intro d
    exact measureReal_le_one

/-- Original BM matrix feasibility in a fixed genuine Loewner box has probability tending
to one whenever conditioned-cone feasibility holds with vanishing failure probability. -/
theorem actual_box_probability_tendsto_one (n : ℕ → ℕ) {κ R a : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ n d)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ R z}) atTop (𝓝 0)) :
    Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualBoxFeasible (n d) d (Real.sqrt a/(32*κ)) (κ*R) z}) atTop (𝓝 1) := by
  letI : ∀ d, IsProbabilityMeasure (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))) := fun d => inferInstance
  exact probability_tendsto_one_of_failure_tendsto_zero _ _
    (actual_box_failure_tendsto_zero n hκ hR ha haspect hcone)

/-- The lower endpoint is strictly positive and independent of dimension. -/
theorem fixed_box_lower_positive {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) :
    0 < Real.sqrt a/(32*κ) := div_pos (Real.sqrt_pos.mpr ha) (mul_pos (by norm_num) hκ)

end BMSpectralBridge

namespace BMSpectralBridge

/-- The finite-dimensional success-probability form of the conversion. -/
theorem actual_cone_probability_sub_error_le_box_probability {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) {κ R a : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a) (haspect : a*(d:ℝ)^2 ≤ n) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | actualConeFeasible n d κ R z} - 2*Real.exp (-2*(d:ℝ)) ≤
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | actualBoxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) z} := by
  have hsub : {z | actualConeFeasible n d κ R z} ⊆
      {z | actualBoxFeasible n d (Real.sqrt a/(32*κ)) (κ*R) z} ∪
        {z | 32 < ‖meanOp n (fun i => actualGOEOp d (z i))‖} := by
    intro z hz
    by_cases hm : 32 < ‖meanOp n (fun i => actualGOEOp d (z i))‖
    · exact Or.inr hm
    · left
      obtain ⟨S,hS,hR',hfeas⟩ := hz
      have hfeas' : ∀ i, Matrix.trace (opMatrix (actualGOEOp d (z i))*opMatrix S) = 1 := by
        simpa only [actualGOEOp_matrix] using hfeas
      exact ⟨opMatrix S, feasible_fixed_spectralBox_thirtytwo hn hd hκ hR ha haspect
        _ S hS hR' hfeas' (le_of_not_gt hm), hfeas⟩
  have hu := (measureReal_mono (μ := Measure.pi
      (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))) hsub).trans (measureReal_union_le _ _)
  have ht := actualMeanGOE_thirtytwo_tail hn hd
  linarith

/-- Direct completion of BM (30) to fixed-box feasibility with probability tending to one.
The positive eventual lower aspect is explicit and is not inferred from a strict limsup. -/
theorem actual_box_probability_tendsto_one_of_cone_probability (n : ℕ → ℕ) {κ R a : ℝ}
    (hκ : 0 < κ) (hR : 0 ≤ R) (ha : 0 < a)
    (haspect : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ n d)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualConeFeasible (n d) d κ R z}) atTop (𝓝 1)) :
    Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | actualBoxFeasible (n d) d (Real.sqrt a/(32*κ)) (κ*R) z}) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hcone.sub meanGOE_error_tendsto) tendsto_const_nhds
  · filter_upwards [haspect, eventually_gt_atTop 0] with d haD hd
    have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
    have hn : 0 < n d := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<a*(d:ℝ)^2) haD)
    exact actual_cone_probability_sub_error_le_box_probability hn hd hκ hR ha haD
  · exact Eventually.of_forall (fun _ => measureReal_le_one)

end BMSpectralBridge
