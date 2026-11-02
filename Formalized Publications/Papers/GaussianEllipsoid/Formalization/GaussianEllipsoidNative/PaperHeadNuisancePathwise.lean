import PaperHeadNuisanceConditional

noncomputable section
open MeasureTheory Set Filter Module
open scoped BigOperators Topology
namespace UCEscape
open GaussianEllipsoid PaperUpperInfBridges PaperEmpiricalSupAdapter

/-- On the literal joint good event, the residual margin holds even for a
nuisance vector selected after observing all tail rows. The l1 cap follows from
the empirical continuity bound and a putative small residual. -/
theorem head_joint_good_margin {j p n : ℕ} {τ B c A : ℝ}
    (hn : 0<n) (hc1 : c≤1) (hBA : A+1<B)
    (g : Sample j n) (w : Sample p n)
    (hgood : (g,w) ∉ headJointFailure j p n τ B c A)
    (D : Square p) (hD : D.PosSemidef) (hF : frobeniusNorm D=1)
    (hOp : matrixOpNorm D≤τ) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ headNuisanceSpace g) :
    c ≤ (1/(n:ℝ))*(∑ i, |measurementQ w D i-v i|) := by
  classical
  by_contra hbad
  have hbad' := lt_of_not_ge hbad
  have hnot : ¬ (A:EReal)<empiricalSup p n w := fun hh => hgood (Or.inr hh)
  have hq : (1/(n:ℝ))*(∑ i, |measurementQ w D i|) ≤ A := by
    by_contra h
    apply hnot
    exact (empiricalSup_gt_iff p n A w).mpr ⟨D,(Matrix.isHermitian_iff_isSymm.mp hD.isHermitian),hF,lt_of_not_ge h⟩
  have htri : (∑ i, |v i|) ≤ (∑ i, |measurementQ w D i|)+
      (∑ i, |measurementQ w D i-v i|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := abs_sub (measurementQ w D i) (measurementQ w D i-v i)
    have he : measurementQ w D i-(measurementQ w D i-v i)=v i := by ring
    rw [he] at hh
    simpa only [sub_zero,zero_sub,abs_neg] using hh
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hnorm : (1/(n:ℝ))*(∑ i, |v i|) < B := by
    have hh := mul_le_mul_of_nonneg_left htri (by positivity : 0≤1/(n:ℝ))
    rw [mul_add] at hh
    linarith
  have hvB : (∑ i, |v i|) ≤ B*n := by
    have hh : (∑ i, |v i|)/(n:ℝ)<B := by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hnorm
    exact (div_lt_iff₀ hnR).mp hh |>.le
  apply hgood
  apply Or.inl
  exact ⟨D,hD,hF,hOp,v,hv,hvB,hbad'⟩

/-- Integrating an actual conditional indicator bound preserves the same
probability bound on an arbitrary probability space. -/
theorem probability_le_of_conditional_indicator {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m≤mΩ)
    (E : Set Ω) (hE : MeasurableSet E) (q : ℝ)
    (h : μ[E.indicator (1 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => q) : μ.real E ≤ q := by
  have hi := integral_mono_ae
    (integrable_condExp (μ := μ) (m := m) (f := E.indicator (1 : Ω → ℝ)))
    (integrable_const q : Integrable (fun _ : Ω => q) μ) h
  have hu : μ.real Set.univ=1 := by simp [Measure.real]
  simpa only [integral_condExp hm,integral_indicator_one hE,integral_const,hu,one_smul] using hi

/-- The source's unconditional statement is obtained by integrating its actual
head-conditional estimate, with the same constants and exceptional event. -/
theorem paper_head_joint_unconditional (ε B C₁ : ℝ)
    (hε : 0<ε) (hB : 0<B) (hC₁ : 0<C₁) :
    ∃ A τ c γ : ℝ, 0<A ∧ 0<τ ∧ τ≤1 ∧ 0<c ∧ 0<γ ∧
    ∀ᶠ p : ℕ in atTop, ∀ d j n K : ℕ, j≤K →
      (1/4+ε)*(p:ℝ)^2 ≤ (n:ℝ)-(1+K*(K+1)/2:ℕ) →
      (n:ℝ) ≤ C₁*(p:ℝ)^2 →
      ∀ e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p),
      (gaussianSampleLaw d n).real
        {x | gaussianSampleBlockSplit e n x ∈ headJointFailure j p n τ B c A} ≤
          3*Real.exp (-γ*(p:ℝ)^2) := by
  obtain ⟨A,τ,c,γ,hA,hτ,hτ1,hc,hγ,h⟩ := paper_head_joint_conditional ε B C₁ hε hB hC₁
  refine ⟨A,τ,c,γ,hA,hτ,hτ1,hc,hγ,?_⟩
  filter_upwards [h,eventually_gt_atTop 0] with p hp hp0
  intro d j n K hj hnlo hnhi e
  have hnlo' : (1/4+ε)*(p:ℝ)^2 ≤ n := hnlo.trans (sub_le_self _ (Nat.cast_nonneg _))
  have hn : 0<(n:ℝ) := (mul_pos (by linarith) (sq_pos_of_pos (Nat.cast_pos.mpr hp0))).trans_le hnlo'
  exact probability_le_of_conditional_indicator (headSampleSigmaField e n)
    (gaussianSampleLaw d n) ((gaussianSampleBlockSplit e n).measurable.fst.comap_le)
    _ ((gaussianSampleBlockSplit e n).measurable
      (headJointFailure_measurable j p n τ B c A (mul_pos hB hn))) _
    (hp d j n K hj hnlo hnhi e)

#print axioms paper_head_joint_unconditional
#print axioms head_joint_good_margin
end UCEscape
