import UCPeelingSmallTail

noncomputable section
open MeasureTheory ProbabilityTheory Filter BMGeometry
open scoped Topology BigOperators
namespace GaussianEllipsoid.UCPeelingSmallTail
open UCFixedRankMargin UCContinuityGeometry UCUniformContinuity

def exceptionRate : ℝ := rate/2

theorem exceptionRate_pos : 0<exceptionRate := half_pos rate_pos

/-- The exact source conicInf domain is nonempty in positive dimension. -/
theorem source_conic_values_nonempty {d n : ℕ} (hd : 0<d) (x : Sample d n) :
    {t : ℝ | ∃ A : Square d, A.PosSemidef ∧ frobeniusNorm A=1 ∧
      t=(1/(n:ℝ))*l1Size (center (measurementQ x A))}.Nonempty := by
  obtain ⟨S,hS⟩ := UCEscape.psdUnit_nonempty hd
  let A : Square d := opMatrix (frobeniusOperator S)
  have hA : A.PosSemidef := (opMatrix_posSemidef_iff _).mpr hS.1
  have hF : frobeniusNorm A=1 := by
    rw [UCEscape.frobeniusNorm_opMatrix,operatorFrobenius_frobeniusOperator]
    simpa only [Metric.mem_sphere,dist_zero_right] using hS.2
  exact ⟨conicMargin x A,A,hA,hF,rfl⟩

/-- No attainment assumption is needed to expose a matrix witness for a
strict conicInf failure. -/
theorem conicInf_bad_subset {d n : ℕ} (hd : 0<d) (c : ℝ) :
    {x : Sample d n | conicInf d n x<c} ⊆ allBadEvent d n c := by
  intro x hx
  obtain ⟨t,⟨A,hA,hF,rfl⟩,ht⟩ := exists_lt_of_csInf_lt (source_conic_values_nonempty hd x) hx
  exact ⟨A,hA,hF,ht⟩

/-- The two actual exceptions, kept distinct from the unresolved diffuse
branch and without any assumed concentration law. -/
def exceptionEvent (a : ℝ) (d n K : ℕ) : Set (Sample d n) :=
  badEvent d n K ∪ continuityException a d n

theorem exceptions_tail_eventually {a : ℝ} (ha : 0<a) (K : ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2≤n →
      (gaussianSampleLaw d n).real (exceptionEvent a d n K) ≤
        Real.exp (-exceptionRate*(n:ℝ)) := by
  have hra : 0<rate*a := mul_pos rate_pos ha
  obtain ⟨N,hN⟩ := exists_nat_ge (max 1 (2/(rate*a)))
  filter_upwards [fixedRank_tail_eventually ha K,eventually_ge_atTop N] with d hRank hd
  have hdR : (N:ℝ)≤d := by exact_mod_cast hd
  have hd1 : (1:ℝ)≤d := (le_max_left _ _).trans (hN.trans hdR)
  have hd2 : 2/(rate*a)≤d := (le_max_right _ _).trans (hN.trans hdR)
  have hdpos : 0<d := by exact_mod_cast (show (0:ℝ)<d by linarith)
  intro n haspect
  have hnR : (0:ℝ)<n := (mul_pos ha (sq_pos_of_pos (by exact_mod_cast hdpos))).trans_le haspect
  have hnpos : 0<n := by exact_mod_cast hnR
  have hnsize : 2≤rate*(n:ℝ) := by
    have hh := (div_le_iff₀ hra).mp hd2
    have hs : (d:ℝ)≤(d:ℝ)^2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hs hra.le
    have hn' := mul_le_mul_of_nonneg_left haspect rate_pos.le
    nlinarith
  have hr1 : rate≤1 := by norm_num [rate,UCConicPointTail.pointRate]
  have hcont := empiricalOperator_tail ha hdpos hnpos haspect
  have hexp : Real.exp (-(n:ℝ))≤Real.exp (-rate*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htwo : 2≤Real.exp (rate*(n:ℝ)/2) := by
    linarith [Real.add_one_le_exp (rate*(n:ℝ)/2)]
  calc
    _ ≤ (gaussianSampleLaw d n).real (badEvent d n K)+
        (gaussianSampleLaw d n).real (continuityException a d n) := measureReal_union_le _ _
    _ ≤ Real.exp (-rate*(n:ℝ))+Real.exp (-(n:ℝ)) := add_le_add (hRank n haspect) hcont
    _ ≤ 2*Real.exp (-rate*(n:ℝ)) := by linarith
    _ ≤ Real.exp (rate*(n:ℝ)/2)*Real.exp (-rate*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; unfold exceptionRate; congr 1; ring

/-- End-to-end source-level reduction. The only remaining probability is the
genuine normalized-diffuse event; the entire small-tail branch has been
proved to have a universal exponentially small exceptional probability. -/
theorem exists_source_probability_reduction {a τ : ℝ} (ha : 0<a) (hτ : 0<τ) :
    ∃ K : ℕ, (1-τ^2)^K≤tailCutoff a^2 ∧
      ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2≤n → ∀ c : ℝ, c≤peeledMargin →
        (gaussianSampleLaw d n).real {x | conicInf d n x<c} ≤
          Real.exp (-exceptionRate*(n:ℝ))+
            (gaussianSampleLaw d n).real (diffuseBadEvent a τ d n K c) := by
  obtain ⟨K,hK,hsplit⟩ := exists_peeling_bad_event_split ha hτ
  refine ⟨K,hK,?_⟩
  filter_upwards [exceptions_tail_eventually ha K,eventually_ge_atTop 1] with d hexc hd
  have hdpos : 0<d := by omega
  intro n haspect c hc
  have hnpos : 0<n := by
    have hh : (0:ℝ)<a*(d:ℝ)^2 := mul_pos ha (sq_pos_of_pos (by exact_mod_cast hdpos))
    exact_mod_cast hh.trans_le haspect
  calc
    _ ≤ (gaussianSampleLaw d n).real (allBadEvent d n c) :=
      measureReal_mono (conicInf_bad_subset hdpos c)
    _ ≤ (gaussianSampleLaw d n).real (exceptionEvent a d n K ∪ diffuseBadEvent a τ d n K c) :=
      measureReal_mono (hsplit d n hnpos c hc)
    _ ≤ (gaussianSampleLaw d n).real (exceptionEvent a d n K)+
        (gaussianSampleLaw d n).real (diffuseBadEvent a τ d n K c) := measureReal_union_le _ _
    _ ≤ _ := add_le_add (hexc n haspect) le_rfl

#print axioms source_conic_values_nonempty
#print axioms exceptions_tail_eventually
#print axioms exists_source_probability_reduction
end GaussianEllipsoid.UCPeelingSmallTail
