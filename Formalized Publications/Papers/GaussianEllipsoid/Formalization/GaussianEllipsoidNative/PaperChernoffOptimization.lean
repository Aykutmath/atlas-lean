import MultiscaleMGF
import GaussianRandomCompensator

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianEllipsoidCandidate

/-- Removing a random predictable compensator uses its pathwise upper bound;
plain exponential integrability is proved rather than assumed. -/
theorem paper_mgf_of_random_compensator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X v : Ω → ℝ) (hX : Measurable X) (lam V : ℝ)
    (hint : Integrable (fun ω => Real.exp (-lam*X ω-lam^2*v ω)) μ)
    (hcomp : (∫ ω, Real.exp (-lam*X ω-lam^2*v ω) ∂μ) ≤ 1)
    (hvar : ∀ᵐ ω ∂μ, v ω ≤ V) :
    Integrable (fun ω => Real.exp (-lam*X ω)) μ ∧
      mgf X μ (-lam) ≤ Real.exp (lam^2*V) := by
  have hdom : ∀ᵐ ω ∂μ, Real.exp (-lam*X ω) ≤
      Real.exp (lam^2*V)*Real.exp (-lam*X ω-lam^2*v ω) := by
    filter_upwards [hvar] with ω hω
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hω (sq_nonneg lam)]
  have hg := hint.const_mul (Real.exp (lam^2*V))
  have hf : Integrable (fun ω => Real.exp (-lam*X ω)) μ := by
    apply hg.mono' ((hX.const_mul (-lam)).exp.aestronglyMeasurable)
    filter_upwards [hdom] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hω
  refine ⟨hf,?_⟩
  calc
    mgf X μ (-lam) ≤ ∫ ω, Real.exp (lam^2*V)*Real.exp (-lam*X ω-lam^2*v ω) ∂μ :=
      integral_mono_ae hf hg hdom
    _ = Real.exp (lam^2*V)*(∫ ω, Real.exp (-lam*X ω-lam^2*v ω) ∂μ) := integral_const_mul _ _
    _ ≤ Real.exp (lam^2*V) := by nlinarith [Real.exp_pos (lam^2*V)]

/-- The exact parameter chosen in the source, with its admissible radius and
quadratic-exponent estimate. The constants are kept explicit. -/
theorem paper_chernoff_min_parameter (V B c x : ℝ)
    (hV : 0 < V) (hB : 0 < B) (hc : 0 < c) (hx : 0 ≤ x) :
    0 ≤ min (x/(2*V)) (c/(2*B)) ∧
    min (x/(2*V)) (c/(2*B)) ≤ c/B ∧
    -(min (x/(2*V)) (c/(2*B)))*x+(min (x/(2*V)) (c/(2*B)))^2*V ≤
      -(1/4:ℝ)*min (x^2/V) (c*x/B) := by
  have h0 : 0 ≤ min (x/(2*V)) (c/(2*B)) := le_min (by positivity) (by positivity)
  have hrad : min (x/(2*V)) (c/(2*B)) ≤ c/B :=
    (min_le_right _ _).trans (by apply div_le_div_of_nonneg_left hc.le hB; linarith)
  refine ⟨h0,hrad,?_⟩
  by_cases hcase : x*B ≤ c*V
  · have hmin : x/(2*V) ≤ c/(2*B) := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
    rw [min_eq_left hmin]
    have he : -(x/(2*V))*x+(x/(2*V))^2*V = -(1/4:ℝ)*(x^2/V) := by
      field_simp [hV.ne']; ring
    rw [he]
    exact mul_le_mul_of_nonpos_left (min_le_left _ _) (by norm_num)
  · have hcase' : c*V ≤ x*B := le_of_lt (lt_of_not_ge hcase)
    have hmin : c/(2*B) ≤ x/(2*V) := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
    rw [min_eq_right hmin]
    have hbound : V ≤ x*B/c := (le_div_iff₀ hc).mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg (c/(2*B)))
    have he : -(c/(2*B))*x+(c/(2*B))^2*(x*B/c) = -(1/4:ℝ)*(c*x/B) := by
      field_simp [hB.ne',hc.ne']; ring
    calc
      _ ≤ -(c/(2*B))*x+(c/(2*B))^2*(x*B/c) := by linarith
      _ = _ := he
      _ ≤ _ := mul_le_mul_of_nonpos_left (min_le_right _ _) (by norm_num)

/-- Literal Markov infimum over the whole admissible closed interval. -/
theorem paper_markov_mgf_infimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (V B c x : ℝ)
    (hB : 0 < B) (hc : 0 < c)
    (hint : ∀ lam, 0 ≤ lam → lam ≤ c/B → Integrable (fun ω => Real.exp ((-lam)*X ω)) μ)
    (hmgf : ∀ lam, 0 ≤ lam → lam ≤ c/B → mgf X μ (-lam) ≤ Real.exp (lam^2*V)) :
    μ.real {ω | X ω ≤ -x} ≤
      ⨅ lam : Set.Icc (0:ℝ) (c/B), Real.exp (-lam.val*x+lam.val^2*V) := by
  letI : Nonempty (Set.Icc (0:ℝ) (c/B)) := ⟨⟨0,le_rfl,by positivity⟩⟩
  apply le_ciInf
  intro lam
  calc
    _ ≤ Real.exp (-(-lam.val)*(-x))*mgf X μ (-lam.val) :=
      measure_le_le_exp_mul_mgf (-x) (neg_nonpos.mpr lam.property.1)
        (hint lam.val lam.property.1 lam.property.2)
    _ ≤ Real.exp (-(-lam.val)*(-x))*Real.exp (lam.val^2*V) :=
      mul_le_mul_of_nonneg_left (hmgf lam.val lam.property.1 lam.property.2) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The displayed infimum is bounded by the source's explicit minimum choice. -/
theorem paper_chernoff_infimum_bound (V B c x : ℝ)
    (hV : 0 < V) (hB : 0 < B) (hc : 0 < c) (hx : 0 ≤ x) :
    (⨅ lam : Set.Icc (0:ℝ) (c/B), Real.exp (-lam.val*x+lam.val^2*V)) ≤
      Real.exp (-(1/4:ℝ)*min (x^2/V) (c*x/B)) := by
  obtain ⟨hl0,hlmax,hopt⟩ := paper_chernoff_min_parameter V B c x hV hB hc hx
  have hb : BddBelow (Set.range (fun lam : Set.Icc (0:ℝ) (c/B) =>
      Real.exp (-lam.val*x+lam.val^2*V))) := ⟨0,by rintro y ⟨lam,rfl⟩; exact Real.exp_nonneg _⟩
  exact (ciInf_le hb ⟨min (x/(2*V)) (c/(2*B)),hl0,hlmax⟩).trans (Real.exp_le_exp.mpr hopt)


/-- Full source chain from the proved random compensator to Markov's infimum
and its explicitly chosen parameter. No plain-MGF premise is needed. -/
theorem paper_tail_from_random_compensator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X v : Ω → ℝ) (hX : Measurable X)
    (V B c x : ℝ) (hV : 0 < V) (hB : 0 < B) (hc : 0 < c) (hx : 0 ≤ x)
    (hcomp : ∀ lam, 0 ≤ lam → lam ≤ c/B →
      Integrable (fun ω => Real.exp (-lam*X ω-lam^2*v ω)) μ ∧
      (∫ ω,Real.exp (-lam*X ω-lam^2*v ω) ∂μ) ≤ 1)
    (hvar : ∀ᵐ ω ∂μ,v ω ≤ V) :
    μ.real {ω | X ω ≤ -x} ≤
      (⨅ lam : Set.Icc (0:ℝ) (c/B), Real.exp (-lam.val*x+lam.val^2*V)) ∧
    (⨅ lam : Set.Icc (0:ℝ) (c/B), Real.exp (-lam.val*x+lam.val^2*V)) ≤
      Real.exp (-(1/4:ℝ)*min (x^2/V) (c*x/B)) := by
  refine ⟨paper_markov_mgf_infimum μ X V B c x hB hc ?_ ?_,
    paper_chernoff_infimum_bound V B c x hV hB hc hx⟩
  · intro lam hl hr
    exact (paper_mgf_of_random_compensator μ X v hX lam V (hcomp lam hl hr).1
      (hcomp lam hl hr).2 hvar).1
  · intro lam hl hr
    exact (paper_mgf_of_random_compensator μ X v hX lam V (hcomp lam hl hr).1
      (hcomp lam hl hr).2 hvar).2

/-- At the homogeneous source threshold the sharp variance and radius produce
exactly the d² and d²/log d ratios, for arbitrary positive constants. -/
theorem paper_martingale_threshold_ratios (a M d CV CB V B : ℝ)
    (ha : 0 ≤ a) (hM : 0 < M) (hd : 0 < d) (hCV : 0 < CV) (hCB : 0 < CB)
    (hV : 0 < V) (hB : 0 < B)
    (hvar : V ≤ CV*M^2/d) (hrad : B ≤ CB*M*Real.log d/(d*Real.sqrt d)) :
    a^2*d^2/CV ≤ (a*M*Real.sqrt d)^2/V ∧
    a*d^2/(CB*Real.log d) ≤ (a*M*Real.sqrt d)/B := by
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hs := Real.sq_sqrt hd.le
  have hlog : 0 < Real.log d := by
    by_contra hn
    have hn' : Real.log d ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (mul_pos hCB hM).le hn'
    have hh := div_nonpos_of_nonpos_of_nonneg hp (mul_pos hd hroot).le
    linarith
  constructor
  · calc
      _ = (a*M*Real.sqrt d)^2/(CV*M^2/d) := by
        field_simp [hCV.ne',hM.ne',hd.ne']
        nlinarith [hs]
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hV hvar
  · calc
      _ = (a*M*Real.sqrt d)/(CB*M*Real.log d/(d*Real.sqrt d)) := by
        field_simp [hCB.ne',hM.ne',hd.ne',hroot.ne',hlog.ne']
        nlinarith [hs]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hB hrad


/-- The zero-future branch has zero positive-threshold lower-tail probability;
no reciprocal of a zero MGF-radius parameter is used. -/
theorem paper_zero_future_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : X =ᵐ[μ] 0) (x : ℝ) (hx : 0 < x) :
    μ.real {ω | X ω ≤ -x}=0 := by
  have he : {ω | X ω ≤ -x} =ᵐ[μ] (∅ : Set Ω) := by
    filter_upwards [hX] with ω hω
    simp only [Pi.zero_apply] at hω
    apply propext
    change X ω ≤ -x ↔ False
    simp [hω,not_le.mpr (neg_neg_of_pos hx)]
  rw [measureReal_congr he]
  simp

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_chernoff_min_parameter
#print axioms GaussianEllipsoidCandidate.paper_markov_mgf_infimum
#print axioms GaussianEllipsoidCandidate.paper_chernoff_infimum_bound

#print axioms GaussianEllipsoidCandidate.paper_mgf_of_random_compensator

#print axioms GaussianEllipsoidCandidate.paper_tail_from_random_compensator
#print axioms GaussianEllipsoidCandidate.paper_martingale_threshold_ratios

#print axioms GaussianEllipsoidCandidate.paper_zero_future_tail
