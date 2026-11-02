import UCFixedRankFinal
import UCProjectSpectralPeeling

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCPeelingSmallTail
open UCContinuityGeometry UCUniformContinuity UCFixedRankGeometry UCFixedRankMargin

/-- This cutoff is chosen before the peeling rank budget. -/
def tailCutoff (a : ℝ) : ℝ := min (1/2) (margin/(8*continuityConstant a))
def peeledMargin : ℝ := margin/4

theorem tailCutoff_pos {a : ℝ} (ha : 0<a) : 0<tailCutoff a := by
  unfold tailCutoff
  exact lt_min (by norm_num) (by positivity [margin_pos,continuityConstant_pos ha])

theorem tailCutoff_le_half (a : ℝ) : tailCutoff a ≤ 1/2 := min_le_left _ _

theorem tailCutoff_error {a : ℝ} (ha : 0<a) :
    2*continuityConstant a*tailCutoff a ≤ margin/4 := by
  have h := (le_div_iff₀ (show 0<8*continuityConstant a by positivity [continuityConstant_pos ha])).mp
    (min_le_right (1/2:ℝ) (margin/(8*continuityConstant a)))
  change tailCutoff a * (8*continuityConstant a) ≤ margin at h
  nlinarith

theorem peeledMargin_pos : 0<peeledMargin := by unfold peeledMargin; positivity [margin_pos]

theorem conicMargin_smul {d n : ℕ} (x : Sample d n) (c : ℝ) (A : Square d) :
    conicMargin x (c • A) = |c| * conicMargin x A := by
  simp only [conicMargin,measurementQ_smul,center_smul,l1Size,Pi.smul_apply,smul_eq_mul,
    abs_mul,← Finset.mul_sum]
  ring

theorem psd_transpose {d : ℕ} (A : Square d) (hA : A.PosSemidef) : A.transpose=A := by
  simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian

/-- Normalizing a nonzero PSD head preserves its actual source matrix rank. -/
theorem normalized_head {d : ℕ} (H : Square d) (hH : H.PosSemidef)
    (hF : 0<frobeniusNorm H) :
    ((frobeniusNorm H)⁻¹ • H).PosSemidef ∧
      ((frobeniusNorm H)⁻¹ • H).rank=H.rank ∧
      frobeniusNorm ((frobeniusNorm H)⁻¹ • H)=1 := by
  refine ⟨hH.smul (inv_nonneg.mpr hF.le),?_,?_⟩
  · exact Matrix.rank_smul_of_mem_nonZeroDivisors H
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero (ne_of_gt hF)))
  · rw [frobeniusNorm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hF)]
    exact inv_mul_cancel₀ (ne_of_gt hF)

/-- The complete small-tail argument, on the two actual good events. -/
theorem smallTail_margin {a : ℝ} (ha : 0<a) {d n K : ℕ} (hn : 0<n)
    (x : Sample d n) (hRankGood : x ∉ badEvent d n K)
    (hContGood : ‖empiricalOperator x‖ ≤ continuityConstant a)
    (A H R : Square d) (hA : A.PosSemidef) (hH : H.PosSemidef)
    (hdec : A=H+R) (hRank : H.rank≤K)
    (henergy : frobeniusNorm H^2+frobeniusNorm R^2=1)
    (hsmall : frobeniusNorm R≤tailCutoff a) :
    peeledMargin ≤ conicMargin x A := by
  have hR0 := frobeniusNorm_nonneg R
  have hH0 := frobeniusNorm_nonneg H
  have hRhalf := hsmall.trans (tailCutoff_le_half a)
  have hHhalf : (1/2:ℝ)≤frobeniusNorm H := by nlinarith
  have hHpos : 0<frobeniusNorm H := by linarith
  obtain ⟨hNpsd,hNrank,hNF⟩ := normalized_head H hH hHpos
  have hNmargin : margin≤conicMargin x ((frobeniusNorm H)⁻¹ • H) := by
    by_contra hnot
    exact hRankGood ⟨_,psd_transpose _ hNpsd,hNrank.trans_le hRank,hNF,lt_of_not_ge hnot⟩
  rw [conicMargin_smul,abs_of_pos (inv_pos.mpr hHpos)] at hNmargin
  have hhead : margin*frobeniusNorm H ≤ conicMargin x H := by
    apply (le_div_iff₀ hHpos).mp
    simpa only [div_eq_mul_inv,mul_comm] using hNmargin
  have hhead' : margin/2≤conicMargin x H := by
    have hh := mul_le_mul_of_nonneg_left hHhalf margin_pos.le
    nlinarith
  have hdiff : A-H=R := by rw [hdec]; abel
  have hperturb := conicMargin_abs_sub_le hn x A H (psd_transpose _ hA)
    (psd_transpose _ hH) (continuityConstant a) hContGood
  rw [hdiff] at hperturb
  have herror := (mul_le_mul_of_nonneg_left hsmall
    (show 0≤2*continuityConstant a by positivity [continuityConstant_pos ha])).trans
    (tailCutoff_error ha)
  have hh := (abs_le.mp hperturb).1
  unfold peeledMargin
  linarith

/-- Source-level failures for all PSD Frobenius-unit matrices. -/
def allBadEvent (d n : ℕ) (c : ℝ) : Set (Sample d n) :=
  {x | ∃ A : Square d, A.PosSemidef ∧ frobeniusNorm A=1 ∧ conicMargin x A<c}

def continuityException (a : ℝ) (d n : ℕ) : Set (Sample d n) :=
  {x | continuityConstant a < ‖empiricalOperator x‖}

/-- A literal normalized-diffuse peeled witness, retaining all source
matrix geometry needed for complementary-frame compression. -/
def diffuseBadEvent (a τ : ℝ) (d n K : ℕ) (c : ℝ) : Set (Sample d n) :=
  {x | ∃ H D : Square d, ∃ ρ : ℝ,
    H.PosSemidef ∧ H.rank≤K ∧ D.PosSemidef ∧ H*D=0 ∧
    frobeniusNorm D=1 ∧ matrixOpNorm D≤τ ∧ tailCutoff a<ρ ∧ ρ≤1 ∧
    frobeniusNorm H^2+ρ^2=1 ∧ frobeniusNorm (H+ρ • D)=1 ∧
    conicMargin x (H+ρ • D)<c}

/-- Actual spectral peeling splits every full-cone failure into the two
proved exceptional events and a genuine non-small normalized diffuse event. -/
theorem exists_peeling_bad_event_split {a τ : ℝ} (ha : 0<a) (hτ : 0<τ) :
    ∃ K : ℕ, (1-τ^2)^K≤tailCutoff a^2 ∧
      ∀ (d n : ℕ), 0<n → ∀ c : ℝ, c≤peeledMargin → allBadEvent d n c ⊆
        badEvent d n K ∪ continuityException a d n ∪ diffuseBadEvent a τ d n K c := by
  obtain ⟨K,hK,hpeel⟩ := UCEscape.exists_project_spectral_peeling hτ (tailCutoff_pos ha)
  refine ⟨K,hK,?_⟩
  intro d n hn c hc x hx
  by_cases hRank : x ∈ badEvent d n K
  · exact Or.inl (Or.inl hRank)
  by_cases hCont : x ∈ continuityException a d n
  · exact Or.inl (Or.inr hCont)
  obtain ⟨A,hA,hF,hbad⟩ := hx
  obtain ⟨H,R,hH,hR,hdec,hzero,hRankH,henergy,hstop⟩ := hpeel d A hA hF
  rcases hstop with hsmall | ⟨ρ,D,hρ,hRdec,hD,hHD,hDF,hDop⟩
  · have hgood : ‖empiricalOperator x‖≤continuityConstant a := le_of_not_gt hCont
    have hm := smallTail_margin ha hn x hRank hgood A H R hA hH hdec hRankH henergy hsmall
    exact False.elim (not_lt_of_ge (hc.trans hm) hbad)
  · have hρpos : 0<ρ := (tailCutoff_pos ha).trans hρ
    have hRF : frobeniusNorm R=ρ := by
      rw [hRdec,frobeniusNorm_smul,Real.norm_eq_abs,abs_of_pos hρpos,hDF,mul_one]
    have henergy' : frobeniusNorm H^2+ρ^2=1 := by simpa only [hRF] using henergy
    have hρ1 : ρ≤1 := by nlinarith [sq_nonneg (frobeniusNorm H)]
    have hAdec : A=H+ρ • D := hdec.trans (by rw [hRdec])
    exact Or.inr ⟨H,D,ρ,hH,hRankH,hD,hHD,hDF,hDop,hρ,hρ1,henergy',
      hAdec ▸ hF,hAdec ▸ hbad⟩

/-- Probability reduction with every small-tail probabilistic ingredient
already discharged for the actual Gaussian sample measure. -/
theorem exists_peeling_probability_reduction {a τ : ℝ} (ha : 0<a) (hτ : 0<τ) :
    ∃ K : ℕ, (1-τ^2)^K≤tailCutoff a^2 ∧
      ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2≤n → ∀ c : ℝ, c≤peeledMargin →
        (gaussianSampleLaw d n).real (allBadEvent d n c) ≤
          Real.exp (-rate*(n:ℝ))+Real.exp (-(n:ℝ))+
            (gaussianSampleLaw d n).real (diffuseBadEvent a τ d n K c) := by
  obtain ⟨K,hK,hsplit⟩ := exists_peeling_bad_event_split ha hτ
  refine ⟨K,hK,?_⟩
  filter_upwards [fixedRank_tail_eventually ha K,eventually_ge_atTop 1] with d hRank hd
  intro n haspect c hc
  have hdpos : 0<d := by omega
  have hnpos : 0<n := by
    have hh : (0:ℝ)<a*(d:ℝ)^2 := mul_pos ha (sq_pos_of_pos (by exact_mod_cast hdpos))
    exact_mod_cast hh.trans_le haspect
  have hCont := empiricalOperator_tail ha hdpos hnpos haspect
  calc
    _ ≤ (gaussianSampleLaw d n).real
        (badEvent d n K ∪ continuityException a d n ∪ diffuseBadEvent a τ d n K c) :=
      measureReal_mono (hsplit d n hnpos c hc)
    _ ≤ (gaussianSampleLaw d n).real (badEvent d n K ∪ continuityException a d n)+
        (gaussianSampleLaw d n).real (diffuseBadEvent a τ d n K c) := measureReal_union_le _ _
    _ ≤ ((gaussianSampleLaw d n).real (badEvent d n K)+
        (gaussianSampleLaw d n).real (continuityException a d n))+
        (gaussianSampleLaw d n).real (diffuseBadEvent a τ d n K c) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (hRank n haspect) hCont) le_rfl

#print axioms smallTail_margin
#print axioms exists_peeling_bad_event_split
#print axioms exists_peeling_probability_reduction
end GaussianEllipsoid.UCPeelingSmallTail
