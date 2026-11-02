import PaperRhoScalars
import PaperRegularHeadConditional
import CutoffThresholds

noncomputable section
open MeasureTheory ProbabilityTheory Module Filter
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoid
open scoped BigOperators ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Apply the regular-group theorem with the paper's literal c_rank=1/4,
C_reg=8q, arbitrary admissible rho, and h=floor(d/2). All current rows are
independent of the actual selected past sigma-field. -/
theorem paper_rho_projected_group_conditional
    (q rho : ℝ) (hq : 1<q) (hrho : 0<rho)
    (hrcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    {N p n d : ℕ} (hd : 8≤d)
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N) (hdisj : ∀ i j,eH i≠eJ j)
    (hbudget : (p:ℝ) ≤ rho*d)
    (u : Euclid n) {σ mass R S : ℝ} (hσ : 0<σ)
    (husum : ∑ i,(u i)^2=σ^2) (hmass : mass=∑ i,|u i|)
    (hRdef : R=mass^2/σ^2)
    (hlow : generalLow (8*q)*Real.log (d:ℝ) ≤ R)
    (hS : S≤rho*d) (hR : R≤16*q^2*S)
    (hcap : ∀ i,|u i|≤(8*q)*σ/Real.sqrt R) :
    (tensorGaussianLaw N (d/2))[({z | spectralNuclearNorm (projectedBilinear
      (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).1))
      (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).2))
      n d (selectSample eJ z) u) < generalProj (1/4) (8*q)*Real.sqrt d*mass}).indicator
      (1 : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → ℝ) | selectedSampleSigmaField eH]
        ≤ᵐ[tensorGaussianLaw N (d/2)]
      fun _ => Real.exp (-generalProj (1/4) (8*q)*(d:ℝ)*R) := by
  have hq0 : 0<q := by linarith
  have hdim := GaussianEllipsoidCandidate.rho_floor_half_margin rho (lt_min_iff.mp hrcap).1 d hd
  have hb : (1/4:ℝ)*(d:ℝ)+(p:ℝ) ≤ (d/2:ℕ) := by linarith
  have hu := GaussianEllipsoidCandidate.rho_effective_support_cap q rho
    (generalUp (1/4) (8*q)) d S R hq hrho (lt_min_iff.mp hrcap).2
    (by positivity : (0:ℝ)<d) hS hR
  exact projected_regular_head_half_dimension_conditional (by norm_num) (by positivity)
    eH eJ hdisj hb u hσ husum hmass hRdef hlow hu.le hcap

#print axioms paper_rho_projected_group_conditional
end GaussianEllipsoid.ProjectedClusters

namespace GaussianEllipsoidCandidate
/-- A single eventual threshold supplies all small-support/floor/logarithmic
requirements for any fixed q,T,rho and regular-group lower constant. -/
theorem eventually_paper_rho_numerics (q rho C : ℝ) (hq : 1<q) (hrho : 0<rho)
    (hC : 0<C) (T : ℕ) (hT : 0<T) :
    ∀ᶠ d : ℕ in atTop,8≤d ∧ 0<Real.log (d:ℝ) ∧
      (d:ℝ)/(16384*Real.log d) ≤ (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) ∧
      (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) ≤ rho*d ∧
      C*Real.log (d:ℝ) ≤ 3*(q-1)*(d:ℝ)/(262144*T*q^3*Real.log d) := by
  have hq0 : 0<q := by linarith
  have hqm : 0<q-1 := by linarith
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  have hc : 0<3*(q-1)/(262144*T*q^3) := by positivity
  have hlog := eventually_nat_log_le_mul_div_log (3*(q-1)/(262144*T*q^3)) C hc hC
  have hbudget := tendsto_natCast_atTop_atTop.eventually (eventually_sparse_budget_le_rho rho hrho)
  have hfloor := tendsto_natCast_atTop_atTop.eventually eventually_sparse_cutoff_bounds
  filter_upwards [eventually_ge_atTop (8:ℕ),hlog,hbudget,hfloor] with d hd hl hb hf
  refine ⟨hd,hf.1,hf.2.1,hb,?_⟩
  convert hl using 1 <;> ring

#print axioms eventually_paper_rho_numerics
end GaussianEllipsoidCandidate
