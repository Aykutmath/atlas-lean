import UCFixedRankFinal
import UCProjectSpectralPeeling

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianEllipsoid.PaperUpperAdapters
open UCFixedRankMargin

/-- Paper main-lemma-11-1: all symmetric matrices, not only PSD matrices.
The universal margin is selected before the aspect interval and fixed rank.
The exceptional event is written as existence of a strict violating witness. -/
theorem paper_fixedRank_symmetric :
    ∃ cStar : ℝ, 0 < cStar ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → ∀ K : ℕ,
      ∃ cK : ℝ, 0 < cK ∧ ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
        a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ b*(d:ℝ)^2 →
        (gaussianSampleLaw d n).real {x | ∃ A : Square d,
          A.transpose=A ∧ A.rank ≤ K ∧ frobeniusNorm A=1 ∧
          (1/(n:ℝ))*l1Size (center (measurementQ x A)) < cStar} ≤
            Real.exp (-cK*(d:ℝ)^2) := by
  refine ⟨margin, margin_pos, ?_⟩
  intro a b ha hab K
  refine ⟨rate*a, mul_pos rate_pos ha, ?_⟩
  filter_upwards [fixedRank_tail_eventually ha K] with d hd
  intro n hnlo hnhi
  have h := hd n hnlo
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hnlo rate_pos.le
  nlinarith

def paperPeelingBudget (τ δ : ℝ) : ℕ := Nat.ceil (2*Real.log (1/δ)/τ^2)+1

/-- The precise logarithmic rank budget displayed in paper main-lemma-11-2. -/
theorem paperPeelingBudget_sufficient {τ δ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1-τ^2)^(paperPeelingBudget τ δ) ≤ δ^2 := by
  let K := paperPeelingBudget τ δ
  have ht2 : 0 < τ^2 := sq_pos_of_pos hτ
  have hbase : 0 ≤ 1-τ^2 := by nlinarith
  have hb : 1-τ^2 ≤ Real.exp (-τ^2) := by
    linarith [Real.add_one_le_exp (-τ^2)]
  have hc : 2*Real.log (1/δ)/τ^2 ≤ (K:ℝ) := by
    have h := Nat.le_ceil (2*Real.log (1/δ)/τ^2)
    dsimp [K, paperPeelingBudget]
    push_cast
    linarith
  have hexp : (K:ℝ)*(-τ^2) ≤ 2*Real.log δ := by
    have h := (div_le_iff₀ ht2).mp hc
    rw [one_div, Real.log_inv] at h
    nlinarith
  calc
    _ ≤ (Real.exp (-τ^2))^K := pow_le_pow_left₀ hbase hb K
    _ = Real.exp ((K:ℝ)*(-τ^2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (2*Real.log δ) := Real.exp_le_exp.mpr hexp
    _ = δ^2 := by rw [show (2:ℝ)*Real.log δ = Real.log (δ^2) by rw [Real.log_pow]; norm_num, Real.exp_log (sq_pos_of_pos hδ)]

/-- Exact source-matrix version of the paper's stated peeling rank budget.
All PSD, orthogonality, normalization, and strict rho cutoff data are retained. -/
theorem paper_spectral_peeling {τ δ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (d : ℕ) (A : Square d) (hA : A.PosSemidef) (hF : frobeniusNorm A = 1) :
    ∃ H R : Square d,
      H.PosSemidef ∧ R.PosSemidef ∧ A=H+R ∧ H*R=0 ∧
      H.rank ≤ paperPeelingBudget τ δ ∧
      (frobeniusNorm R ≤ δ ∨
        ∃ ρ : ℝ, ∃ D : Square d,
          δ < ρ ∧ R=ρ • D ∧ D.PosSemidef ∧ H*D=0 ∧
          frobeniusNorm D=1 ∧ matrixOpNorm D ≤ τ) := by
  let T := frobeniusOperator (UCEscape.sourceFrobenius A)
  have hT : BMGeometry.IsPSD T := (UCEscape.sourceFrobenius_psd A).mpr hA
  have hn : ‖operatorFrobenius T‖ = 1 := by
    change ‖operatorFrobenius (frobeniusOperator (UCEscape.sourceFrobenius A))‖ = 1
    rw [operatorFrobenius_frobeniusOperator, UCEscape.sourceFrobenius_norm, hF]
  obtain ⟨j,hj,H,R,hH,hR,hdec,hcomp,hrange,hinner,hrank,hmrank,hstop⟩ :=
    BMGeometry.spectral_peeling_of_budget T hT hn hτ.le hτ1.le hδ.le
      (paperPeelingBudget_sufficient hτ hτ1 hδ hδ1)
  refine ⟨BMGeometry.opMatrix H,BMGeometry.opMatrix R,
    (BMGeometry.opMatrix_posSemidef_iff H).mpr hH,
    (BMGeometry.opMatrix_posSemidef_iff R).mpr hR,?_,?_,hmrank.trans hj,?_⟩
  · have h := congrArg BMGeometry.opMatrix hdec
    change BMGeometry.opMatrix (frobeniusOperator (UCEscape.sourceFrobenius A)) =
      BMGeometry.opMatrix (H+R) at h
    rw [UCEscape.opMatrix_sourceFrobenius, UCEscape.opMatrix_add] at h
    exact h
  · rw [← UCEscape.opMatrix_comp, hcomp, UCEscape.opMatrix_zero]
  · by_cases hs : ‖operatorFrobenius R‖ ≤ δ
    · exact Or.inl (by simpa only [UCEscape.frobeniusNorm_opMatrix] using hs)
    · obtain ⟨ρ,D,hρ,hRdec,hD,hHD,hDnorm,hDop⟩ :=
        BMGeometry.normalize_diffuse_tail hR hcomp hδ.le (lt_of_not_ge hs)
          (hstop.resolve_left hs)
      refine Or.inr ⟨ρ,BMGeometry.opMatrix D,hρ,?_,
        (BMGeometry.opMatrix_posSemidef_iff D).mpr hD,?_,?_,?_⟩
      · rw [hRdec, UCEscape.opMatrix_smul]
      · rw [← UCEscape.opMatrix_comp, hHD, UCEscape.opMatrix_zero]
      · simpa only [UCEscape.frobeniusNorm_opMatrix] using hDnorm
      · simpa only [UCEscape.matrixOpNorm_opMatrix] using hDop

#print axioms paper_spectral_peeling
#print axioms paperPeelingBudget_sufficient
#print axioms paper_fixedRank_symmetric
end GaussianEllipsoid.PaperUpperAdapters
