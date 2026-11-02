import UCFixedRankMargin

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianEllipsoid.UCFixedRankMargin

/-- Both constants are chosen before the fixed rank K. Only the eventual
dimension threshold depends on K and the aspect floor. -/
theorem exists_universal_fixedRank_margin :
    ∃ cStar cProb : ℝ, 0<cStar ∧ 0<cProb ∧
      ∀ a : ℝ, 0<a → ∀ K : ℕ, ∀ᶠ d : ℕ in atTop,
        ∀ n : ℕ, a*(d:ℝ)^2≤n →
          (gaussianSampleLaw d n).real {x | ∃ A : Square d,
            A.PosSemidef ∧ A.rank≤K ∧ frobeniusNorm A=1 ∧
            (1/(n:ℝ))*l1Size (center (measurementQ x A))<cStar} ≤
              Real.exp (-cProb*(n:ℝ)) := by
  refine ⟨margin,rate,margin_pos,rate_pos,?_⟩
  intro a ha K
  exact fixedRank_psd_tail_eventually ha K

theorem margin_eq : margin = 1/240000000 := by
  norm_num [margin,UCConicPointTail.pointMargin]

theorem rate_eq : rate = 1/115200000000000000 := by
  norm_num [rate,UCConicPointTail.pointRate]

#print axioms exists_universal_fixedRank_margin
#print axioms fixedRank_tail_of_large_dimension
#print axioms UCQuadraticSmallBall.paired_clip_mean
#print axioms UCConicPointTail.conicMargin_lower_tail
#print axioms UCFixedRankGeometry.exists_rank_unit_net
#print axioms UCFixedRankGeometry.conicMargin_abs_sub_le
end GaussianEllipsoid.UCFixedRankMargin
