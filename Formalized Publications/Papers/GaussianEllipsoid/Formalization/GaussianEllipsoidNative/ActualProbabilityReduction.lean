import ActualCapturedDeterministic

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- A fixed original-vector failure in the captured-mass branch is contained
in exactly two actual exceptional events. The sparse and atom events are the
same simultaneous events used by the final coefficient net. -/
theorem actual_fixed_captured_failure_subset {n d : ℕ} (hd : 24 ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 1 ≤ J) (hJup : J ≤ 17*(1+Real.log K))
    (hT : T = 40+4*⌈K⌉₊)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) :
    ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
      sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ⊆
    actualCapturedProjectionBad u amp ha groups T d p q hreg hflat ∪
      {X | actualCapturedCross u amp ha groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} := by
  rintro X ⟨⟨hbad, hsp⟩, hatom⟩
  by_cases hp : X ∈ actualCapturedProjectionBad u amp ha groups T d p q hreg hflat
  · exact Or.inl hp
  · right
    by_contra hcross
    have hgood := actual_captured_retained_lower hd u amp ha groups T p q hreg hflat hpq hq
      hbudget K J hK hJ hcapt X hsp hp (le_of_not_ge hcross)
    have hret := actual_fixed_failure_subset_retained u hu amp groups K J hK (by linarith)
      hJup T hT herr ⟨hbad, hatom⟩
    exact (not_lt_of_ge hgood) hret

/-- The projected-cluster exponent dominates the common cross-term exponent. -/
theorem projected_tail_le_common (d T : ℝ) (hd : 0 ≤ d) (hT : 0 < T)
    (hlog : 0 < Real.log d) :
    Real.exp (-3*d^2/(137438953472*T*Real.log d)) ≤
      Real.exp (-d^2/((2:ℝ)^67*T*Real.log d)) := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right
    (show (1/(2:ℝ)^67) ≤ 3/137438953472 by norm_num)
    (show 0 ≤ d^2/(T*Real.log d) by positivity)
  convert! neg_le_neg hh using 1 <;> norm_num <;> ring

/-- The macroscopic late-bin exponent also dominates the same common tail. -/
theorem late_tail_le_common (d T : ℝ) (hd : 0 ≤ d) (hT : 0 < T)
    (hlog : 1 ≤ Real.log d) :
    Real.exp (-d^2/(1048576*T)) ≤
      Real.exp (-d^2/((2:ℝ)^67*T*Real.log d)) := by
  apply Real.exp_le_exp.mpr
  have hlog0 : 0 < Real.log d := by linarith
  have hden : 1048576*T ≤ (2:ℝ)^67*T*Real.log d := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2:ℝ)^67*T by positivity)
    have ht : (1048576:ℝ)*T ≤ (2:ℝ)^67*T := mul_le_mul_of_nonneg_right (by norm_num) hT.le
    nlinarith
  have hh := div_le_div_of_nonneg_left (sq_nonneg d) (by positivity : 0 < 1048576*T) hden
  simpa only [neg_div] using neg_le_neg hh

end GaussianEllipsoidCandidate
