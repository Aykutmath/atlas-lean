import GaussianEllipsoid.DSABThread

/- Reconstructed from preserved consumer and proved DSAB/Huber interfaces.
   This is a new source, not a recovered original. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianEllipsoid

theorem paper_huber_good_shift
    (n : ℕ → ℕ) (α : ℝ) (hn : ∀ d, 0 < n d)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α)) (hα : 0 < α)
    (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hBM : BMminRisk n lo hi) :
    ∃ K : ℝ, 0 < K ∧ ∃ Good : ∀ d, Set (Sample d (n d)),
      Tendsto (fun d => (gaussianSampleLaw d (n d)).real (Good d)ᶜ) atTop (𝓝 0) ∧
      ∀ᶠ d in atTop, ∀ x ∈ Good d, ∀ j : Fin (n d), ∀ S : Square d,
        IsDeletedMinimizer lo hi x j S → |deletedMeanShift d S| ≤ K := by
  let A : ℝ := 450/97
  let B : ℝ := 900/97
  have hA : 0 < A := by norm_num [A]
  have hB : 0 ≤ B := by norm_num [B]
  let K := hi * (A / Real.sqrt α + 1) + (Real.sqrt 2 + 2) + 1
  let Good : ∀ d, Set (Sample d (n d)) := fun d =>
    {x | bmMinRisk d (n d) x lo hi 1 < 1/2} ∩
    {x | ∀ j : Fin (n d), matrixOpNorm (deletedCovariance x j - 1) ≤ covC_gen A B n d}
  have hhi : 0 < hi := hlo.trans_le hle
  refine ⟨K, by dsimp [K]; positivity, Good, ?_, ?_⟩
  · have hb := bm_good_event hBM (by norm_num : (0:ℝ) < 1/4)
    have hc := GGlue.tendsto_two_mul_exp_neg_half.add (GGlue.tendsto_chi_union hα hn hconv)
    rw [add_zero] at hc
    have ht := hb.add hc
    rw [zero_add] at ht
    apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ ht
    filter_upwards [GGlue.eventually_good_index hα hn hconv] with d hd
    have hs : (Good d)ᶜ ⊆
        {x | (1/4:ℝ) < bmMinRisk d (n d) x lo hi 1} ∪
        {x | ∃ j : Fin (n d), covC_gen A B n d < matrixOpNorm (deletedCovariance x j - 1)} := by
      intro x hx
      by_cases hb0 : bmMinRisk d (n d) x lo hi 1 < 1/2
      · right
        have hnot : ¬ ∀ j : Fin (n d), matrixOpNorm (deletedCovariance x j - 1) ≤ covC_gen A B n d :=
          fun h => hx ⟨hb0,h⟩
        obtain ⟨j,hj⟩ := not_forall.mp hnot
        exact ⟨j,not_le.mp hj⟩
      · left
        change (1/4:ℝ) < bmMinRisk d (n d) x lo hi 1
        have h := le_of_not_gt hb0
        linarith
    have hcov := cov_good_tail_quarter_gen A B (by omega : 0 < d) hd.2.1 hd.2.2
      (dsClassicalCovariance_gen dsPerCenterTail_theorem)
    exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans
      (add_le_add (le_refl _) hcov))
  · have hcov := eventually_sqrt_mul_covC_le_gen A B hA hB hα hn hconv
    have hratio := (GGlue.tendsto_n_div_pred hα hconv).eventually
      (eventually_le_nhds (by norm_num : (1:ℝ) < 3/2))
    have hridge := (fin_C_half_tendsto ((|lo|+|hi|+1)^2)).eventually
      (eventually_le_nhds (by norm_num : (0:ℝ) < 1/4))
    filter_upwards [GGlue.eventually_good_index hα hn hconv,hcov,hratio,hridge] with d hd hc hr he
    intro x hx j S hS
    have hshift := onGood_shift_le x j hd.2.1 (by omega : 0 < d) hlo.le hle hS (hx.2 j) hx.1
    have hR : bmGoodR d (n d) lo hi (1/2) ≤ 1 := by
      unfold bmGoodR
      linarith
    have hroot := Real.sqrt_le_sqrt (show 2*bmGoodR d (n d) lo hi (1/2) ≤ 2 by linarith)
    have hmain := mul_le_mul_of_nonneg_left hc hhi.le
    dsimp [K]
    nlinarith

end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_huber_good_shift
