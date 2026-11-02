import GaussianBilinearContinuity

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianTensorTrace Filter
open scoped Topology
namespace GaussianTensorMoments

/-- General fixed-aspect continuity: the auxiliary covariance size is M*d.
No restriction n≤d² is imposed. -/
theorem gaussianBilinearOperator_aspect_norm_tail (M n h d : ℕ)
    (hM : 1 ≤ M) (hd : 0 < d) (hh : 0 < h) (hhd : h ≤ d)
    (hn : n ≤ (M*d)^2) :
    (tensorGaussianLaw n h).real
      {z | (96*((M:ℝ)+1))*Real.sqrt d < ‖gaussianBilinearOperator n h d z‖} ≤
      (h:ℝ)^2/(2:ℝ)^h := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hMR : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hhdR : (h:ℝ) ≤ d := by exact_mod_cast hhd
  have hsub : {z | (96*((M:ℝ)+1))*Real.sqrt d < ‖gaussianBilinearOperator n h d z‖} ⊆
      {z | 2048*(h+M*d : ℕ)^2 < ‖matrixCLM (tensorGaussianCovariance n h z)‖} := by
    intro z hz
    have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ (96*((M:ℝ)+1))*Real.sqrt d)
      (norm_nonneg (gaussianBilinearOperator n h d z))).mpr hz
    have hsqrt := Real.sq_sqrt hdR.le
    have hid := gaussianBilinearOperator_norm_sq n h d z
    have hid' : ‖gaussianBilinearOperator n h d z‖^2 * d =
        ‖matrixCLM (tensorGaussianCovariance n h z)‖ :=
      (eq_div_iff (ne_of_gt hdR)).mp hid
    have hs : ((h:ℝ)+(M:ℝ)*d)^2 ≤ (((M:ℝ)+1)*d)^2 := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      calc
        (h:ℝ)+(M:ℝ)*d ≤ (d:ℝ)+(M:ℝ)*d := add_le_add hhdR (le_refl _)
        _ = ((M:ℝ)+1)*d := by ring
    have hsq' : 9216*((M:ℝ)+1)^2*d < ‖gaussianBilinearOperator n h d z‖^2 := by
      rw [mul_pow, mul_pow, hsqrt] at hsq
      norm_num at hsq
      exact hsq
    have hstrong := mul_lt_mul_of_pos_right hsq' hdR
    have hbound : 2048*((h:ℝ)+(M:ℝ)*d)^2 ≤ 9216*((M:ℝ)+1)^2*d*d := by
      calc
        _ ≤ 2048*(((M:ℝ)+1)*d)^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
        _ = 2048*(((M:ℝ)+1)^2*(d:ℝ)^2) := by ring
        _ ≤ 9216*(((M:ℝ)+1)^2*(d:ℝ)^2) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = _ := by ring
    change 2048*((h+M*d : ℕ):ℝ)^2 < _
    push_cast
    exact hbound.trans_lt (hstrong.trans_eq hid')
  exact (measureReal_mono hsub).trans
    (tensorGaussianCovariance_norm_tail n (M*d) h
      (Nat.succ_le_of_lt (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hM) hd)) hh hn)

/-- Paper Lemma main-lemma-4-2, with arbitrary fixed positive aspect A and
literal h=floor(d/2). An explicit constant witnesses O_P(sqrt d). -/
theorem gaussianBilinearOperator_arbitrary_aspect_tendsto_zero
    (A : ℝ) (hA : 0 < A) :
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ → ℕ,
      (∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) →
      Tendsto (fun d => (tensorGaussianLaw (n d) (d/2)).real
        {z | L*Real.sqrt d < ‖gaussianBilinearOperator (n d) (d/2) d z‖})
        atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max A 1)
  have hAM : A < (M:ℝ) := (le_max_left A 1).trans_lt hM
  have hMR : (1:ℝ) < M := (le_max_right A 1).trans_lt hM
  have hMN : 1 ≤ M := by exact_mod_cast hMR.le
  have hAsq : A ≤ (M:ℝ)^2 := by nlinarith
  refine ⟨96*((M:ℝ)+1), by positivity, ?_⟩
  intro n hn
  have hupper := tensor_covariance_error_tendsto_zero.comp
    (Nat.tendsto_div_const_atTop (by norm_num : (2:ℕ)≠0))
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _ hupper
  filter_upwards [hn, eventually_ge_atTop 2] with d hnd hd
  have hnM : n d ≤ (M*d)^2 := by
    have hbound : (n d:ℝ) ≤ ((M:ℝ)*(d:ℝ))^2 := by
      calc
        (n d:ℝ) ≤ A*(d:ℝ)^2 := hnd
        _ ≤ (M:ℝ)^2*(d:ℝ)^2 := mul_le_mul_of_nonneg_right hAsq (sq_nonneg _)
        _ = ((M:ℝ)*(d:ℝ))^2 := (mul_pow _ _ _).symm
    exact_mod_cast hbound
  exact gaussianBilinearOperator_aspect_norm_tail M (n d) (d/2) d hMN
    (by omega) (by omega) (Nat.div_le_self d 2) hnM

end GaussianTensorMoments
#print axioms GaussianTensorMoments.gaussianBilinearOperator_aspect_norm_tail
#print axioms GaussianTensorMoments.gaussianBilinearOperator_arbitrary_aspect_tendsto_zero
