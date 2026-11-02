import AHHProductRadialCutoff
import Mathlib.Algebra.Order.Chebyshev

/-! Quantitative differential control of the actual product radial cutoff.
All error constants here may depend on the finite number of blocks; they
multiply a cutoff energy tending to zero and do not alter angular constants. -/
noncomputable section
open Filter PaperSmoothCutoff
open scoped BigOperators Topology
namespace AHHRadial
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem lipschitz_norm_block (j : ι) :
    LipschitzWith 1 (fun z : PiLp 2 (fun _ : ι => E) => ‖z j‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [NNReal.coe_one, one_mul] using
    (dist_norm_norm_le (z j) (w j)).trans (by simpa only [dist_eq_norm] using
      (PiLp.dist_apply_le z w j))

theorem norm_fderiv_blockRadialCutoff_le (k : ℕ) (z : PiLp 2 (fun _ : ι => E)) :
    ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖ ≤
      ∑ j, |radialCutoffDerivative k ‖z j‖| := by
  by_cases hz : ∀ j, z j ≠ 0
  · let A : ι → (PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) := fun j =>
      radialCutoffDerivative k ‖z j‖ •
        fderiv ℝ (fun y : PiLp 2 (fun _ : ι => E) => ‖y j‖) z
    have hd (j : ι) : HasFDerivAt
        (fun y : PiLp 2 (fun _ : ι => E) => loss 1 (((k : ℝ) + 1) * ‖y j‖))
        (A j) z := by
      have hc : ContDiffAt ℝ 1 (fun y : PiLp 2 (fun _ : ι => E) => ‖y j‖) z :=
        (contDiffAt_piLp_apply 2).norm ℝ (hz j)
      have hn := hc.differentiableAt (by decide)
      exact (hasDerivAt_scaled_radialCutoff k ‖z j‖).comp_hasFDerivAt
        (f := fun y : PiLp 2 (fun _ : ι => E) => ‖y j‖) z hn.hasFDerivAt
    have hp := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd j)
    change HasFDerivAt (blockRadialCutoff k)
      (∑ j, (∏ l ∈ Finset.univ.erase j, loss 1 (((k : ℝ) + 1) * ‖z l‖)) • A j) z at hp
    rw [hp.fderiv]
    refine (norm_sum_le Finset.univ (fun j =>
      (∏ l ∈ Finset.univ.erase j, loss 1 (((k : ℝ) + 1) * ‖z l‖)) • A j)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    have hc0 : 0 ≤ ∏ l ∈ Finset.univ.erase j, loss 1 (((k : ℝ) + 1) * ‖z l‖) :=
      Finset.prod_nonneg fun l _ => loss_nonneg _ _
    have hc1 : (∏ l ∈ Finset.univ.erase j, loss 1 (((k : ℝ) + 1) * ‖z l‖)) ≤ 1 :=
      Finset.prod_le_one (fun l _ => loss_nonneg _ _) (fun l _ => loss_le_one _ _)
    have hA : ‖A j‖ ≤ |radialCutoffDerivative k ‖z j‖| := by
      dsimp only [A]
      have hn : ‖fderiv ℝ (fun y : PiLp 2 (fun _ : ι => E) => ‖y j‖) z‖ ≤ 1 :=
        by simpa only [NNReal.coe_one] using
          (norm_fderiv_le_of_lipschitz ℝ (lipschitz_norm_block (E := E) j) (x₀ := z))
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
        simpa only [mul_one, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left hn (abs_nonneg (radialCutoffDerivative k ‖z j‖)))
    apply (ContinuousLinearMap.opNorm_smul_le
      (∏ l ∈ Finset.univ.erase j, loss 1 (((k : ℝ) + 1) * ‖z l‖)) (A j)).trans
    rw [Real.norm_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hA hc0).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hc1
        (abs_nonneg (radialCutoffDerivative k ‖z j‖))))
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have he : blockRadialCutoff (ι := ι) (E := E) k =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      blockRadialCutoff_eventually_zero k z j hj
    rw [he.fderiv_eq, fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _

theorem norm_sq_fderiv_blockRadialCutoff_le (k : ℕ)
    (z : PiLp 2 (fun _ : ι => E)) :
    ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2 ≤
      (Fintype.card ι : ℝ) * ∑ j, (radialCutoffDerivative k ‖z j‖)^2 := by
  calc
    _ ≤ (∑ j, |radialCutoffDerivative k ‖z j‖|)^2 :=
      pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (blockRadialCutoff k) z))
        (norm_fderiv_blockRadialCutoff_le k z) 2
    _ ≤ _ := by
      simpa only [sq_abs, Finset.card_univ] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j => |radialCutoffDerivative k ‖z j‖|)

theorem norm_fderiv_blockRadialCutoff_uniform (k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t, |deriv (loss 1) t| ≤ M) (z : PiLp 2 (fun _ : ι => E)) :
    ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖ ≤
      (Fintype.card ι : ℝ) * (((k : ℝ) + 1) * M) := by
  apply (norm_fderiv_blockRadialCutoff_le k z).trans
  calc
    (∑ j, |radialCutoffDerivative k ‖z j‖|) ≤ ∑ _j : ι, (((k : ℝ) + 1) * M) := by
      apply Finset.sum_le_sum
      intro j _
      rw [radialCutoffDerivative, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hbound _) (by positivity)
    _ = _ := by simp

#print axioms norm_fderiv_blockRadialCutoff_le
#print axioms norm_sq_fderiv_blockRadialCutoff_le
#print axioms norm_fderiv_blockRadialCutoff_uniform
end AHHRadial
