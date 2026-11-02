import UCContinuumTransfer

noncomputable section
open MeasureTheory BMClippedL1Bridge
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators
namespace GaussianEllipsoid.UCContinuumTransfer

theorem meanLoss_abs_sub_l1_le {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A B : Square d) (hA : A.transpose = A) (hB : B.transpose = B)
    (v w : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : ‖empiricalOperator x‖ ≤ C) :
    |meanLoss x A v-meanLoss x B w| ≤ C*frobeniusNorm (A-B)+(1/(n:ℝ))*∑ i, |v i-w i| := by
  have hpoint (i : Fin n) : |smoothLoss (measurementQ x A i-v i)-
      smoothLoss (measurementQ x B i-w i)| ≤ |measurementQ x (A-B) i|+|(v-w) i| := by
    apply (UCRationalLoss.smoothLoss_abs_sub _ _).trans
    have he : measurementQ x A i-v i-(measurementQ x B i-w i) =
        measurementQ x (A-B) i-(v-w) i := by rw [measurementQ_sub]; change _ = _-(v i-w i); ring
    rw [he]
    exact abs_sub _ _
  have hsym : (A-B).transpose = A-B := by simp [hA,hB]
  have hQ := (empirical_mean_le_operator x (A-B) hsym).trans
    (mul_le_mul_of_nonneg_right hC (frobeniusNorm_nonneg _))
  calc
    _ = (1/(n:ℝ))*|∑ i, (smoothLoss (measurementQ x A i-v i)-
        smoothLoss (measurementQ x B i-w i))| := by
      rw [Finset.sum_sub_distrib, meanLoss, meanLoss, ← mul_sub, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(n:ℝ))]
    _ ≤ (1/(n:ℝ))*∑ i, |smoothLoss (measurementQ x A i-v i)-
        smoothLoss (measurementQ x B i-w i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1/(n:ℝ))*∑ i, (|measurementQ x (A-B) i|+|(v-w) i|) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpoint i) (by positivity)
    _ ≤ _ := by rw [Finset.sum_add_distrib, mul_add]; apply add_le_add hQ
                simp only [PiLp.sub_apply, le_refl]


#print axioms meanLoss_abs_sub_l1_le
end GaussianEllipsoid.UCContinuumTransfer
