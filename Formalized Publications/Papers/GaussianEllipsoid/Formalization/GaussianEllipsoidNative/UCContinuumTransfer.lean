import UCRationalLoss
import UCUniformContinuity

/-! Actual rational-loss Lipschitz transfer from finite candidates to the
continuum, using the proved Frobenius empirical operator. -/
noncomputable section
open MeasureTheory BMClippedL1Bridge
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators
namespace GaussianEllipsoid.UCContinuumTransfer

/-- Empirical bounded rational loss against a deterministic nuisance vector. -/
def meanLoss {d n : ℕ} (x : Sample d n) (A : Square d)
    (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1/(n:ℝ))*∑ i, smoothLoss (measurementQ x A i-v i)

 theorem meanLoss_le_abs {d n : ℕ} (x : Sample d n) (A : Square d)
    (v : EuclideanSpace ℝ (Fin n)) :
    meanLoss x A v ≤ (1/(n:ℝ))*∑ i, |measurementQ x A i-v i| :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => UCRationalLoss.smoothLoss_le_abs _)
    (by positivity)

 theorem measurementQ_sub {d n : ℕ} (x : Sample d n) (A B : Square d) (i : Fin n) :
    measurementQ x (A-B) i = measurementQ x A i-measurementQ x B i := by
  simp only [measurementQ, quadratic_sub, Matrix.trace_sub]
  ring

/-- Each Euclidean coordinate is bounded by the full norm, so even an
absolute Euclidean nuisance mesh gives an averaged-l1 mesh of the same size. -/
theorem mean_abs_coords_le {n : ℕ} (hn : 0 < n) (v : EuclideanSpace ℝ (Fin n)) :
    (1/(n:ℝ))*∑ i, |v i| ≤ ‖v‖ := by
  have hi (i : Fin n) : |v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    _ ≤ (1/(n:ℝ))*∑ _i : Fin n, ‖v‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by positivity)
    _ = _ := by simp [hn0]

/-- Exact deterministic Lipschitz estimate on the genuine continuity event. -/
theorem meanLoss_abs_sub_le {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A B : Square d) (hA : A.transpose = A) (hB : B.transpose = B)
    (v w : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : ‖empiricalOperator x‖ ≤ C) :
    |meanLoss x A v-meanLoss x B w| ≤ C*frobeniusNorm (A-B)+‖v-w‖ := by
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
  have hV := mean_abs_coords_le hn (v-w)
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
    _ ≤ _ := by rw [Finset.sum_add_distrib, mul_add]; exact add_le_add hQ hV

/-- Any actual matrix/nuisance cover transfers a finite loss margin. -/
theorem meanLoss_lower_of_approx {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A B : Square d) (hA : A.transpose = A) (hB : B.transpose = B)
    (v w : EuclideanSpace ℝ (Fin n)) (C r s m : ℝ)
    (hC : ‖empiricalOperator x‖ ≤ C) (hr : frobeniusNorm (A-B) ≤ r)
    (hs : ‖v-w‖ ≤ s) (hmargin : m ≤ meanLoss x B w) :
    m-(C*r+s) ≤ meanLoss x A v := by
  have hCn : 0 ≤ C := (norm_nonneg (empiricalOperator x)).trans hC
  have h := (abs_le.mp (meanLoss_abs_sub_le hn x A B hA hB v w C hC)).1
  have herr := add_le_add (mul_le_mul_of_nonneg_left hr hCn) hs
  linarith

#print axioms meanLoss_abs_sub_le
#print axioms meanLoss_lower_of_approx
end GaussianEllipsoid.UCContinuumTransfer
