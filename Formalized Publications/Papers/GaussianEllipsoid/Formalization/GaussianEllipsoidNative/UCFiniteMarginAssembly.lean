import UCFreeEnergyConcentration
import UCContinuumTransfer

/-! Exact finite-candidate loss margin and continuum event inclusion. The
probability estimate is inherited from the proved actual quadratic comparison
and the proved bounded-differences theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory BMClippedL1Bridge
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.UCFiniteMarginAssembly
open UCRationalLoss UCContinuumTransfer UCContinuityGeometry UCUniformContinuity

variable {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ] {d n : ℕ}

def finiteValue (β : ℝ) (x : Sample d n) (A : κ → Square d)
    (v : κ → EuclideanSpace ℝ (Fin n)) : ℝ :=
  FiniteFreeEnergy.freeEnergy β n
    (FiniteFreeEnergy.totalLoss (fun i k => smoothLoss (measurementQ x (A k) i-v k i)))

/-- Exact uniform-prior realization under the shifted rational Gibbs data. -/
theorem finiteValue_eq_actual (β : ℝ) (hβ : 0 ≤ β) (x : Sample d n)
    (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n)) :
    finiteValue β x A v = UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ).toData
      (fun i => UCActualFreeEnergy.quadraticRow A (x i)+(fun k => 1-v k i)) := by
  symm
  simpa only [UCActualFreeEnergy.quadraticRow, Pi.add_def, measurementQ, finiteValue] using
    uniformData_freeEnergy β hβ (fun i k => measurementQ x (A k) i) (fun i k => v k i)

/-- Every candidate mean loss bounds the finite free energy from above up to
its exact entropy error. -/
theorem finiteValue_le_meanLoss_add (β err : ℝ) (hβ : 0 < β) (hn : 0 < n)
    (hEnt : Real.log (Fintype.card κ:ℝ) ≤ err*β*n)
    (x : Sample d n) (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n)) (k : κ) :
    finiteValue β x A v ≤ meanLoss x (A k) (v k)+err := by
  let H := FiniteFreeEnergy.totalLoss (fun i k => smoothLoss (measurementQ x (A k) i-v k i))
  have h := FiniteFreeEnergy.freeEnergy_min_error β n hβ hn H err hEnt
  have hmin := div_le_div_of_nonneg_right (FiniteFreeEnergy.candidateMin_le H k)
    (by positivity : (0:ℝ) ≤ n)
  apply h.trans
  have he : H k/(n:ℝ) = meanLoss x (A k) (v k) := by
    unfold H FiniteFreeEnergy.totalLoss meanLoss
    ring
  linarith

/-- Actual-law finite-net loss failure, keeping its exponential-in-n rate. -/
theorem finite_loss_margin_tail (β θ τ : ℝ) (hβ : 0 < β) (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (A : κ → Square d) (hAsym : ∀ k, (A k).transpose = A k) (hd : 0 < d)
    (hOp : ∀ k, matrixOpNorm (A k) ≤ τ) (hF : ∀ k, frobeniusNorm (A k) ≤ 1)
    (m : ℕ) (v : κ → EuclideanSpace ℝ (Fin (m+1)))
    (hEnt : Real.log (Fintype.card κ:ℝ) ≤ (θ/16)*β*(m+1:ℕ))
    (hsmall : normalizedComparisonConstant β hβ.le*τ ≤ θ/16)
    (hGaussian : 15*θ/16 ≤ ∫ z : Fin (m+1) → (Fin (d*d) → ℝ),
      UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ.le).toData
        (fun i => UCActualFreeEnergy.linearRow A (z i)+(fun k => 1-v k i))
        ∂Measure.pi (fun _ : Fin (m+1) => GaussianTensorMoments.gaussianProductLaw (Fin (d*d)))) :
    (gaussianSampleLaw d (m+1)).real {x | ∃ k, meanLoss x (A k) (v k) < 11*θ/16} ≤
      Real.exp (-((m+1:ℕ):ℝ)*θ^2/128) := by
  let D := uniformData (κ := κ) β hβ.le
  have htail := UCFreeEnergyConcentration.quadratic_freeEnergy_margin D
    (fun k => rfl) hβ (uniformData_loss_bounds β hβ.le) A hAsym hd τ hτ hOp hF m
    (fun i k => 1-v k i) θ hθ hsmall hGaussian
  have hsub : {x : Sample d (m+1) | ∃ k, meanLoss x (A k) (v k) < 11*θ/16} ⊆
      {x | UCActualFreeEnergy.freeEnergy D.toData
        (fun i => UCActualFreeEnergy.quadraticRow A (x i)+(fun k => 1-v k i)) < 3*θ/4} := by
    rintro x ⟨k,hk⟩
    have h := finiteValue_le_meanLoss_add β (θ/16) hβ (Nat.succ_pos m) hEnt x A v k
    rw [finiteValue_eq_actual β hβ.le] at h
    change UCActualFreeEnergy.freeEnergy D.toData _ < _
    linarith
  exact (measureReal_mono hsub).trans htail

/-- Deterministic event inclusion for a genuine joint finite cover; the two
exceptional events are already controlled exponentially by proved theorems. -/
theorem continuum_bad_subset {K : Set (Square d)} {V : Set (EuclideanSpace ℝ (Fin n))}
    (hn : 0 < n) (hKsym : ∀ A ∈ K, A.transpose = A)
    (A : κ → Square d) (hAsym : ∀ k, (A k).transpose = A k)
    (v : κ → EuclideanSpace ℝ (Fin n))
    (C r s θ : ℝ) (hθ : 0 < θ)
    (hCover : ∀ B ∈ K, ∀ w ∈ V, ∃ k, frobeniusNorm (B-A k) ≤ r ∧ ‖w-v k‖ ≤ s)
    (hmesh : C*r+s ≤ 3*θ/16) :
    {x : Sample d n | ∃ B ∈ K, ∃ w ∈ V, (1/(n:ℝ))*∑ i, |measurementQ x B i-w i| < θ/2} ⊆
      {x | C < ‖empiricalOperator x‖} ∪ {x | ∃ k, meanLoss x (A k) (v k) < 11*θ/16} := by
  rintro x ⟨B,hBK,w,hwV,hbad⟩
  by_cases hC : C < ‖empiricalOperator x‖
  · exact Or.inl hC
  by_cases hnet : ∃ k, meanLoss x (A k) (v k) < 11*θ/16
  · exact Or.inr hnet
  exfalso
  obtain ⟨k,hr,hs⟩ := hCover B hBK w hwV
  have hm : 11*θ/16 ≤ meanLoss x (A k) (v k) := le_of_not_gt (fun h => hnet ⟨k,h⟩)
  have ht := meanLoss_lower_of_approx hn x B (A k) (hKsym B hBK) (hAsym k) w (v k)
    C r s (11*θ/16) (le_of_not_gt hC) hr hs hm
  have hu := meanLoss_le_abs x B w
  linarith

#print axioms finite_loss_margin_tail
#print axioms continuum_bad_subset
end GaussianEllipsoid.UCFiniteMarginAssembly
