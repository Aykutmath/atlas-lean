import UCFiniteMarginAssembly
import UCGaussianLossEvent

/-! The actual Gaussian uniform loss event implies the exact finite-candidate
free-energy expectation floor used by the proved quadratic replacement. -/
noncomputable section
open MeasureTheory ProbabilityTheory BMClippedL1Bridge
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.UCGaussianFreeEnergyFloor
open UCRationalLoss

/-- Integrating a nonnegative observable over its measurable good event. -/
theorem expectation_floor_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (hnn : ∀ x, 0 ≤ f x) (G : Set Ω) (hG : MeasurableSet G)
    (η p : ℝ) (hη : 0 ≤ η) (hp : μ.real Gᶜ ≤ p) (hfloor : ∀ x ∈ G, η ≤ f x) :
    η*(1-p) ≤ ∫ x, f x ∂μ := by
  have hpoint : ∀ x, G.indicator (fun _ => η) x ≤ f x := by
    intro x
    by_cases hx : x ∈ G
    · simpa only [Set.indicator_of_mem hx] using hfloor x hx
    · simpa only [Set.indicator_of_notMem hx] using hnn x
  have h := integral_mono ((integrable_const η).indicator hG) hf hpoint
  rw [integral_indicator_const η hG] at h
  simp only [smul_eq_mul] at h
  have hc := probReal_compl_eq_one_sub hG (μ := μ)
  rw [hc] at hp
  nlinarith

variable {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ] {d n : ℕ}

def gaussianValue (β : ℝ) (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n))
    (z : Fin n → (Fin (d*d) → ℝ)) : ℝ :=
  FiniteFreeEnergy.freeEnergy β n (FiniteFreeEnergy.totalLoss
    (fun i k => smoothLoss (UCNormalizedRows.gaussianRow (A k) (z i)-v k i)))

 theorem gaussianValue_eq_actual (β : ℝ) (hβ : 0 ≤ β)
    (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n)) (z : Fin n → (Fin (d*d) → ℝ)) :
    gaussianValue β A v z = UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ).toData
      (fun i => UCActualFreeEnergy.linearRow A (z i)+(fun k => 1-v k i)) := by
  symm
  simpa only [UCActualFreeEnergy.linearRow, Pi.add_def, gaussianValue] using
    uniformData_freeEnergy β hβ (fun i k => UCNormalizedRows.gaussianRow (A k) (z i)) (fun i k => v k i)

 theorem gaussianValue_bounds (β : ℝ) (hβ : 0 < β) (hn : 0 < n)
    (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n)) (z : Fin n → (Fin (d*d) → ℝ)) :
    0 ≤ gaussianValue β A v z ∧ gaussianValue β A v z ≤ 1 :=
  FiniteFreeEnergy.freeEnergy_of_bounded_rows_mem_unit_interval β n hβ hn _
    (fun i k => ⟨smoothLoss_nonneg _, (smoothLoss_lt_one _).le⟩)

 theorem gaussianValue_ge (β η : ℝ) (hβ : 0 < β) (hn : 0 < n)
    (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n)) (z : Fin n → (Fin (d*d) → ℝ))
    (hfloor : ∀ k, η ≤ (∑ i, smoothLoss (UCNormalizedRows.gaussianRow (A k) (z i)-v k i))/(n:ℝ)) :
    η ≤ gaussianValue β A v z := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hH : ∀ k, η*(n:ℝ) ≤ FiniteFreeEnergy.totalLoss
      (fun i k => smoothLoss (UCNormalizedRows.gaussianRow (A k) (z i)-v k i)) k :=
    fun k => (le_div_iff₀ hnR).mp (hfloor k)
  have h := FiniteFreeEnergy.freeEnergy_mono β n hβ hn hH
  rw [FiniteFreeEnergy.freeEnergy_const β n hβ hn (η*(n:ℝ))] at h
  simpa only [mul_div_cancel_right₀ η hnR.ne', gaussianValue] using h

/-- Exact 15η/16 finite free-energy floor from the genuine actual-row good
event. The event controls every PSD matrix and every nuisance vector, so the
candidate family may be any deterministic finite net. -/
theorem gaussian_freeEnergy_mean_floor (β η : ℝ) (hβ : 0 < β) (hη : 0 ≤ η)
    (hd : 0 < d) (hn : 0 < n)
    (A : κ → Square d) (v : κ → EuclideanSpace ℝ (Fin n))
    (G : Set (Fin n → (Fin (d*d) → ℝ))) (hG : MeasurableSet G)
    (hp : (Measure.pi (fun _ : Fin n => GaussianTensorMoments.gaussianProductLaw (Fin (d*d)))).real Gᶜ ≤ 1/16)
    (hfloor : ∀ z ∈ G, ∀ k, η ≤
      (∑ i, smoothLoss (UCNormalizedRows.gaussianRow (A k) (z i)-v k i))/(n:ℝ)) :
    15*η/16 ≤ ∫ z : Fin n → (Fin (d*d) → ℝ),
      UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ.le).toData
        (fun i => UCActualFreeEnergy.linearRow A (z i)+(fun k => 1-v k i))
        ∂Measure.pi (fun _ : Fin n => GaussianTensorMoments.gaussianProductLaw (Fin (d*d))) := by
  let μ := Measure.pi (fun _ : Fin n => GaussianTensorMoments.gaussianProductLaw (Fin (d*d)))
  have hm : Measurable (gaussianValue β A v) := by
    have he : gaussianValue β A v = fun z =>
        UCActualFreeEnergy.freeEnergy (uniformData (κ := κ) β hβ.le).toData
          (fun i => UCActualFreeEnergy.linearRow A (z i)+(fun k => 1-v k i)) :=
      funext (gaussianValue_eq_actual β hβ.le A v)
    rw [he]
    exact UCFreeEnergyConcentration.measurable_freeEnergy _ _
      (UCActualFreeEnergy.linearRow_continuous A hd).measurable _
  have hi : Integrable (gaussianValue β A v) μ :=
    UCProductConcentration.integrable_of_abs_bound hm (fun z => by
      have h := gaussianValue_bounds β hβ hn A v z
      rw [abs_of_nonneg h.1]
      exact h.2)
  have h := expectation_floor_of_good_event μ _ hi
    (fun z => (gaussianValue_bounds β hβ hn A v z).1) G hG η (1/16) hη hp
    (fun z hz => gaussianValue_ge β η hβ hn A v z (hfloor z hz))
  have he : η*(1-(1/16:ℝ))=15*η/16 := by ring
  rw [he] at h
  simpa only [gaussianValue_eq_actual β hβ.le A v] using h

#print axioms gaussian_freeEnergy_mean_floor
end GaussianEllipsoid.UCGaussianFreeEnergyFloor
