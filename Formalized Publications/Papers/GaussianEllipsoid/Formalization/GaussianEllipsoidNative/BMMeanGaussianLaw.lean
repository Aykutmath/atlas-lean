import GaussianCoisometry
import GaussianQuadraticSpectral

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace BMSpectralBridge

variable {ι : Type*} [Fintype ι]

def normalizedAverage (n : ℕ) (x : (Fin n × ι) → ℝ) : ι → ℝ :=
  fun j => (Real.sqrt n)⁻¹ * ∑ i : Fin n, x (i,j)

def averageLinear (n : ℕ) :
    EuclideanSpace ℝ (Fin n × ι) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := (WithLp.equiv 2 _).symm (normalizedAverage n x)
  map_add' x y := by
    ext j
    simp [normalizedAverage, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext j
    simp [normalizedAverage, Finset.mul_sum, mul_left_comm]

def averageCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n × ι) →L[ℝ] EuclideanSpace ℝ ι :=
  (averageLinear n).toContinuousLinearMap

def repeatLinear (n : ℕ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin n × ι) where
  toFun y := (WithLp.equiv 2 _).symm (fun p => (Real.sqrt n)⁻¹ * y p.2)
  map_add' x y := by ext p; simp [mul_add]
  map_smul' c x := by ext p; simp [mul_left_comm]

def repeatCLM (n : ℕ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin n × ι) :=
  (repeatLinear n).toContinuousLinearMap

@[simp] theorem averageCLM_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n × ι)) (j : ι) :
    averageCLM n x j = (Real.sqrt n)⁻¹ * ∑ i : Fin n, x (i,j) := rfl

@[simp] theorem repeatCLM_apply (n : ℕ) (x : EuclideanSpace ℝ ι) (p : Fin n × ι) :
    repeatCLM n x p = (Real.sqrt n)⁻¹ * x p.2 := rfl

theorem repeatCLM_eq_adjoint (n : ℕ) :
    repeatCLM (ι := ι) n = ContinuousLinearMap.adjoint (averageCLM n) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.star_apply, star_trivial, repeatCLM_apply, averageCLM_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i : Fin n, y (i,j) * ((Real.sqrt n)⁻¹ * x j)) =
    ((Real.sqrt n)⁻¹ * ∑ i : Fin n, y (i,j)) * x j
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem averageCLM_coisometry {n : ℕ} (hn : 0 < n) :
    averageCLM (ι := ι) n ∘L ContinuousLinearMap.adjoint (averageCLM n) =
      ContinuousLinearMap.id ℝ _ := by
  rw [← repeatCLM_eq_adjoint]
  ext y j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    averageCLM_apply, repeatCLM_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hs : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  field_simp
  rw [hs]

/-- Full joint law of the normalized entrywise average, not just marginal Gaussianity. -/
theorem normalizedAverage_preserving {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (normalizedAverage (ι := ι) n)
      (gaussianProductLaw (Fin n × ι)) (gaussianProductLaw ι) := by
  have hQ : MeasurePreserving (averageCLM (ι := ι) n)
      (euclideanGaussianLaw (Fin n × ι)) (euclideanGaussianLaw ι) :=
    ⟨(averageCLM n).continuous.measurable,
      GaussianEllipsoid.SmallBall.euclideanGaussianLaw_map_coisometry _ (averageCLM_coisometry hn)⟩
  have he : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × ι) → ℝ))
      (gaussianProductLaw (Fin n × ι)) (euclideanGaussianLaw (Fin n × ι)) :=
    ⟨(MeasurableEquiv.toLp 2 ((Fin n × ι) → ℝ)).measurable, rfl⟩
  exact BMQuadraticSpectral.coordinates_preserving.comp (hQ.comp he)

end BMSpectralBridge
