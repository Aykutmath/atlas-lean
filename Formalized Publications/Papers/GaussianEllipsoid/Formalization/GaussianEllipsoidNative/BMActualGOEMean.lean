import BMMeanGaussianLaw
import BMSpectralBox
import BMBadEventTail
import BMGaussianEquivalent
import GaussianSelectedColumns

noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid BMGeometry
open scoped BigOperators InnerProductSpace
namespace BMSpectralBridge

/-- The actual BM GOE, as a real continuous Euclidean operator. -/
def goeOp (d : ℕ) : ((Fin d × Fin d) → ℝ) →ₗ[ℝ] Op d where
  toFun x := Real.sqrt (2/(d:ℝ)) • isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)
  map_add' x y := by
    simp only [isotropicSymmetricOp_eq_symmetrize, map_add, smul_add]
    abel
  map_smul' c x := by
    simp only [isotropicSymmetricOp_eq_symmetrize, map_smul, smul_add, smul_smul, RingHom.id_apply]
    module

theorem goeOp_continuous (d : ℕ) : Continuous (goeOp d) :=
  (goeOp d).continuous_of_finiteDimensional

/-- Equality with the literal full-entry BM adapter, including its normalization. -/
theorem goeOp_eq_adapter (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    opMatrix (goeOp d x) = BMGaussianEquivalent.symmetrizedGaussianMatrix d
      (fun k => x (finProdFinEquiv.symm k)) := by
  ext i j
  simp only [goeOp, LinearMap.coe_mk, AddHom.coe_mk, opMatrix_smul,
    opMatrix, operatorFrobenius_smul, isotropicSymmetricOp_frobenius, frobeniusToMatrix,
    symmetricFrob_apply, Matrix.smul_apply, smul_eq_mul,
    BMGaussianEquivalent.symmetrizedGaussianMatrix, Equiv.symm_apply_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, symmetricFrob_apply]
  change Real.sqrt (2/(d:ℝ)) * ((x (i,j)+x (j,i))/2) = _
  ring

/-- Exact GOE law as the pushforward of independent standard entries. -/
def goeLaw (d : ℕ) : Measure (Op d) := (gaussianProductLaw (Fin d × Fin d)).map (goeOp d)

instance goeLaw_probability (d : ℕ) : IsProbabilityMeasure (goeLaw d) :=
  MeasureTheory.Measure.isProbabilityMeasure_map (goeOp_continuous d).measurable.aemeasurable

def meanOp {d : ℕ} (n : ℕ) (G : Fin n → Op d) : Op d := (Real.sqrt n)⁻¹ • ∑ i, G i

theorem meanOp_continuous (n d : ℕ) : Continuous (meanOp (d := d) n) := by
  unfold meanOp
  fun_prop

/-- The flattened Gaussian entries generate the full independent GOE-row law. -/
theorem goeRows_preserving (n d : ℕ) :
    MeasurePreserving (fun x : (Fin n × (Fin d × Fin d)) → ℝ =>
      fun i => goeOp d (fun p => x (i,p)))
      (gaussianProductLaw (Fin n × (Fin d × Fin d)))
      (Measure.pi (fun _ : Fin n => goeLaw d)) := by
  have hc : MeasurePreserving
      (fun x : (Fin n × (Fin d × Fin d)) → ℝ => fun i p => x (i,p))
      (gaussianProductLaw (Fin n × (Fin d × Fin d)))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d × Fin d))) :=
    ⟨by fun_prop, gaussianProductLaw_map_curry⟩
  exact (measurePreserving_pi _ _ (fun _ =>
    show MeasurePreserving (goeOp d) (gaussianProductLaw (Fin d × Fin d)) (goeLaw d) from
      ⟨(goeOp_continuous d).measurable, rfl⟩)).comp hc

theorem goeOp_normalizedAverage (n d : ℕ)
    (x : (Fin n × (Fin d × Fin d)) → ℝ) :
    goeOp d (normalizedAverage n x) = meanOp n (fun i => goeOp d (fun p => x (i,p))) := by
  have he : normalizedAverage n x = (Real.sqrt n)⁻¹ • ∑ i : Fin n, (fun p => x (i,p)) := by
    ext p
    simp [normalizedAverage]
  rw [he, map_smul, map_sum]
  rfl

/-- Exact equality of full operator-valued laws under genuinely independent GOE rows. -/
theorem meanGOE_map {n d : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => goeLaw d)).map (meanOp n) = goeLaw d := by
  rw [← (goeRows_preserving n d).map_eq,
    Measure.map_map (meanOp_continuous n d).measurable (goeRows_preserving n d).measurable]
  have he : meanOp n ∘ (fun x : (Fin n × (Fin d × Fin d)) → ℝ =>
      fun i => goeOp d (fun p => x (i,p))) = goeOp d ∘ normalizedAverage n := by
    funext x
    exact (goeOp_normalizedAverage n d x).symm
  rw [he, ← Measure.map_map (goeOp_continuous d).measurable
    (normalizedAverage_preserving hn).measurable, (normalizedAverage_preserving hn).map_eq]
  rfl

/-- Elementary genuine operator bound, with no asymptotic spectral theorem premise. -/
theorem goeOp_thirtytwo_tail {d : ℕ} (hd : 0 < d) :
    (gaussianProductLaw (Fin d × Fin d)).real {x | 32 < ‖goeOp d x‖} ≤
      2*Real.exp (-2*(d:ℝ)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : Real.sqrt (2/(d:ℝ)) * Real.sqrt d = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hd'.ne']
  have hs2 : Real.sqrt 2 ≤ (2:ℝ) := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  apply (measureReal_mono (show {x | 32 < ‖goeOp d x‖} ⊆
    {x | 12*Real.sqrt d < ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖} from ?_)).trans
    (isotropicSymmetricOp_twelve_tail d)
  intro x hx
  by_contra hb
  have hb' : ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖ ≤ 12*Real.sqrt d := le_of_not_gt hb
  have hh : ‖goeOp d x‖ ≤ 32 := by
    change ‖Real.sqrt (2/(d:ℝ)) • isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖ ≤ 32
    rw [norm_smul (Real.sqrt (2/(d:ℝ))) (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)), Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (2/(d:ℝ)) * (12*Real.sqrt d) := mul_le_mul_of_nonneg_left hb' (Real.sqrt_nonneg _)
      _ = 12*Real.sqrt 2 := by rw [← mul_assoc, mul_comm _ (12:ℝ), mul_assoc, hs]
      _ ≤ 32 := by linarith
  exact not_lt_of_ge hh hx

/-- The same nonasymptotic bound for the normalized sum of independent actual GOE rows. -/
theorem meanGOE_thirtytwo_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => goeLaw d)).real {G | 32 < ‖meanOp n G‖} ≤
      2*Real.exp (-2*(d:ℝ)) := by
  have hm : MeasurePreserving (meanOp n)
      (Measure.pi (fun _ : Fin n => goeLaw d)) (goeLaw d) :=
    ⟨(meanOp_continuous n d).measurable, meanGOE_map hn⟩
  have hg : MeasurePreserving (goeOp d) (gaussianProductLaw (Fin d × Fin d)) (goeLaw d) :=
    ⟨(goeOp_continuous d).measurable, rfl⟩
  have hs : MeasurableSet {T : Op d | 32 < ‖T‖} := isOpen_lt continuous_const continuous_norm |>.measurableSet
  rw [show {G | 32 < ‖meanOp n G‖} = meanOp n ⁻¹' {T : Op d | 32 < ‖T‖} from rfl,
    hm.measureReal_preimage hs.nullMeasurableSet,
    ← hg.measureReal_preimage hs.nullMeasurableSet]
  exact goeOp_thirtytwo_tail hd

end BMSpectralBridge

namespace BMSpectralBridge

/-- Literal Fin(d*d)-indexed adapter, realized as an actual continuous Euclidean operator. -/
def actualGOEOp (d : ℕ) (z : Fin (d*d) → ℝ) : Op d :=
  goeOp d (fun p => z (finProdFinEquiv p))

theorem actualGOEOp_matrix (d : ℕ) (z : Fin (d*d) → ℝ) :
    opMatrix (actualGOEOp d z) = BMGaussianEquivalent.symmetrizedGaussianMatrix d z := by
  rw [actualGOEOp, goeOp_eq_adapter]
  simp only [Equiv.apply_symm_apply]

/-- Exact coordinate transport from the actual adapter source, not an assumed Gaussian law. -/
theorem actualGOEOp_preserving (d : ℕ) :
    MeasurePreserving (actualGOEOp d) (gaussianProductLaw (Fin (d*d))) (goeLaw d) := by
  have he : MeasurePreserving
      (fun z : Fin (d*d) → ℝ => fun p : Fin d × Fin d => z (finProdFinEquiv p))
      (gaussianProductLaw (Fin (d*d))) (gaussianProductLaw (Fin d × Fin d)) :=
    by
      convert! measurePreserving_piCongrLeft
        (fun _ : Fin d × Fin d => gaussianReal 0 1) finProdFinEquiv.symm using 1
      ext z p
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  exact (show MeasurePreserving (goeOp d) (gaussianProductLaw (Fin d × Fin d)) (goeLaw d) from
    ⟨(goeOp_continuous d).measurable, rfl⟩).comp he

/-- Simultaneous transport of every independent literal adapter row. -/
theorem actualGOERows_preserving (n d : ℕ) :
    MeasurePreserving (fun z : Fin n → Fin (d*d) → ℝ => fun i => actualGOEOp d (z i))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d))))
      (Measure.pi (fun _ : Fin n => goeLaw d)) :=
  measurePreserving_pi _ _ (fun _ => actualGOEOp_preserving d)

/-- The normalized sum of literal BM-adapter rows has the exact GOE operator law. -/
theorem actualMeanGOE_map {n d : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).map
      (fun z => meanOp n (fun i => actualGOEOp d (z i))) = goeLaw d := by
  rw [← meanGOE_map (d := d) hn, ← (actualGOERows_preserving n d).map_eq,
    Measure.map_map (meanOp_continuous n d).measurable (actualGOERows_preserving n d).measurable]
  rfl

/-- The literal independent-entry GOE source satisfies the same explicit operator event. -/
theorem actualMeanGOE_thirtytwo_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).real
      {z | 32 < ‖meanOp n (fun i => actualGOEOp d (z i))‖} ≤
      2*Real.exp (-2*(d:ℝ)) := by
  have hs : MeasurableSet {G : Fin n → Op d | 32 < ‖meanOp n G‖} :=
    (isOpen_lt continuous_const (meanOp_continuous n d).norm).measurableSet
  rw [show {z | 32 < ‖meanOp n (fun i => actualGOEOp d (z i))‖} =
      (fun z : Fin n → Fin (d*d) → ℝ => fun i => actualGOEOp d (z i)) ⁻¹'
        {G | 32 < ‖meanOp n G‖} from rfl,
    (actualGOERows_preserving n d).measureReal_preimage hs.nullMeasurableSet]
  exact meanGOE_thirtytwo_tail hn hd

end BMSpectralBridge

namespace BMSpectralBridge

theorem opMatrix_continuous (d : ℕ) : Continuous (opMatrix : Op d → Matrix (Fin d) (Fin d) ℝ) := by
  change Continuous (fun T : Op d => fun i j => T (EuclideanSpace.basisFun (Fin d) ℝ j) i)
  fun_prop

theorem opMatrix_meanOp {n d : ℕ} (G : Fin n → Op d) :
    opMatrix (meanOp n G) = (Real.sqrt n)⁻¹ • ∑ i, opMatrix (G i) := by
  ext i j
  change (((Real.sqrt n)⁻¹ • ∑ k, G k) (EuclideanSpace.basisFun (Fin d) ℝ j)) i = _
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, PiLp.smul_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) i)
    (fun k => G k (EuclideanSpace.basisFun (Fin d) ℝ j)) Finset.univ

local instance (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

local instance (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

/-- Full matrix-valued law of the literal normalized sum, not merely its trace marginals. -/
theorem actualMeanGOEMatrix_map {n d : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))).map
      (fun z => (Real.sqrt n)⁻¹ • ∑ i, BMGaussianEquivalent.symmetrizedGaussianMatrix d (z i)) =
    (gaussianProductLaw (Fin (d*d))).map (BMGaussianEquivalent.symmetrizedGaussianMatrix d) := by
  have he : (fun z : Fin n → Fin (d*d) → ℝ =>
      (Real.sqrt n)⁻¹ • ∑ i, BMGaussianEquivalent.symmetrizedGaussianMatrix d (z i)) =
      opMatrix ∘ (fun z => meanOp n (fun i => actualGOEOp d (z i))) := by
    funext z
    simp only [Function.comp_apply, opMatrix_meanOp, actualGOEOp_matrix]
  have hm : Measurable (fun z : Fin n → Fin (d*d) → ℝ => meanOp n (fun i => actualGOEOp d (z i))) :=
    (meanOp_continuous n d).measurable.comp (actualGOERows_preserving n d).measurable
  rw [he, ← Measure.map_map (opMatrix_continuous d).measurable hm, actualMeanGOE_map hn,
    ← (actualGOEOp_preserving d).map_eq,
    Measure.map_map (opMatrix_continuous d).measurable (actualGOEOp_preserving d).measurable]
  congr 1
  funext z
  exact actualGOEOp_matrix d z

end BMSpectralBridge
