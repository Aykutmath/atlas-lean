import MeasurableHalfPolar

open MeasureTheory Module
open scoped InnerProductSpace

namespace GaussianEllipsoid

/-- An explicitly supported measurable half-polar witness. -/
noncomputable def supportedMeasurableHalfPolar {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r)
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q) :
    Euclid q →L[ℝ] Euclid r :=
  D ∘L measurableHalfPolar r q (operatorFrobenius T) ∘L E

/-- Joint Borel dependence on the measured block and its two support projections. -/
theorem measurable_supportedMeasurableHalfPolar (r q : ℕ) :
    Measurable (fun p : (Euclid q →L[ℝ] Euclid r) ×
        (Euclid r →L[ℝ] Euclid r) × (Euclid q →L[ℝ] Euclid q) =>
      supportedMeasurableHalfPolar p.1 p.2.1 p.2.2) := by
  have hW : Measurable (fun p : (Euclid q →L[ℝ] Euclid r) ×
        (Euclid r →L[ℝ] Euclid r) × (Euclid q →L[ℝ] Euclid q) =>
      measurableHalfPolar r q (operatorFrobenius p.1)) :=
    (measurable_measurableHalfPolar r q).comp
      ((continuous_operatorFrobenius r q).measurable.comp measurable_fst)
  have hcR : Measurable (fun p : (Euclid q →L[ℝ] Euclid r) × (Euclid q →L[ℝ] Euclid q) =>
      p.1 ∘L p.2) := (continuous_fst.clm_comp continuous_snd).measurable
  have hcL : Measurable (fun p : (Euclid r →L[ℝ] Euclid r) × (Euclid q →L[ℝ] Euclid r) =>
      p.1 ∘L p.2) := (continuous_fst.clm_comp continuous_snd).measurable
  exact hcL.comp ((measurable_fst.comp measurable_snd).prodMk
    (hcR.comp (hW.prodMk (measurable_snd.comp measurable_snd))))

/-- The supported measurable witness is contractive, has the exact support,
attains at least half the nuclear norm, and has Frobenius energy bounded by
the support rank. Arbitrary measurable spectral basis selection is unnecessary. -/
theorem supportedMeasurableHalfPolar_properties {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r)
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (hDself : ContinuousLinearMap.adjoint D = D) (hEself : ContinuousLinearMap.adjoint E = E)
    (hDsq : D ∘L D = D) (hEsq : E ∘L E = E) (hT : D ∘L T ∘L E = T) :
    let W := supportedMeasurableHalfPolar T D E
    ‖W‖ ≤ 1 ∧ D ∘L W ∘L E = W ∧
      spectralNuclearNorm (operatorFrobenius T) / 2 ≤
        ⟪operatorFrobenius T, operatorFrobenius W⟫_ℝ ∧
      ‖operatorFrobenius W‖^2 ≤ (finrank ℝ (LinearMap.range E.toLinearMap) : ℝ) := by
  let W₀ := measurableHalfPolar r q (operatorFrobenius T)
  let W := supportedMeasurableHalfPolar T D E
  have hDn := norm_projection_le_one D hDself hDsq
  have hEn := norm_projection_le_one E hEself hEsq
  have hW : ‖W‖ ≤ 1 := norm_comp_le_one D _ hDn
    (norm_comp_le_one W₀ E (norm_measurableHalfPolar_le _) hEn)
  have hRight : W ∘L E = W := by
    dsimp [W, supportedMeasurableHalfPolar]
    simp only [ContinuousLinearMap.comp_assoc, hEsq]
  have hLeft : D ∘L W = W := by
    dsimp [W, supportedMeasurableHalfPolar]
    rw [← ContinuousLinearMap.comp_assoc, hDsq]
  have hSupport : D ∘L W ∘L E = W := by rw [← ContinuousLinearMap.comp_assoc, hLeft, hRight]
  refine ⟨hW, hSupport, ?_, frobenius_supported_contraction_sq_le_rank W E hW hEself hEsq hRight⟩
  have hp₀ := inner_operator_comp_left D (T ∘L E) W₀
  rw [hDself] at hp₀
  have hp₁ := inner_operator_comp_right T E (D ∘L W₀)
  rw [hEself] at hp₁
  have hp := hp₀.trans hp₁
  rw [hT] at hp
  have hTarget : (D ∘L W₀) ∘L E = W := by
    dsimp [W, W₀, supportedMeasurableHalfPolar]
    rw [ContinuousLinearMap.comp_assoc]
  rw [hTarget] at hp
  rw [← hp]
  exact half_nuclear_le_pairing (operatorFrobenius T)

/-- Measurable input data give a measurable supported witness on any sample space. -/
theorem measurable_supported_witness_comp {Ω : Type*} [MeasurableSpace Ω] {r q : ℕ}
    (T : Ω → (Euclid q →L[ℝ] Euclid r))
    (D : Ω → (Euclid r →L[ℝ] Euclid r)) (E : Ω → (Euclid q →L[ℝ] Euclid q))
    (hT : Measurable T) (hD : Measurable D) (hE : Measurable E) :
    Measurable (fun ω => supportedMeasurableHalfPolar (T ω) (D ω) (E ω)) :=
  (measurable_supportedMeasurableHalfPolar r q).comp (hT.prodMk (hD.prodMk hE))

#print axioms measurable_supportedMeasurableHalfPolar
#print axioms supportedMeasurableHalfPolar_properties
#print axioms measurable_supported_witness_comp

end GaussianEllipsoid
