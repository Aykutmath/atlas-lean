import PaperDimensionality
import CanonicalSymGaussian

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open BMGeometry BMSaddle UCEscape GaussianEllipsoid.UCContinuityGeometry
open GaussianEllipsoid.PaperIsonormal
open scoped BigOperators InnerProductSpace
universe u
namespace GaussianEllipsoid.PaperIsonormalDimensionality
local instance {d : ℕ} : NormedAddCommGroup (SymFrob d) := Submodule.normedAddCommGroup (symmetricFrobenius d)
local instance {d : ℕ} : NormedSpace ℝ (SymFrob d) := Submodule.normedSpace (symmetricFrobenius d)
local instance {d : ℕ} : SeminormedAddCommGroup (SymFrob d) :=
  (inferInstance : NormedAddCommGroup (SymFrob d)).toSeminormedAddCommGroup
local instance {d : ℕ} : InnerProductSpace ℝ (SymFrob d) := Submodule.innerProductSpace (symmetricFrobenius d)

/-- Literal Frobenius pairing with the source matrix. -/
def rowPairing {d : ℕ} (G : SymFrob d) (A : Square d) : ℝ :=
  ∑ i, ∑ j, matrix G i j * A i j

def rowValues {d n : ℕ} (G : Fin n → SymFrob d) (A : Square d) : Euclid n :=
  WithLp.toLp 2 (fun i => rowPairing (G i) A)

lemma rowValues_continuous {d n : ℕ} (A : Square d) :
    Continuous (fun G : Fin n → SymFrob d => rowValues G A) := by
  unfold rowValues
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  unfold rowPairing matrix frobeniusToMatrix
  fun_prop

lemma retainedCoordinates_continuous {n : ℕ} (J : Finset (Fin n)) :
    Continuous (retainedCoordinates J) := by
  classical
  unfold retainedCoordinates
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases hi : i ∈ J
  · simpa only [hi,ite_true] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
  · simpa only [hi,ite_false] using (continuous_const : Continuous (fun _ : Euclid n => (0:ℝ)))

/-- The actual simultaneous good set in the space of symmetric Gaussian rows.
It is independent of the choice of a coordinate realization. -/
def retainedSymmetricGood (d n : ℕ) (θ γ : ℝ) (L : Submodule ℝ (Euclid n)) :
    Set (Fin n → SymFrob d) :=
  {G | ∀ A : Square d, A.PosSemidef → frobeniusNorm A=1 →
    ∀ v : Euclid n, v ∈ L → ∀ J : Finset (Fin n), J.card=n-Nat.floor (θ*n) →
      γ*d ≤ ‖retainedCoordinates J (rowValues G A-v)‖}

/-- Arbitrary intersections of closed norm inequalities prove Borel
measurability of the literal uniform event. No noninjective-image transport is used. -/
theorem retainedSymmetricGood_isClosed (d n : ℕ) (θ γ : ℝ) (L : Submodule ℝ (Euclid n)) :
    IsClosed (retainedSymmetricGood d n θ γ L) := by
  classical
  simp only [retainedSymmetricGood,Set.setOf_forall]
  apply isClosed_iInter
  intro A
  apply isClosed_iInter
  intro hA
  apply isClosed_iInter
  intro hF
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  apply isClosed_iInter
  intro J
  apply isClosed_iInter
  intro hJ
  exact isClosed_le continuous_const
    (((retainedCoordinates_continuous J).comp ((rowValues_continuous A).sub continuous_const)).norm)

/-- Exact matrix/inner-product representation for every PSD Frobenius-unit test. -/
lemma rowPairing_eq_inner {d : ℕ} (Y : SymFrob d) (A : Square d)
    (hA : A.PosSemidef) (hF : frobeniusNorm A=1) :
    rowPairing Y A = ⟪(⟨sourceFrobenius A,(sourceFrobenius_mem_psdUnit A hA hF).1.1⟩ : SymFrob d),Y⟫_ℝ := by
  change (∑ i, ∑ j, Y.val j i * A i j) = ∑ j, ∑ i, Y.val j i * A i j
  exact Finset.sum_comm

lemma canonical_rowValues {d n : ℕ} (z : Raw n d) (A : Square d)
    (hA : A.PosSemidef) (hF : frobeniusNorm A=1) :
    rowValues (fun i => symmetrizedFullEntry d (z i)) A =
      WithLp.toLp 2 (fun i => UCNormalizedRows.gaussianRow A (z i)) := by
  ext i
  change rowPairing (symmetrizedFullEntry d (z i)) A = UCNormalizedRows.gaussianRow A (z i)
  rw [rowPairing_eq_inner _ A hA hF,symmetrizedFullEntry_inner]
  rfl

/-- The complete raw row array pushes forward to the product symmetric Gaussian law. -/
lemma canonical_rows_preserving (d n : ℕ) :
    MeasurePreserving (fun z : Raw n d => fun i => symmetrizedFullEntry d (z i))
      (rawSourceLaw n d) (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))) :=
  measurePreserving_pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))
    (fun _ : Fin n => stdGaussian (SymFrob d)) (fun _ => symmetrizedFullEntry_preserving d)

/-- Arbitrary-law retained dimensionality with the same theta, dimension
cutoff, gamma(epsilon), retained cardinality, and probability as the checked
canonical theorem. All probability spaces and row laws are quantified after
theta and the cutoff, so those constants are uniform over realizations. -/
theorem paper_dimensionality_isonormal {ε C₁ : ℝ} (hε : 0<ε) (hC : 0<C₁) :
    ∃ θ : ℝ, 0<θ ∧ θ<1/2 ∧ θ*C₁≤ε/2 ∧
      C₁*(-θ*Real.log θ-(1-θ)*Real.log (1-θ)) ≤ (paperRetainedGamma ε)^2/8 ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀≤d → (n:ℝ)≤C₁*(d:ℝ)^2 →
      ∀ L : Submodule ℝ (Euclid n),
        (1/4+ε)*(d:ℝ)^2 ≤ (n:ℝ)-(Module.finrank ℝ L:ℝ) →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ (G : Fin n → Ω → SymFrob d), (∀ i, Measurable (G i)) →
          iIndepFun G μ → (∀ i, IsIsonormalSymLaw d (μ.map (G i))) →
        ∃ E : Set Ω, MeasurableSet E ∧
          μ.real Eᶜ ≤ Real.exp (-(paperRetainedGamma ε)^2*(d:ℝ)^2/4) ∧
          ∀ ω ∈ E, ∀ A : Square d, A.PosSemidef → frobeniusNorm A=1 →
            ∀ v : Euclid n, v ∈ L →
              ∀ J : Finset (Fin n), J.card=n-Nat.floor (θ*n) →
                paperRetainedGamma ε*d ≤ ‖retainedCoordinates J
                  (rowValues (fun i => G i ω) A-v)‖ := by
  obtain ⟨θ,hθ,hθhalf,hθC,hent,d₀,h⟩ := paper_dimensionality_corrected hε hC
  refine ⟨θ,hθ,hθhalf,hθC,hent,d₀,?_⟩
  intro d n hd hn L hdim Ω _ μ _ G hG hind hiso
  let S := retainedSymmetricGood d n θ (paperRetainedGamma ε) L
  have hS : MeasurableSet S := (retainedSymmetricGood_isClosed d n θ (paperRetainedGamma ε) L).measurableSet
  obtain ⟨K,hK,hKbad,hKgood⟩ := h d n hd hn L hdim
  have hsub : (fun z : Raw n d => fun i => symmetrizedFullEntry d (z i)) ⁻¹' Sᶜ ⊆ Kᶜ := by
    intro z hz hzin
    apply hz
    intro A hA hF v hv J hJ
    change paperRetainedGamma ε*d ≤ ‖retainedCoordinates J
      (rowValues (fun i => symmetrizedFullEntry d (z i)) A-v)‖
    rw [canonical_rowValues z A hA hF]
    exact hKgood z hzin A hA hF v hv J hJ
  have hcanonical : (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))).real Sᶜ ≤
      Real.exp (-(paperRetainedGamma ε)^2*(d:ℝ)^2/4) := by
    rw [← (canonical_rows_preserving d n).measureReal_preimage hS.compl.nullMeasurableSet]
    exact (measureReal_mono hsub).trans hKbad
  have hp : MeasurePreserving (fun ω => fun i => G i ω) μ
      (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob d))) :=
    ⟨measurable_pi_iff.mpr hG,iid_isonormal_symmetric_rows_law μ d n G hG hind hiso⟩
  refine ⟨(fun ω => fun i => G i ω) ⁻¹' S,hp.measurable hS,?_,?_⟩
  · rw [← Set.preimage_compl,hp.measureReal_preimage hS.compl.nullMeasurableSet]
    exact hcanonical
  · intro ω hω
    exact hω

#print axioms retainedSymmetricGood_isClosed
#print axioms paper_dimensionality_isonormal
end GaussianEllipsoid.PaperIsonormalDimensionality
