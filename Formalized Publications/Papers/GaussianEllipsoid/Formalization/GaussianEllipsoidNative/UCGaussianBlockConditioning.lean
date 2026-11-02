import UCProjectedNorm
import UCRetainedFrames
import BMGordonExpectations
import GaussianEllipsoid.GaussianProbability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
namespace UCEscape

/-- The literal source Gaussian coordinate law, realized as a Euclidean Gaussian. -/
theorem gaussianVector_toLp_preserving (d : ℕ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (GaussianEllipsoid.gaussianVectorLaw d) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  exact ⟨(MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable, map_pi_eq_stdGaussian⟩

/-- A full orthogonal change of coordinates followed by a head/tail block split. -/
def gaussianBlockSplit {d j p : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p)) :
    GaussianEllipsoid.Vector d ≃ᵐ
      (GaussianEllipsoid.Vector j × GaussianEllipsoid.Vector p) :=
  (((MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans e.toHomeomorph.toMeasurableEquiv).trans
    BMGordon.splitBlocks).trans
    ((MeasurableEquiv.toLp 2 (Fin j → ℝ)).symm.prodCongr
      (MeasurableEquiv.toLp 2 (Fin p → ℝ)).symm)

/-- Exact source Gaussian law becomes the independent head/tail product. -/
theorem gaussianBlockSplit_preserving {d j p : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p)) :
    MeasurePreserving (gaussianBlockSplit e) (GaussianEllipsoid.gaussianVectorLaw d)
      ((GaussianEllipsoid.gaussianVectorLaw j).prod (GaussianEllipsoid.gaussianVectorLaw p)) := by
  have he : MeasurePreserving e (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (stdGaussian (EuclideanSpace ℝ (Fin j ⊕ Fin p))) :=
    ⟨e.continuous.measurable, stdGaussian_map e⟩
  have hs : MeasurePreserving (BMGordon.splitBlocks (ι := Fin j) (η := Fin p))
      (stdGaussian (EuclideanSpace ℝ (Fin j ⊕ Fin p)))
      ((stdGaussian (EuclideanSpace ℝ (Fin j))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin p)))) := by
    simpa only [euclideanGaussianLaw_eq_stdGaussian] using
      (BMGordon.splitBlocks_preserving (ι := Fin j) (η := Fin p))
  exact (((gaussianVector_toLp_preserving j).symm (MeasurableEquiv.toLp 2 (Fin j → ℝ))).prod
    ((gaussianVector_toLp_preserving p).symm (MeasurableEquiv.toLp 2 (Fin p → ℝ)))).comp
    (hs.comp (he.comp (gaussianVector_toLp_preserving d)))

/-- Split every source sample row and collect all head rows and all tail rows. -/
def gaussianSampleBlockSplit {d j p : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p)) (n : ℕ) :
    GaussianEllipsoid.Sample d n ≃ᵐ
      (GaussianEllipsoid.Sample j n × GaussianEllipsoid.Sample p n) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin n => gaussianBlockSplit e)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (GaussianEllipsoid.Vector j)
      (GaussianEllipsoid.Vector p) (Fin n))

/-- The complete row sample, rather than only its marginals, splits into
independent iid Gaussian head and tail samples. -/
theorem gaussianSampleBlockSplit_preserving {d j p : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p)) (n : ℕ) :
    MeasurePreserving (gaussianSampleBlockSplit e n) (GaussianEllipsoid.gaussianSampleLaw d n)
      ((GaussianEllipsoid.gaussianSampleLaw j n).prod (GaussianEllipsoid.gaussianSampleLaw p n)) := by
  exact (measurePreserving_arrowProdEquivProdArrow (GaussianEllipsoid.Vector j)
    (GaussianEllipsoid.Vector p) (Fin n)
    (fun _ => GaussianEllipsoid.gaussianVectorLaw j)
    (fun _ => GaussianEllipsoid.gaussianVectorLaw p)).comp
    (measurePreserving_pi (fun _ : Fin n => GaussianEllipsoid.gaussianVectorLaw d)
      (fun _ => (GaussianEllipsoid.gaussianVectorLaw j).prod (GaussianEllipsoid.gaussianVectorLaw p))
      (fun _ => gaussianBlockSplit_preserving e))

/-- Fubini probability bound with explicit measurable joint event and section
bounds. No measurable choice of a head-dependent net or witness is assumed. -/
theorem product_bad_event_bound {H T : Type*} [MeasurableSpace H] [MeasurableSpace T]
    (μ : Measure H) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : Set (H × T)) (hB : MeasurableSet B) (q : ℝ) (hq : 0 ≤ q)
    (hsections : ∀ h : H, ν.real {t | (h, t) ∈ B} ≤ q) :
    (μ.prod ν).real B ≤ q := by
  have he : (μ.prod ν) B ≤ ENNReal.ofReal q := by
    rw [Measure.prod_apply hB]
    calc
      _ ≤ ∫⁻ _h : H, ENNReal.ofReal q ∂μ := by
        apply lintegral_mono
        intro h
        dsimp only
        have hs := ENNReal.ofReal_le_ofReal (hsections h)
        have heq : Prod.mk h ⁻¹' B = {t | (h, t) ∈ B} := by ext t; rfl
        rw [heq]
        simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hs
      _ = ENNReal.ofReal q := by simp
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [Measure.real, ENNReal.toReal_ofReal hq] using hr

/-- Conditioning on every deterministic head sample transfers a tail exceptional
probability bound to the exact unsplit source Gaussian sample. -/
theorem gaussianSample_conditioning_bound {d j p : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p)) (n : ℕ)
    (B : Set (GaussianEllipsoid.Sample j n × GaussianEllipsoid.Sample p n))
    (hB : MeasurableSet B) (q : ℝ) (hq : 0 ≤ q)
    (hsections : ∀ h, (GaussianEllipsoid.gaussianSampleLaw p n).real
      {t | (h, t) ∈ B} ≤ q) :
    (GaussianEllipsoid.gaussianSampleLaw d n).real
      {z | gaussianSampleBlockSplit e n z ∈ B} ≤ q := by
  have heq : {z | gaussianSampleBlockSplit e n z ∈ B} = (gaussianSampleBlockSplit e n) ⁻¹' B := by
    ext z; rfl
  rw [heq, (gaussianSampleBlockSplit_preserving e n).measureReal_preimage hB.nullMeasurableSet]
  exact product_bad_event_bound _ _ B hB q hq hsections

#print axioms gaussianBlockSplit_preserving
#print axioms gaussianSampleBlockSplit_preserving
#print axioms gaussianSample_conditioning_bound
end UCEscape
