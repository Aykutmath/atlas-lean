import GaussianCoordinateSplit
import GaussianCenteredCompression
import GaussianWeightedBilinearMGF

/-! Direct original-sample law for the canonical (b,a)-ordered rows used by
centered quadratic compression. No distributional identification is left to a caller. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.ProjectedClusters
namespace GaussianEllipsoidCandidate

/-- Regroup flat tensor coordinates into the canonical row order (b,a). -/
def tensorToCanonicalRows (n h : ℕ) (z : GaussianEntries n h × GaussianEntries n h) :
    Fin n → Euclid h × Euclid h :=
  fun i => (entriesToRows n h z.2 i, entriesToRows n h z.1 i)

theorem tensorToCanonicalRows_preserving (n h : ℕ) :
    MeasurePreserving (tensorToCanonicalRows n h) (tensorGaussianLaw n h)
      (gaussianBilinearSampleLaw (Fin n) h h) := by
  have hswap : MeasurePreserving Prod.swap (tensorGaussianLaw n h) (tensorGaussianLaw n h) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have hp := (entriesToRows_preserving n h).prod (entriesToRows_preserving n h)
  have he := (measurePreserving_arrowProdEquivProdArrow (Euclid h) (Euclid h) (Fin n)
    (fun _ => euclideanGaussianLaw (Fin h)) (fun _ => euclideanGaussianLaw (Fin h))).symm
  exact he.comp (hp.comp hswap)

theorem extractedRows_eq_tensorToCanonicalRows {n d h : ℕ}
    (eL eR : Fin h ↪ Fin d) (X : Fin n → Euclid d) :
    extractedRows eL eR X = tensorToCanonicalRows n h (splitCoordinateRows n eL eR X) := by
  funext i
  apply Prod.ext
  · ext a
    exact extractedRows_fst eL eR X i a
  · ext b
    exact extractedRows_snd eL eR X i b

/-- Exact pushforward of the original iid standard Euclidean sample law to the
canonical independent rectangular (b,a)-pair row law. -/
theorem extractedRows_preserving {n d h : ℕ} (eL eR : Fin h ↪ Fin d)
    (hdis : ∀ a b, eL a ≠ eR b) :
    MeasurePreserving (extractedRows (n := n) eL eR)
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d)))
      (gaussianBilinearSampleLaw (Fin n) h h) := by
  have he : extractedRows (n := n) eL eR =
      tensorToCanonicalRows n h ∘ splitCoordinateRows n eL eR := by
    funext X
    exact extractedRows_eq_tensorToCanonicalRows eL eR X
  rw [he]
  exact (tensorToCanonicalRows_preserving n h).comp
    (splitCoordinateRows_preserving n eL eR hdis)

theorem euclideanRowsLaw_map_extractedRows {n d h : ℕ} (eL eR : Fin h ↪ Fin d)
    (hdis : ∀ a b, eL a ≠ eR b) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).map
      (extractedRows eL eR) = gaussianBilinearSampleLaw (Fin n) h h :=
  (extractedRows_preserving eL eR hdis).map_eq

end GaussianEllipsoidCandidate
