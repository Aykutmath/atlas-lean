import ExplicitCappedVector
import GaussianSelectedColumns

noncomputable section
open MeasureTheory Finset GaussianTensorMoments
namespace GaussianEllipsoid.CappedSimplex

/-- Paper Lemma 5.1 under the literal independent standard Gaussian vector law.
S contains k=floor(1/a) full-cap coordinates; R contains the single remainder
coordinate exactly when rho is nonzero. Any ordering gives the same result. -/
theorem paper_capped_simplex_extremizer (r N : ℕ) {a s : ℝ}
    (ha : 0 < a) (_ha1 : a < 1) (hs : 0 < s) (w : Fin N → ℝ)
    (hw : (∀ i, 0 ≤ w i ∧ w i ≤ a) ∧ ∑ i, w i = 1)
    (S R : Finset (Fin N)) (hSR : Disjoint S R)
    (hS : S.card = Nat.floor (1/a))
    (hR : R.card = if 1 - (Nat.floor (1/a):ℝ)*a = 0 then 0 else 1) :
    (∫⁻ g : Fin N → Fin r → ℝ,
      ((ENNReal.ofReal (∑ i, w i • Matrix.vecMulVec (g i) (g i)).det)^s)⁻¹
        ∂Measure.pi (fun _ : Fin N => gaussianProductLaw (Fin r))) ≤
    (∫⁻ g : Fin N → Fin r → ℝ,
      ((ENNReal.ofReal (∑ i, cappedVector a S R i • Matrix.vecMulVec (g i) (g i)).det)^s)⁻¹
        ∂Measure.pi (fun _ : Fin N => gaussianProductLaw (Fin r))) := by
  exact extendedRealMoment_le_explicit_cappedVector (gaussianProductLaw (Fin r)) ha hs hw S R hSR hS hR
end GaussianEllipsoid.CappedSimplex
#print axioms GaussianEllipsoid.CappedSimplex.paper_capped_simplex_extremizer
