import BMGordonExpectations
import BMGordonProcesses
import GordonCompactPassage

noncomputable section
open scoped InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace BMGordon

theorem primaryValue_eq_compactMinMax {n d : ℕ} (κ R : ℝ) (ω : Space n d) :
    primaryValue n d κ R ω = BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => primary p ω+rowDrift R p.1) ω := rfl

theorem auxiliaryValue_eq_compactMinMax {n d : ℕ} (κ R : ℝ) (ω : Space n d) :
    auxiliaryValue n d κ R ω = BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => auxiliary p ω+rowDrift R p.1) ω := rfl

theorem primary_compact_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ ω, BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => primary p ω+rowDrift R p.1) ω ∂law n d) =
      statisticMean n d κ R := primaryValue_mean hn hd hκ R

theorem auxiliary_compact_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ ω, BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => auxiliary p ω+rowDrift R p.1) ω ∂law n d) =
      conditionedWidth d κ - (∫ h : Euclid n, ‖h-R⁻¹ • ones n‖ ∂euclideanGaussianLaw (Fin n)) :=
  auxiliaryValue_mean hn hd hκ R

theorem primary_compact_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => primary p ω+rowDrift R p.1)) (law n d) :=
  primaryValue_integrable hn hd hκ R

theorem auxiliary_compact_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (BMGordonCompact.compactMinMax
      (fun p : UnitSample n × UnitCone d κ => fun ω => auxiliary p ω+rowDrift R p.1)) (law n d) :=
  auxiliaryValue_integrable hn hd hκ R

theorem expectedGordonComparison_of_compact {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R : ℝ}
    (hκ : 1 ≤ κ)
    (hcompare : (∫ ω, BMGordonCompact.compactMinMax
        (fun p : UnitSample n × UnitCone d κ => fun ω => auxiliary p ω+rowDrift R p.1) ω ∂law n d) ≤
      ∫ ω, BMGordonCompact.compactMinMax
        (fun p : UnitSample n × UnitCone d κ => fun ω => primary p ω+rowDrift R p.1) ω ∂law n d) :
    ExpectedGordonComparison n d κ R := expectedGordonComparison_of_values hn hd hκ hcompare

#print axioms splitBlocks_preserving
#print axioms matrixBlock_preserving
#print axioms scalarBlock_preserving
#print axioms widthBlock_preserving
#print axioms driftBlock_preserving
#print axioms primaryValue_eq
#print axioms auxiliaryValue_eq
#print axioms primary_compact_integrable
#print axioms auxiliary_compact_integrable
#print axioms primary_compact_mean
#print axioms auxiliary_compact_mean
#print axioms expectedGordonComparison_of_compact
end BMGordon
