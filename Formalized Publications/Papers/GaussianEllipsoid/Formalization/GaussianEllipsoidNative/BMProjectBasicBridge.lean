import GaussianEllipsoid.Basic
import BMApproximateFittingUnconditional

/-!
# Verified BM bridges to the user's actual Basic module

GaussianEllipsoid.Basic is the unchanged supplied Basic(1).lean, compiled in
an external temporary module layout. This file imports that actual module and
proves literal coordinate bridges. It does not define or mock the unavailable
GaussianEllipsoid.GaussianProbability or GaussianEllipsoid.BelowObjects modules.
The endpoint below still explicitly names the independently verified raw iid
Gaussian law until the user's actual GaussianProbability definition is supplied.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace GaussianEllipsoidBMBridge

/-- The user's actual coordinate quadratic and the proved BM quadratic coincide. -/
theorem quadratic_eq_bm {d : ℕ} (S : GaussianEllipsoid.Square d)
    (x : GaussianEllipsoid.Vector d) :
    GaussianEllipsoid.quadratic S x = BMRescaling.quadratic S x := rfl

/-- The user's actual residual is exactly the physical fitting residual. -/
theorem residual_apply_eq_bm {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (S : GaussianEllipsoid.Square d) (i : Fin n) :
    GaussianEllipsoid.residual x S i = BMRescaling.fittingResidual S (x i) := rfl

/-- Whole-vector form of the exact actual-project residual bridge. -/
theorem residual_eq_bm {d n : ℕ} (x : GaussianEllipsoid.Sample d n)
    (S : GaussianEllipsoid.Square d) :
    GaussianEllipsoid.residual x S = fun i => BMRescaling.fittingResidual S (x i) := rfl

/-- The user's extended dimension ratio is literally the original strict-limsup ratio. -/
theorem dimensionRatio_eq (n : ℕ → ℕ) (d : ℕ) :
    GaussianEllipsoid.dimensionRatio n d = (n d : ℝ≥0∞)/(d : ℝ≥0∞)^2 := rfl

/-- All real-power risks, not only r=1, coincide on the user's actual coordinates. -/
theorem fittingRisk_eq_project {d n : ℕ} (r : ℝ) (S : GaussianEllipsoid.Square d)
    (x : GaussianEllipsoid.Sample d n) :
    BMBoxRiskAssembly.fittingRisk r S x =
      (1/(n:ℝ))*∑ i, |GaussianEllipsoid.residual x S i|^r := rfl

/-- The infimum-risk formula in BelowObjects, before any named project-law
identification, is the exact already-proved BM infimum. -/
theorem minFittingRisk_eq_project_expression
    (d n : ℕ) (x : GaussianEllipsoid.Sample d n) (lo hi r : ℝ) :
    BMBoxRiskAssembly.minFittingRisk d n x lo hi r =
      sInf {t : ℝ | ∃ S : GaussianEllipsoid.Square d,
        (S-lo • (1 : GaussianEllipsoid.Square d)).PosSemidef ∧
        (hi • (1 : GaussianEllipsoid.Square d)-S).PosSemidef ∧
        t=(1/(n:ℝ))*∑ i, |GaussianEllipsoid.residual x S i|^r} := by
  unfold BMBoxRiskAssembly.minFittingRisk BMRescaling.spectralBox
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, fittingRisk_eq_project, exists_prop, and_assoc]

/-- Unconditional full BM formula on the user's actual Basic types, quadratic,
residual and ENNReal dimension ratio. The Gaussian law is deliberately still
named coordinateSampleLaw; this is not a claim that GaussianProbability or
BelowObjects has compiled or been identified. -/
theorem bm_formula_actual_Basic_rawGaussianLaw :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (GaussianEllipsoid.dimensionRatio n) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Tendsto (fun d => (BMBoxRiskAssembly.coordinateSampleLaw d (n d)).real
            {x : GaussianEllipsoid.Sample d (n d) |
              ε < sInf {t : ℝ | ∃ S : GaussianEllipsoid.Square d,
                (S-lo • (1 : GaussianEllipsoid.Square d)).PosSemidef ∧
                (hi • (1 : GaussianEllipsoid.Square d)-S).PosSemidef ∧
                t=(1/(n d:ℝ))*∑ i, |GaussianEllipsoid.residual x S i|^r}})
            atTop (nhds 0) := by
  intro n hn haspect
  obtain ⟨lo,hi,hlo,hlohi,hfit⟩ := BMBoxRiskAssembly.bmApproximateFitting n hn haspect
  refine ⟨lo,hi,hlo,hlohi,?_⟩
  intro r hr hrq ε hε
  simpa only [← minFittingRisk_eq_project_expression] using hfit r hr hrq ε hε

end GaussianEllipsoidBMBridge
