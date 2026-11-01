module

/-
# Core definitions: simplex functional and coordinate gaps (HI-DEF-S, HI-DEF-D)

Paper-faithful definitions of the two protagonists:
- `S d ν = E vol_d(conv{Z_0,…,Z_d})`, §1 Eq.(1), as a lower Lebesgue integral
  (so `+∞` values are handled by `ℝ≥0∞` arithmetic);
- `gap j ν = E |Z^{(j)} - Z'^{(j)}|`, §1 Eq.(2).

The ambient space `R^d` is `EuclideanSpace ℝ (Fin d)` with `volume`.
The paper's convention `S_0 = 1` is recovered as a theorem for `d = 0`
(`volume` on `EuclideanSpace ℝ (Fin 0)` is the Dirac measure).
-/

public import Mathlib

namespace HypercubeInequality

open MeasureTheory Measure
open scoped ENNReal NNReal

variable {d : ℕ}

/-- Paper determinant convention `det(1; v_0,…,v_k)`: determinant of the
`(k+1) × (k+1)` matrix with rows `(1, v_r)` (HI-DEF-DET). -/
@[expose] public noncomputable def simDet {k : ℕ} (v : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    ℝ :=
  Matrix.det (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => v r j) c))

/-- Simplex functional `S_d(ν)` (§1 Eq.(1)): expected `d`-volume of the convex
hull of `d+1` independent samples with law `ν`. -/
@[expose] public noncomputable def S (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ Z, volume (convexHull ℝ (Set.range Z))
    ∂(Measure.pi (fun _ : Fin (d + 1) => ν))

/-- Coordinate gap `D_j(ν)` (§1 Eq.(2)): mean absolute difference of the `j`th
coordinates of two independent samples with law `ν`. -/
@[expose] public noncomputable def gap {d : ℕ} (j : Fin d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ p, (‖p.1 j - p.2 j‖₊ : ℝ≥0∞) ∂(ν.prod ν)

/-- The gap integrand is measurable. -/
public theorem measurable_coord {d : ℕ} (j : Fin d) :
    Measurable fun x : EuclideanSpace ℝ (Fin d) => x j :=
  (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))

public theorem measurable_gap_integrand {d : ℕ} (j : Fin d) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (‖p.1 j - p.2 j‖₊ : ℝ≥0∞) := by
  apply measurable_coe_nnreal_ennreal.comp
  apply Measurable.nnnorm
  apply Measurable.sub
  · exact (measurable_coord j).comp measurable_fst
  · exact (measurable_coord j).comp measurable_snd

end HypercubeInequality
