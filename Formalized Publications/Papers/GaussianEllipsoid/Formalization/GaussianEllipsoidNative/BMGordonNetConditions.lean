import BMGordonProcesses
import BMGordonFiniteBounds

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace BMGordon

variable {n d : ℕ} {κ : ℝ} {I J : Type*}
  [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

theorem primary_finite_abs_le (u : I → UnitSample n) (S : J → UnitCone d κ) (ω : Space n d) :
    |finiteValue (fun i j => primary (u i,S j)) ω| ≤ 2*‖ω‖ :=
  finiteValue_abs_le _ _ (fun i j ω => primary_abs_le (u i,S j) ω) ω

theorem auxiliary_finite_abs_le (u : I → UnitSample n) (S : J → UnitCone d κ) (ω : Space n d) :
    |finiteValue (fun i j => auxiliary (u i,S j)) ω| ≤ 2*‖ω‖ :=
  finiteValue_abs_le _ _ (fun i j ω => auxiliary_abs_le (u i,S j) ω) ω

theorem primary_finite_integrable (u : I → UnitSample n) (S : J → UnitCone d κ) :
    Integrable (finiteValue (fun i j => primary (u i,S j))) (law n d) :=
  finiteValue_integrable _ _ _ (fun i j => primary_sample_continuous (u i,S j))
    (envelope_integrable n d) (fun i j ω => primary_abs_le (u i,S j) ω)

theorem auxiliary_finite_integrable (u : I → UnitSample n) (S : J → UnitCone d κ) :
    Integrable (finiteValue (fun i j => auxiliary (u i,S j))) (law n d) :=
  finiteValue_integrable _ _ _ (fun i j => auxiliary_sample_continuous (u i,S j))
    (envelope_integrable n d) (fun i j ω => auxiliary_abs_le (u i,S j) ω)

theorem affine_envelope_integrable (R : ℝ) :
    Integrable (fun ω : Space n d => 2*‖ω‖+Real.sqrt n/|R|) (law n d) :=
  (envelope_integrable n d).add (integrable_const _)

theorem primary_affine_abs_le (R : ℝ) (p : UnitSample n × UnitCone d κ) (ω : Space n d) :
    |primary p ω+rowDrift R p.1| ≤ 2*‖ω‖+Real.sqrt n/|R| :=
  (abs_add_le _ _).trans (add_le_add (primary_abs_le p ω) (rowDrift_abs_le R p.1))

theorem auxiliary_affine_abs_le (R : ℝ) (p : UnitSample n × UnitCone d κ) (ω : Space n d) :
    |auxiliary p ω+rowDrift R p.1| ≤ 2*‖ω‖+Real.sqrt n/|R| :=
  (abs_add_le _ _).trans (add_le_add (auxiliary_abs_le p ω) (rowDrift_abs_le R p.1))

theorem primary_affine_finite_integrable (R : ℝ) (u : I → UnitSample n) (S : J → UnitCone d κ) :
    Integrable (finiteValue (fun i j ω => primary (u i,S j) ω+rowDrift R (u i))) (law n d) :=
  finiteValue_integrable _ _ _
    (fun i j => (primary_sample_continuous (u i,S j)).add continuous_const)
    (affine_envelope_integrable R) (fun i j ω => primary_affine_abs_le R (u i,S j) ω)

theorem auxiliary_affine_finite_integrable (R : ℝ) (u : I → UnitSample n) (S : J → UnitCone d κ) :
    Integrable (finiteValue (fun i j ω => auxiliary (u i,S j) ω+rowDrift R (u i))) (law n d) :=
  finiteValue_integrable _ _ _
    (fun i j => (auxiliary_sample_continuous (u i,S j)).add continuous_const)
    (affine_envelope_integrable R) (fun i j ω => auxiliary_affine_abs_le R (u i,S j) ω)

end BMGordon
