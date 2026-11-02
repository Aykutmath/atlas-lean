import BMGordonNetConditions
import GordonCompactPassage

noncomputable section
open scoped InnerProductSpace
open MeasureTheory GaussianEllipsoid BMGeometry BMSaddle
namespace BMGordon

def affinePrimary {n d : ℕ} {κ : ℝ} (R : ℝ)
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) : ℝ := primary p ω+rowDrift R p.1

def affineAuxiliary {n d : ℕ} {κ : ℝ} (R : ℝ)
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) : ℝ := auxiliary p ω+rowDrift R p.1

theorem affinePrimary_path_continuous {n d : ℕ} {κ : ℝ} (R : ℝ) (ω : Space n d) :
    Continuous (fun p : UnitSample n × UnitCone d κ => affinePrimary R p ω) :=
  (primary_path_continuous ω).add ((rowDrift_continuous R).comp continuous_fst)

theorem affineAuxiliary_path_continuous {n d : ℕ} {κ : ℝ} (R : ℝ) (ω : Space n d) :
    Continuous (fun p : UnitSample n × UnitCone d κ => affineAuxiliary R p ω) :=
  (auxiliary_path_continuous ω).add ((rowDrift_continuous R).comp continuous_fst)

/-- The supplied compact analysis applied to the genuine shared-drift processes.
The finite comparison remains an explicit input here until the separate affine
interpolation theorem is supplied; every regularity and domination premise is discharged. -/
theorem compact_affine_comparison_of_finite {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ)
    (hFinite : ∀ (I J : Type) [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
      (u : I → UnitSample n) (S : J → UnitCone d κ),
      (∫ ω, finiteValue (fun i j => affineAuxiliary R (u i,S j)) ω ∂law n d) ≤
        ∫ ω, finiteValue (fun i j => affinePrimary R (u i,S j)) ω ∂law n d) :
    (∫ ω, BMGordonCompact.compactMinMax (affineAuxiliary (κ := κ) R) ω ∂law n d) ≤
      ∫ ω, BMGordonCompact.compactMinMax (affinePrimary (κ := κ) R) ω ∂law n d := by
  letI : Nonempty (UnitSample n) := unitSample_nonempty hn
  letI : Nonempty (UnitCone d κ) := unitCone_nonempty hd hκ
  apply BMGordonCompact.compact_comparison_of_finite (UnitSample n) (UnitCone d κ)
    (Space n d) (law n d) (affineAuxiliary R) (affinePrimary R)
  · exact ae_of_all _ (affineAuxiliary_path_continuous R)
  · exact ae_of_all _ (affinePrimary_path_continuous R)
  · intro tK tL htK htL _ _ _ _
    exact hFinite ↥tK ↥tL (fun i => i.1) (fun j => j.1)
  · intro tK tL htK htL _ _ _ _
    exact ⟨auxiliary_affine_finite_integrable R (fun i : ↥tK => i.1) (fun j : ↥tL => j.1),
      primary_affine_finite_integrable R (fun i : ↥tK => i.1) (fun j : ↥tL => j.1)⟩
  · refine ⟨(fun ω => 2*‖ω‖+Real.sqrt n/|R|), (fun ω => 2*‖ω‖+Real.sqrt n/|R|),
      affine_envelope_integrable R, affine_envelope_integrable R, ?_⟩
    intro tK tL htK htL _ _ _ _
    constructor
    · exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using! finiteValue_abs_le
          (fun i : ↥tK => fun j : ↥tL => affineAuxiliary R (i.1,j.1))
          (fun ω => 2*‖ω‖+Real.sqrt n/|R|)
          (fun i j ω => auxiliary_affine_abs_le R (i.1,j.1) ω) ω
    · exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs] using! finiteValue_abs_le
          (fun i : ↥tK => fun j : ↥tL => affinePrimary R (i.1,j.1))
          (fun ω => 2*‖ω‖+Real.sqrt n/|R|)
          (fun i j ω => primary_affine_abs_le R (i.1,j.1) ω) ω

end BMGordon
