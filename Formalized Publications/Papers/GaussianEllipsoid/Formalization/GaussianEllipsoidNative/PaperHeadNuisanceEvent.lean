import PaperHeadNuisanceStructure

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory Set Module
open scoped BigOperators Topology
namespace UCEscape
open GaussianEllipsoid

/-- Literal existential nuisance event, retaining the closed l1 cap. -/
def headNuisanceBad (j p n : ℕ) (τ B c : ℝ) : Set (Sample j n × Sample p n) :=
  {z | ∃ D : Square p, D.PosSemidef ∧ frobeniusNorm D=1 ∧ matrixOpNorm D≤τ ∧
    ∃ v : EuclideanSpace ℝ (Fin n), v ∈ headNuisanceSpace z.1 ∧
      (∑ i, |v i|) ≤ B*n ∧ (1/(n:ℝ))*(∑ i, |measurementQ z.2 D i-v i|) < c}

private def cappedHeadVector {j n : ℕ} (B : ℝ)
    (a : Option (Fin j × Fin j) → ℝ) (h : Sample j n) : EuclideanSpace ℝ (Fin n) :=
  let v := ∑ k, a k • headFeature h k
  (B*n / max (B*n) (∑ i, |v i|)) • v

private theorem cappedHeadVector_mem {j n : ℕ} (B : ℝ)
    (a : Option (Fin j × Fin j) → ℝ) (h : Sample j n) :
    cappedHeadVector B a h ∈ headNuisanceSpace h := by
  apply Submodule.smul_mem
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩))

private theorem cappedHeadVector_cap {j n : ℕ} (B : ℝ) (hBn : 0<B*n)
    (a : Option (Fin j × Fin j) → ℝ) (h : Sample j n) :
    (∑ i, |cappedHeadVector B a h i|) ≤ B*n := by
  let v := ∑ k, a k • headFeature h k
  have hm : 0 < max (B*n) (∑ i, |v i|) := hBn.trans_le (le_max_left _ _)
  change (∑ i, |(B*n / max (B*n) (∑ i, |v i|))*v i|) ≤ B*n
  simp_rw [abs_mul, abs_of_pos (div_pos hBn hm), ← Finset.mul_sum]
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hBn.le

private theorem cappedHeadVector_eq {j n : ℕ} (B : ℝ) (hBn : 0<B*n)
    (a : Option (Fin j × Fin j) → ℝ) (h : Sample j n)
    (hc : (∑ i, |(∑ k, a k • headFeature h k) i|) ≤ B*n) :
    cappedHeadVector B a h = ∑ k, a k • headFeature h k := by
  dsimp only [cappedHeadVector]
  rw [max_eq_left hc, div_self (ne_of_gt hBn), one_smul]

private theorem continuous_cappedHeadVector {j n : ℕ} (B : ℝ) (hBn : 0<B*n)
    (a : Option (Fin j × Fin j) → ℝ) : Continuous (cappedHeadVector (j:=j) (n:=n) B a) := by
  have hf (k : Option (Fin j × Fin j)) : Continuous (fun h : Sample j n => headFeature h k) := by
    cases k with
    | none => exact continuous_const
    | some ab =>
      change Continuous (fun h : Sample j n => WithLp.toLp 2 (fun i => h i ab.1*h i ab.2))
      fun_prop
  have hv : Continuous (fun h : Sample j n => ∑ k, a k • headFeature h k) := by fun_prop
  have hs : Continuous (fun h : Sample j n => ∑ i, |(∑ k,a k • headFeature h k) i|) := by fun_prop
  exact (continuous_const.div (continuous_const.max hs)
    (fun h => ne_of_gt (hBn.trans_le (le_max_left _ _)))).smul hv

/-- Openness includes rank-drop points. A continuous radial cap of each finite
linear combination avoids assuming continuity of a basis or of the projector. -/
theorem headNuisanceBad_isOpen (j p n : ℕ) (τ B c : ℝ) (hBn : 0<B*n) :
    IsOpen (headNuisanceBad j p n τ B c) := by
  classical
  have he : headNuisanceBad j p n τ B c =
      ⋃ D : {D : Square p // D.PosSemidef ∧ frobeniusNorm D=1 ∧ matrixOpNorm D≤τ},
      ⋃ a : Option (Fin j × Fin j) → ℝ,
      {z : Sample j n × Sample p n |
        (1/(n:ℝ))*(∑ i, |measurementQ z.2 D.val i-cappedHeadVector B a z.1 i|) < c} := by
    ext z
    simp only [headNuisanceBad, mem_setOf_eq, mem_iUnion, Subtype.exists]
    constructor
    · rintro ⟨D,hD,hF,hOp,v,hv,hcap,hbad⟩
      obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
      refine ⟨D,⟨hD,hF,hOp⟩,a,?_⟩
      rw [cappedHeadVector_eq B hBn a z.1 (by simpa [ha] using hcap),ha]
      exact hbad
    · rintro ⟨D,⟨hD,hF,hOp⟩,a,hbad⟩
      exact ⟨D,hD,hF,hOp,cappedHeadVector B a z.1,cappedHeadVector_mem B a z.1,
        cappedHeadVector_cap B hBn a z.1,hbad⟩
  rw [he]
  apply isOpen_iUnion
  intro D
  apply isOpen_iUnion
  intro a
  apply isOpen_lt _ continuous_const
  have hv : Continuous (fun z : Sample j n × Sample p n => cappedHeadVector B a z.1) :=
    (continuous_cappedHeadVector B hBn a).comp continuous_fst
  unfold measurementQ quadratic Matrix.mulVec dotProduct
  fun_prop

end UCEscape

#print axioms UCEscape.headNuisanceBad_isOpen
