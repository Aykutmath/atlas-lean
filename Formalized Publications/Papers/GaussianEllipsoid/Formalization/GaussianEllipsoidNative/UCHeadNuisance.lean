import UCGaussianBlockConditioning
import GaussianEllipsoid.AboveObjects

noncomputable section
open MeasureTheory ProbabilityTheory
namespace UCEscape

/-- All head quadratic monomials and a constant column. Symmetry is unnecessary
for the uniform rank bound 1+j². -/
def headFeature {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    Option (Fin j × Fin j) → EuclideanSpace ℝ (Fin n)
  | none => WithLp.toLp 2 (fun _ => 1)
  | some ab => WithLp.toLp 2 (fun i => h i ab.1 * h i ab.2)

def headNuisanceSpace {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range (headFeature h))

theorem headNuisanceSpace_finrank {j n : ℕ} (h : GaussianEllipsoid.Sample j n) :
    Module.finrank ℝ (headNuisanceSpace h) ≤ 1 + j^2 := by
  change (Set.range (headFeature h)).finrank ℝ ≤ 1 + j^2
  apply (finrank_range_le_card (R := ℝ) (headFeature h)).trans
  simp [pow_two, Nat.add_comm]

/-- Every deterministic head quadratic form plus a constant belongs to the
explicit head-generated nuisance subspace. -/
theorem head_quadratic_mem_nuisance {j n : ℕ} (h : GaussianEllipsoid.Sample j n)
    (H : GaussianEllipsoid.Square j) (b : ℝ) :
    (WithLp.toLp 2 (fun i => GaussianEllipsoid.quadratic H (h i) + b)) ∈ headNuisanceSpace h := by
  have hnone : headFeature h none ∈ headNuisanceSpace h := Submodule.subset_span ⟨none, rfl⟩
  have hsome (ab : Fin j × Fin j) : headFeature h (some ab) ∈ headNuisanceSpace h :=
    Submodule.subset_span ⟨some ab, rfl⟩
  have hm : b • headFeature h none +
      (∑ ab : Fin j × Fin j, H ab.1 ab.2 • headFeature h (some ab)) ∈ headNuisanceSpace h :=
    (headNuisanceSpace h).add_mem ((headNuisanceSpace h).smul_mem b hnone)
      ((headNuisanceSpace h).sum_mem (fun ab _ => (headNuisanceSpace h).smul_mem _ (hsome ab)))
  convert hm using 1
  ext i
  simp [headFeature, GaussianEllipsoid.quadratic, dotProduct, Matrix.mulVec,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, add_comm]

/-- Centering and normalization only change the nuisance coefficients. -/
theorem head_measurementQ_mem_nuisance {j n : ℕ} (h : GaussianEllipsoid.Sample j n)
    (H : GaussianEllipsoid.Square j) (b : ℝ) :
    (WithLp.toLp 2 (fun i => GaussianEllipsoid.measurementQ h H i + b)) ∈ headNuisanceSpace h := by
  have hquad := head_quadratic_mem_nuisance h H (b * Real.sqrt 2 - Matrix.trace H)
  have hm := (headNuisanceSpace h).smul_mem (Real.sqrt 2)⁻¹ hquad
  convert hm using 1
  ext i
  simp only [GaussianEllipsoid.measurementQ, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp <;> ring

/-- Every scaled affine centered head quadratic belongs to the same fixed
nuisance span, with no restriction on its scalar coefficients. -/
theorem head_affine_div_mem_nuisance {j n : ℕ} (h : GaussianEllipsoid.Sample j n)
    (H : GaussianEllipsoid.Square j) (b ρ : ℝ) :
    (WithLp.toLp 2 (fun i => (b - GaussianEllipsoid.measurementQ h H i) / ρ)) ∈ headNuisanceSpace h := by
  have hconst : headFeature h none ∈ headNuisanceSpace h := Submodule.subset_span ⟨none, rfl⟩
  have hm := (headNuisanceSpace h).smul_mem ρ⁻¹
    ((headNuisanceSpace h).sub_mem ((headNuisanceSpace h).smul_mem b hconst)
      (head_measurementQ_mem_nuisance h H 0))
  convert hm using 1
  ext i
  change (b - GaussianEllipsoid.measurementQ h H i) / ρ =
    ρ⁻¹ * (b * 1 - (GaussianEllipsoid.measurementQ h H i + 0))
  ring

theorem head_affine_div_eq {j n : ℕ} (h : GaussianEllipsoid.Sample j n)
    (H : GaussianEllipsoid.Square j) (b ρ : ℝ) (i : Fin n) :
    (b - GaussianEllipsoid.measurementQ h H i) / ρ =
      GaussianEllipsoid.measurementQ h ((-ρ⁻¹) • H) i + b / ρ := by
  rw [GaussianEllipsoid.measurementQ_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Joint existential bad event for a fixed tail class. The head matrix and
scalar are quantified existentially, without a head-dependent selection. -/
def headTailQuadraticBadEvent {j p n : ℕ} (K : Set (GaussianEllipsoid.Square p)) (c : ℝ) :
    Set (GaussianEllipsoid.Sample j n × GaussianEllipsoid.Sample p n) :=
  {z | ∃ D : K, ∃ H : GaussianEllipsoid.Square j, ∃ b : ℝ,
    (∑ i, |GaussianEllipsoid.measurementQ z.2 D.val i -
      GaussianEllipsoid.measurementQ z.1 H i - b|) / (n : ℝ) < c}

/-- A scaled-head residual is already included in the explicit joint bad event.
This is the normalization step used for a non-small peeled tail. -/
theorem headTailQuadraticBadEvent_of_scaled_residual {j p n : ℕ}
    (K : Set (GaussianEllipsoid.Square p)) (c : ℝ)
    (h : GaussianEllipsoid.Sample j n) (t : GaussianEllipsoid.Sample p n)
    (D : GaussianEllipsoid.Square p) (hD : D ∈ K)
    (H : GaussianEllipsoid.Square j) (b ρ : ℝ)
    (hbad : (∑ i, |GaussianEllipsoid.measurementQ t D i -
      (b - GaussianEllipsoid.measurementQ h H i) / ρ|) / (n : ℝ) < c) :
    (h, t) ∈ headTailQuadraticBadEvent K c := by
  refine ⟨⟨D, hD⟩, (-ρ⁻¹) • H, b / ρ, ?_⟩
  simp_rw [head_affine_div_eq h H b ρ] at hbad
  simpa only [sub_add_eq_sub_sub] using hbad

/-- Arbitrary unions over tail matrices and head nuisance parameters are open,
since each strict residual inequality is continuous in both samples. -/
theorem headTailQuadraticBadEvent_isOpen {j p n : ℕ}
    (K : Set (GaussianEllipsoid.Square p)) (c : ℝ) : IsOpen (headTailQuadraticBadEvent (j := j) (n := n) K c) := by
  simp only [headTailQuadraticBadEvent, Set.ofPred_exists]
  apply isOpen_iUnion
  intro D
  apply isOpen_iUnion
  intro H
  apply isOpen_iUnion
  intro b
  apply isOpen_lt _ continuous_const
  unfold GaussianEllipsoid.measurementQ GaussianEllipsoid.quadratic Matrix.mulVec dotProduct
  fun_prop

/-- The section event is bounded by the all-nuisance event in a deterministic
subspace of rank at most 1+j². -/
theorem headTailQuadraticBadEvent_section_subset {j p n : ℕ}
    (K : Set (GaussianEllipsoid.Square p)) (c : ℝ) (h : GaussianEllipsoid.Sample j n) :
    {t | (h, t) ∈ headTailQuadraticBadEvent K c} ⊆
      {t | ∃ D : K, ∃ v : EuclideanSpace ℝ (Fin n), v ∈ headNuisanceSpace h ∧
        (∑ i, |GaussianEllipsoid.measurementQ t D.val i - v i|) / (n : ℝ) < c} := by
  rintro t ⟨D, H, b, hb⟩
  refine ⟨D, WithLp.toLp 2 (fun i => GaussianEllipsoid.measurementQ h H i + b),
    head_measurementQ_mem_nuisance h H b, ?_⟩
  simpa only [PiLp.toLp_apply, sub_add_eq_sub_sub] using hb

/-- A uniform deterministic-nuisance tail bound transfers through conditioning
on the head and the exact original Gaussian sample law. -/
theorem gaussian_head_conditioning_transfer {d j p n : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin p))
    (K : Set (GaussianEllipsoid.Square p)) (c q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ L ≤ 1 + j^2 →
      (GaussianEllipsoid.gaussianSampleLaw p n).real
        {t | ∃ D : K, ∃ v : EuclideanSpace ℝ (Fin n), v ∈ L ∧
          (∑ i, |GaussianEllipsoid.measurementQ t D.val i - v i|) / (n : ℝ) < c} ≤ q) :
    (GaussianEllipsoid.gaussianSampleLaw d n).real
      {z | gaussianSampleBlockSplit e n z ∈ headTailQuadraticBadEvent K c} ≤ q := by
  apply gaussianSample_conditioning_bound e n _
    (headTailQuadraticBadEvent_isOpen K c).measurableSet q hq
  intro h
  apply (measureReal_mono (headTailQuadraticBadEvent_section_subset K c h)).trans
  exact hbound (headNuisanceSpace h) (headNuisanceSpace_finrank h)

#print axioms head_affine_div_mem_nuisance
#print axioms headTailQuadraticBadEvent_of_scaled_residual
#print axioms headNuisanceSpace_finrank
#print axioms head_measurementQ_mem_nuisance
#print axioms headTailQuadraticBadEvent_isOpen
#print axioms gaussian_head_conditioning_transfer
end UCEscape
