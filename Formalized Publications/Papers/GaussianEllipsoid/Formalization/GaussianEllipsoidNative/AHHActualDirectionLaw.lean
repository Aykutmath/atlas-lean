import AHHComplexRadialLaw

/-! Extracting direction and squared radius from the actual Gaussian vector,
including a measurable choice at the null origin. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set GaussianMixedNormHelpers
open scoped ENNReal
namespace AHHRadial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

def defaultUnit : UnitSphere E :=
  ⟨(NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1) |>.mpr zero_le_one).choose,
    (NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1) |>.mpr zero_le_one).choose_spec⟩

/-- The value at zero is immaterial, but is explicitly and measurably chosen. -/
def direction (x : E) : UnitSphere E := by
  classical
  exact ⟨if x = 0 then (defaultUnit (E := E)).val else ‖x‖⁻¹ • x, by
    split_ifs with hx
    · exact (defaultUnit (E := E)).property
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem measurable_direction : Measurable (direction (E := E)) := by
  classical
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_singleton (0 : E)) measurable_const (by fun_prop : Measurable (fun x : E => ‖x‖⁻¹ • x))

@[simp] theorem direction_assemble (p : UnitSphere E × Radius) :
    direction (assemble p) = p.1 := by
  classical
  have hn : assemble p ≠ 0 := by
    intro he
    have h := norm_assemble p
    rw [he, norm_zero] at h
    exact p.2.property.ne' h.symm
  apply Subtype.ext
  change (if assemble p = 0 then (defaultUnit (E := E)).val else ‖assemble p‖⁻¹ • assemble p) = _
  rw [if_neg hn, norm_assemble, assemble, smul_smul, inv_mul_cancel₀ p.2.property.ne', one_smul]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The actual extracted direction is Haar-uniform, and its squared radius
has the Gamma law, jointly as an independent product. -/
theorem radialGaussian_polar_joint_law {b : ℝ} (hb : 0 < b) :
    (radialGaussianLaw μ b).map (fun x => (direction x, ‖x‖^2)) =
      (sphereLaw μ).prod (gammaMeasure ((Module.finrank ℝ E : ℝ)/2) b) := by
  rw [radialGaussianLaw_eq_map_polar, Measure.map_map
    (measurable_direction.prodMk (by fun_prop)) measurable_assemble]
  have he : (fun x : E => (direction x, ‖x‖^2)) ∘ assemble =
      Prod.map (fun u : UnitSphere E => u) (fun r : Radius => (r : ℝ)^2) := by
    funext p
    change (direction (assemble p), ‖assemble p‖^2) = (p.1, (p.2 : ℝ)^2)
    rw [direction_assemble, norm_assemble]
  rw [he, ← Measure.map_prod_map (f := fun u : UnitSphere E => u)
      (g := fun r : Radius => (r : ℝ)^2) (sphereLaw μ) (radiusLaw μ b)
      measurable_id (by fun_prop), Measure.map_id',
    radiusLaw_map_sq μ hb]

theorem radialGaussian_direction_law {b : ℝ} (hb : 0 < b) :
    (radialGaussianLaw μ b).map direction = sphereLaw μ := by
  letI := isProbabilityMeasure_gammaMeasure
    (show (0 : ℝ) < (Module.finrank ℝ E : ℝ)/2 from
      div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)) hb
  have he := congrArg (Measure.map Prod.fst) (radialGaussian_polar_joint_law μ hb)
  rw [Measure.map_map measurable_fst (measurable_direction.prodMk (by fun_prop)),
    Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he

theorem radialGaussian_direction_radius_independent {b : ℝ} (hb : 0 < b) :
    IndepFun (direction (E := E)) (fun x : E => ‖x‖^2) (radialGaussianLaw μ b) := by
  letI := radialGaussianLaw_isProbabilityMeasure μ hb
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_direction.aemeasurable (by fun_prop)).mpr
  rw [radialGaussian_polar_joint_law μ hb, radialGaussian_direction_law μ hb,
    radialGaussianLaw_map_norm_sq μ hb]

/-- Source-facing extracted unit direction and radius of the literal normalized
complex Gaussian, for either real/imaginary sign. -/
theorem normalizedRow_polar_joint_law (h : ℕ) [NeZero h] (hh : 0 < h) (s : Bool) :
    (AHHGaussian.pairRealRowLaw h).map (fun x =>
      (direction (AHHGaussian.normalizedRow h s x), ‖AHHGaussian.normalizedRow h s x‖^2)) =
      (sphereLaw (volume : Measure (CE h))).prod (gammaMeasure h h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  rw [show (fun x => (direction (AHHGaussian.normalizedRow h s x),
      ‖AHHGaussian.normalizedRow h s x‖^2)) =
      (fun z : CE h => (direction z, ‖z‖^2)) ∘ AHHGaussian.normalizedRow h s from rfl,
    ← Measure.map_map (measurable_direction.prodMk (by fun_prop))
      (by unfold AHHGaussian.normalizedRow AHHGaussian.normalizedCoordinate; fun_prop),
    normalizedRow_law h hh s, radialGaussian_polar_joint_law _ (by exact_mod_cast hh),
    complex_finrank_real]
  congr 2
  push_cast
  ring

theorem normalizedRow_direction_law (h : ℕ) [NeZero h] (hh : 0 < h) (s : Bool) :
    (AHHGaussian.pairRealRowLaw h).map (fun x => direction (AHHGaussian.normalizedRow h s x)) =
      sphereLaw (volume : Measure (CE h)) := by
  change Measure.map (direction ∘ AHHGaussian.normalizedRow h s) _ = _
  rw [← Measure.map_map measurable_direction
    (by unfold AHHGaussian.normalizedRow AHHGaussian.normalizedCoordinate; fun_prop),
    normalizedRow_law h hh s, radialGaussian_direction_law _ (by exact_mod_cast hh)]

theorem normalizedRow_radiusSq_law (h : ℕ) [NeZero h] (hh : 0 < h) (s : Bool) :
    (AHHGaussian.pairRealRowLaw h).map (fun x => ‖AHHGaussian.normalizedRow h s x‖^2) =
      gammaMeasure h h := by
  change Measure.map ((fun z : CE h => ‖z‖^2) ∘ AHHGaussian.normalizedRow h s) _ = _
  rw [← Measure.map_map (by fun_prop)
    (by unfold AHHGaussian.normalizedRow AHHGaussian.normalizedCoordinate; fun_prop),
    normalizedRow_law h hh s, radialGaussianLaw_map_norm_sq _ (by exact_mod_cast hh),
    complex_finrank_real]
  congr 1
  push_cast
  ring

/-- Independence after extracting the direction and radius from the literal
iid real/imaginary Gaussian sample itself. -/
theorem normalizedRow_direction_radius_independent (h : ℕ) [NeZero h]
    (hh : 0 < h) (s : Bool) :
    IndepFun (fun x => direction (AHHGaussian.normalizedRow h s x))
      (fun x => ‖AHHGaussian.normalizedRow h s x‖^2) (AHHGaussian.pairRealRowLaw h) := by
  have hm : Measurable (AHHGaussian.normalizedRow h s) := by
    unfold AHHGaussian.normalizedRow AHHGaussian.normalizedCoordinate
    fun_prop
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_direction.comp hm).aemeasurable (hm.norm.pow_const 2).aemeasurable).mpr
  simp only [Function.comp_def]
  rw [normalizedRow_polar_joint_law h hh s, normalizedRow_direction_law h hh s,
    normalizedRow_radiusSq_law h hh s]

#print axioms radialGaussian_direction_radius_independent
#print axioms normalizedRow_polar_joint_law
#print axioms normalizedRow_direction_radius_independent
end AHHRadial
