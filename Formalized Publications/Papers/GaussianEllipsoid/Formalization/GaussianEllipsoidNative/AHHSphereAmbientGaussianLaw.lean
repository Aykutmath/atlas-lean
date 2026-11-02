import AHHSphereEuclideanGeometry
import AHHGaussianEntropyTransfer
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Exact identification of the actual product ensemble as a scaled standard
Gaussian on its product-Euclidean ambient space. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators
namespace AHHRadial

/-- Independent standard Gaussian blocks give the standard Gaussian on their
Hilbert direct sum. -/
theorem map_pi_stdGaussian {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] :
    (Measure.pi (fun i => stdGaussian (E i))).map (WithLp.toLp 2) =
      stdGaussian (PiLp 2 E) := by
  apply Measure.ext_of_charFun (E := PiLp 2 E)
  ext t
  simp_rw [charFun_pi, charFun_stdGaussian, ← Complex.exp_sum, ← Complex.ofReal_pow,
    PiLp.norm_sq_eq_of_L2]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The radial complex block is a standard real Hilbert-space Gaussian scaled
by exactly `1 / sqrt (2h)`. -/
theorem complex_radialGaussian_eq_scaled_stdGaussian (h : ℕ) (hh : 0 < h) :
    radialGaussianLaw (volume : Measure (CE h)) h =
      (stdGaussian (CE h)).map (fun x => (Real.sqrt (2 * (h : ℝ)))⁻¹ • x) := by
  rw [← scaled_complexRealIsometry_gaussian h hh]
  have he : euclideanGaussianLaw (Fin h × Bool) = stdGaussian (RE h) := by
    exact map_pi_eq_stdGaussian
  rw [he, ← stdGaussian_map (complexRealIsometry h)]
  rw [Measure.map_map (by fun_prop) (complexRealIsometry h).continuous.measurable]
  rfl

/-- The exact coordinate embedding of pairs in the product Hilbert space. -/
def pairsToSphereAmbient (n h : ℕ) (z : Fin n → CE h × CE h) : SphereAmbient n h :=
  WithLp.toLp 2 (fun j => if j.2 then (z j.1).2 else (z j.1).1)

/-- The inverse coordinate map, with no change to any complex coordinate. -/
def sphereAmbientToPairs (n h : ℕ) (z : SphereAmbient n h) : Fin n → CE h × CE h :=
  fun i => (z (i, false), z (i, true))

@[simp] theorem sphereAmbientToPairs_pairsToSphereAmbient (n h : ℕ)
    (z : Fin n → CE h × CE h) :
    sphereAmbientToPairs n h (pairsToSphereAmbient n h z) = z := by
  funext i
  exact Prod.eta (z i)

@[simp] theorem pairsToSphereAmbient_sphereAmbientToPairs (n h : ℕ)
    (z : SphereAmbient n h) :
    pairsToSphereAmbient n h (sphereAmbientToPairs n h z) = z := by
  ext ⟨i,b⟩
  cases b <;> rfl

/-- The actual independent-pair Gaussian ensemble on the Euclidean ambient
space, defined by its literal coordinate map. -/
def sphereAmbientGaussianLaw (n h : ℕ) : Measure (SphereAmbient n h) :=
  (gaussianPairsLaw n h).map (pairsToSphereAmbient n h)

/-- Reindexing pairs as Boolean-labelled blocks preserves their literal product law. -/
theorem gaussianPairs_map_unpair (n h : ℕ) (hh : 0 < h) :
    (gaussianPairsLaw n h).map
      (fun z => fun j : Fin n × Bool => if j.2 then (z j.1).2 else (z j.1).1) =
    Measure.pi (fun _ : Fin n × Bool => radialGaussianLaw (volume : Measure (CE h)) h) := by
  let := gaussianPairLaw_probability h hh
  let : NeZero h := ⟨Nat.ne_of_gt hh⟩
  let := radialGaussianLaw_isProbabilityMeasure (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  have hm : Measurable
      (fun z : Fin n → CE h × CE h => fun j : Fin n × Bool =>
        if j.2 then (z j.1).2 else (z j.1).1) := by
    apply measurable_pi_iff.mpr
    rintro ⟨i,b⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  apply (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have hp : (fun z : Fin n → CE h × CE h => fun j : Fin n × Bool =>
        if j.2 then (z j.1).2 else (z j.1).1) ⁻¹' Set.univ.pi S =
      Set.univ.pi (fun i => S (i,false) ×ˢ S (i,true)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod, Prod.forall, Bool.forall_bool, Bool.false_eq_true, ite_false, ite_true]
  rw [hp, gaussianPairsLaw, Measure.pi_pi]
  simp_rw [gaussianPairLaw, Measure.prod_prod]
  rw [Fintype.prod_prod_type]
  simp [mul_comm]

/-- Exact Gaussian law of the ambient embedding. -/
theorem sphereAmbientGaussianLaw_eq_scaled_stdGaussian (n h : ℕ) (hh : 0 < h) :
    sphereAmbientGaussianLaw n h =
      (stdGaussian (SphereAmbient n h)).map
        (fun x => (Real.sqrt (2 * (h : ℝ)))⁻¹ • x) := by
  let a : ℝ := (Real.sqrt (2 * (h : ℝ)))⁻¹
  have hp := gaussianPairs_map_unpair n h hh
  have hm : Measurable
      (fun z : Fin n → CE h × CE h => fun j : Fin n × Bool =>
        if j.2 then (z j.1).2 else (z j.1).1) := by
    apply measurable_pi_iff.mpr
    rintro ⟨i,b⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  change (gaussianPairsLaw n h).map
    ((WithLp.toLp 2) ∘ (fun z => fun j : Fin n × Bool =>
      if j.2 then (z j.1).2 else (z j.1).1)) = _
  rw [← Measure.map_map (by fun_prop) hm, hp]
  simp_rw [complex_radialGaussian_eq_scaled_stdGaussian h hh]
  rw [← Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun x : CE h => a • x) (stdGaussian (CE h)))),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← map_pi_stdGaussian (E := fun _ : Fin n × Bool => CE h),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The coordinate embedding preserves the actual ensemble measure. -/
theorem pairsToSphereAmbient_preserving (n h : ℕ) :
    MeasurePreserving (pairsToSphereAmbient n h) (gaussianPairsLaw n h)
      (sphereAmbientGaussianLaw n h) := by
  refine ⟨?_, rfl⟩
  unfold pairsToSphereAmbient
  apply (MeasurableEquiv.toLp 2 _).measurable.comp
  apply measurable_pi_iff.mpr
  rintro ⟨i,b⟩
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem sphereAmbientToPairs_preserving (n h : ℕ) :
    MeasurePreserving (sphereAmbientToPairs n h) (sphereAmbientGaussianLaw n h)
      (gaussianPairsLaw n h) := by
  have hm : Measurable (sphereAmbientToPairs n h) := by
    unfold sphereAmbientToPairs
    fun_prop
  refine ⟨hm, ?_⟩
  rw [sphereAmbientGaussianLaw, Measure.map_map hm (pairsToSphereAmbient_preserving n h).measurable]
  simp only [Function.comp_def, sphereAmbientToPairs_pairsToSphereAmbient, Measure.map_id']

/-- The literal four-independent-real construction has this same ambient law,
for every choice of the complex Gaussian signs. -/
theorem actualNormalizedPairs_ambient_preserving (n h : ℕ) (hh : 0 < h) (s t : Bool) :
    MeasurePreserving (pairsToSphereAmbient n h ∘ actualNormalizedPairs n h s t)
      (AHHGaussian.fourGaussianLaw n h) (sphereAmbientGaussianLaw n h) :=
  (pairsToSphereAmbient_preserving n h).comp (actualNormalizedPairs_preserving n h hh s t)

/-- The actual angular normalization, applied to the ambient complex blocks. -/
def sphereAmbientDirections (n h : ℕ) [NeZero h] (z : SphereAmbient n h) : Directions n h :=
  gaussianDirections n h (sphereAmbientToPairs n h z)

/-- The ambient Gaussian's angular coordinates have exactly the independent
Haar sphere law used by the ensemble. -/
theorem sphereAmbientDirections_preserving (n h : ℕ) [NeZero h] (hh : 0 < h) :
    MeasurePreserving (sphereAmbientDirections n h) (sphereAmbientGaussianLaw n h)
      (directionsLaw n h) :=
  (gaussianDirections_preserving n h hh).comp (sphereAmbientToPairs_preserving n h)

/-- Direct scaled-standard-Gaussian statement of the ensemble's direction law. -/
theorem scaled_stdGaussian_sphereAmbientDirections (n h : ℕ) [NeZero h] (hh : 0 < h) :
    ((stdGaussian (SphereAmbient n h)).map
      (fun x => (Real.sqrt (2 * (h : ℝ)))⁻¹ • x)).map (sphereAmbientDirections n h) =
      directionsLaw n h := by
  rw [← sphereAmbientGaussianLaw_eq_scaled_stdGaussian n h hh]
  exact (sphereAmbientDirections_preserving n h hh).map_eq

#print axioms map_pi_stdGaussian
#print axioms complex_radialGaussian_eq_scaled_stdGaussian
#print axioms sphereAmbientGaussianLaw_eq_scaled_stdGaussian
#print axioms pairsToSphereAmbient_preserving
#print axioms sphereAmbientToPairs_preserving
#print axioms actualNormalizedPairs_ambient_preserving
#print axioms sphereAmbientDirections_preserving
#print axioms scaled_stdGaussian_sphereAmbientDirections
end AHHRadial
