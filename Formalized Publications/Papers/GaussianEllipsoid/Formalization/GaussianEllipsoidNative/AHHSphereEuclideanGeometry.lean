import AHHSphereRootLipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Faithful product-Euclidean realization of the actual sphere directions. -/
noncomputable section
open GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators
namespace AHHRadial

/-- Ambient Hilbert space with one complex block for each sample and each factor. -/
abbrev SphereAmbient (n h : ℕ) := PiLp 2 (fun _ : Fin n × Bool => CE h)

/-- The product of unit spheres, with the inherited Euclidean product metric. -/
abbrev EuclideanDirections (n h : ℕ) :=
  {z : SphereAmbient n h // ∀ j, ‖z j‖ = 1}

/-- Recover the original directions, without changing any complex coordinate. -/
def euclideanToDirections (n h : ℕ) (z : EuclideanDirections n h) : Directions n h :=
  fun i =>
    (⟨z.val (i, false), by simpa only [Metric.mem_sphere, dist_zero_right] using z.property (i, false)⟩,
     ⟨z.val (i, true), by simpa only [Metric.mem_sphere, dist_zero_right] using z.property (i, true)⟩)

/-- Embed the original directions into their Euclidean product realization. -/
def directionsToEuclidean (n h : ℕ) (d : Directions n h) : EuclideanDirections n h :=
  ⟨WithLp.toLp 2 (fun j => if j.2 then ((d j.1).2 : CE h) else ((d j.1).1 : CE h)), by
    rintro ⟨i, b⟩
    cases b
    · change ‖((d i).1 : CE h)‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using (d i).1.property
    · change ‖((d i).2 : CE h)‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using (d i).2.property⟩

@[simp] theorem euclideanToDirections_directionsToEuclidean (n h : ℕ) (d : Directions n h) :
    euclideanToDirections n h (directionsToEuclidean n h d) = d := by
  funext i
  apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp] theorem directionsToEuclidean_euclideanToDirections (n h : ℕ)
    (z : EuclideanDirections n h) :
    directionsToEuclidean n h (euclideanToDirections n h z) = z := by
  apply Subtype.ext
  ext ⟨i, b⟩
  cases b <;> rfl

theorem euclideanDirections_dist_sq (n h : ℕ) (z w : EuclideanDirections n h) :
    dist z w ^ 2 = ∑ i,
      (‖((euclideanToDirections n h z i).1 : CE h) -
        ((euclideanToDirections n h w i).1 : CE h)‖ ^ 2 +
       ‖((euclideanToDirections n h z i).2 : CE h) -
        ((euclideanToDirections n h w i).2 : CE h)‖ ^ 2) := by
  change dist z.val w.val ^ 2 = _
  rw [PiLp.dist_sq_eq_of_L2, Fintype.sum_prod_type]
  simp [dist_eq_norm, euclideanToDirections, add_comm]

/-- Exact constant one, with the Euclidean product metric and the actual observable. -/
theorem lipschitzWith_sqrt_unitCovarianceNorm_euclidean (n h : ℕ) :
    LipschitzWith 1 (fun z : EuclideanDirections n h =>
      Real.sqrt (unitCovarianceNorm n h (euclideanToDirections n h z))) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mp
  rw [sq_abs, euclideanDirections_dist_sq]
  exact unitCovarianceNorm_sqrt_sq_sub_le n h _ _

#print axioms euclideanToDirections_directionsToEuclidean
#print axioms directionsToEuclidean_euclideanToDirections
#print axioms lipschitzWith_sqrt_unitCovarianceNorm_euclidean
end AHHRadial
