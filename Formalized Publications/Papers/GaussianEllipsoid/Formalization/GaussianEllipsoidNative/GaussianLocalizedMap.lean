import GaussianBilinearSmallBall
import HomogeneousLocalization

noncomputable section
open GaussianEllipsoid GaussianEllipsoid.SmallBall
open scoped BigOperators

namespace GaussianEllipsoid.Localized

@[simp] theorem toMatrix_add {r q : ℕ} (A B : FrobeniusMatrix r q) (i : Fin r) (j : Fin q) :
    frobeniusToMatrix (A+B) i j = frobeniusToMatrix A i j + frobeniusToMatrix B i j := rfl

@[simp] theorem toMatrix_smul {r q : ℕ} (c : ℝ) (A : FrobeniusMatrix r q) (i : Fin r) (j : Fin q) :
    frobeniusToMatrix (c • A) i j = c * frobeniusToMatrix A i j := rfl

/-- The actual Gaussian observation is linear in its coefficient vector. -/
def bilinearCoefficientMap (r n : ℕ) (p : BilinearSample r n) :
    Coeff n →ₗ[ℝ] FrobeniusMatrix r r where
  toFun z := bilinearFrobenius r n z p
  map_add' u v := by
    apply (frobeniusEquivEuclidean r r).injective
    ext ab
    obtain ⟨a,b⟩ := ab
    simp only [map_add, PiLp.add_apply, frobeniusEquivEuclidean_apply,
      toMatrix_add, bilinearFrobenius_entry]
    simp only [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c u := by
    apply (frobeniusEquivEuclidean r r).injective
    ext ab
    obtain ⟨a,b⟩ := ab
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, frobeniusEquivEuclidean_apply,
      toMatrix_smul, bilinearFrobenius_entry, RingHom.id_apply]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring

/-- The d-scaled off-diagonal Gaussian coefficient operator, with exact
coordinate normalization d^(-1/2). -/
def localizedOperator (d : ℝ) (r n : ℕ) (p : BilinearSample r n) :
    Coeff n →ₗ[ℝ] FrobeniusMatrix r r :=
  (Real.sqrt (r:ℝ)/Real.sqrt d) • bilinearCoefficientMap r n p

@[simp] theorem localizedOperator_apply (d : ℝ) (r n : ℕ)
    (p : BilinearSample r n) (z : Coeff n) :
    localizedOperator d r n p z =
      (Real.sqrt (r:ℝ)/Real.sqrt d) • bilinearFrobenius r n z p := rfl

/-- Exact entry formula, rather than an unproved identification with the paper. -/
theorem localizedOperator_entry (d : ℝ) (r n : ℕ) (hr : 0 < r)
    (p : BilinearSample r n) (z : Coeff n) (a b : Fin r) :
    frobeniusToMatrix (localizedOperator d r n p z) a b =
      (Real.sqrt d)⁻¹ * ∑ i, z i * p.1 i a * p.2 (i,b) := by
  change (Real.sqrt (r:ℝ)/Real.sqrt d) *
    frobeniusToMatrix (bilinearFrobenius r n z p) a b = _
  rw [bilinearFrobenius_entry]
  have hs : Real.sqrt (r:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr))
  simp only [div_eq_mul_inv]
  calc
    _ = ((Real.sqrt (r:ℝ)) * (Real.sqrt (r:ℝ))⁻¹) * ((Real.sqrt d)⁻¹ * ∑ i, z i * p.1 i a * p.2 (i,b)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.localizedOperator_entry
