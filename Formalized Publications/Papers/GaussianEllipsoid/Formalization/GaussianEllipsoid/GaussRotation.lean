/-
Rotation invariance of the standard Gaussian vector law (conditional proof).

Target (exact statement):
  `gaussianVectorLaw_rotation : ∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ),
    Qᵀ * Q = 1 → (gaussianVectorLaw d).map (fun x => Q *ᵥ x)
      = gaussianVectorLaw d`

Status: proved conditional on three explicit premises (ExternalInputs style:
each a `Prop`, never an axiom) plus the right-inverse identity `Q * Qᵀ = 1`
(which follows from `Qᵀ * Q = 1`; the Mathlib name `Matrix.nonsing_inv_mul`
is unverified). The premises isolate exact Mathlib gaps (probe-verified):
- `gaussianVectorLaw_density` (P1): `Measure.pi` of `withDensity` equals
  `withDensity` of `Measure.pi` with the product density. No `Measure.pi` +
  `withDensity` interchange exists in Mathlib (`pi_withDensity`,
  `withDensity_pi`, `withDensity_prod`, `prod_withDensity`, `lintegral_pi`,
  `pi_finSucc` all missing).
- `piVolume_orthogonal_invariant` (P2): orthogonal maps preserve product
  volume. `addHaar_image/preimage_linearMap` exist, but the determinant link
  (`LinearMap.det` of `Matrix.mulVecLin`) and the `IsAddHaarMeasure`
  instance for product volume are missing.
- `measure_eq_of_lintegral_eq` (P3): measures agreeing on all lintegrals are
  equal (`ext_of_forall_lintegral_eq` missing; true in general via
  indicators).

Proved unconditionally: orthogonal norm preservation
(`dotProduct_mulVec_self_of_transpose_mul_self_eq_one`,
`sum_sq_mulVec_of_transpose_mul_self_eq_one`), `|det Q| = 1`
(`det_sq_of_transpose_mul_self_eq_one`,
`abs_det_of_transpose_mul_self_eq_one`), the joint Gaussian density in closed
radial form plus its invariance (`gaussianPDFReal_zero_one`,
`gaussianPDF_zero_one`, `jointDensity_eq`, `jointDensity_invariant`),
measurability of matrix-vector maps (`measurable_mulVec`), and the full
change-of-variables lintegral chain
(`gaussianVectorLaw_lintegral_agreement`).

Mathematical source: rotation invariance of N(0, I_d); unblocks DS per-center
tails, Huber-width inputs, and M9 once P1–P3 (+ right inverse) are discharged.
-/
import Mathlib
import GaussianEllipsoid.GaussianProbability

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

/-! ### Linear algebra helpers (unconditional) -/

/-- Orthogonal maps preserve `dotProduct` against itself. -/
theorem dotProduct_mulVec_self_of_transpose_mul_self_eq_one {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) (x : Vector d) :
    dotProduct (Q *ᵥ x) (Q *ᵥ x) = dotProduct x x := by
  have hQx : Q *ᵥ x = x ᵥ* Qᵀ := by
    have h := Matrix.mulVec_transpose Qᵀ x
    rw [Matrix.transpose_transpose] at h
    exact h
  rw [Matrix.dotProduct_mulVec, hQx, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

/-- A real matrix with `Qᵀ * Q = 1` has squared determinant `1`. -/
theorem det_sq_of_transpose_mul_self_eq_one {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) : Q.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [pow_two]
  exact h

/-- A real matrix with `Qᵀ * Q = 1` has determinant of absolute value `1`. -/
theorem abs_det_of_transpose_mul_self_eq_one {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) : |Q.det| = 1 := by
  have h2 := det_sq_of_transpose_mul_self_eq_one Q hQ
  rcases sq_eq_one_iff.mp h2 with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- Orthogonal maps preserve the sum of squares. -/
theorem sum_sq_mulVec_of_transpose_mul_self_eq_one {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) (x : Vector d) :
    ∑ j, ((Q *ᵥ x) j) ^ 2 = ∑ j, (x j) ^ 2 := by
  have e1 : ∀ y : Vector d, (∑ j, (y j) ^ 2) = dotProduct y y := by
    intro y
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e1, e1]
  exact dotProduct_mulVec_self_of_transpose_mul_self_eq_one Q hQ x

/-! ### Joint density in closed form (unconditional) -/

/-- The standard Gaussian density in closed form. -/
theorem gaussianPDFReal_zero_one (z : ℝ) :
    gaussianPDFReal 0 1 z
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]

/-- The standard Gaussian density as an `ENNReal` in closed form. -/
theorem gaussianPDF_zero_one (z : ℝ) :
    gaussianPDF 0 1 z
      = ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2)) := by
  unfold gaussianPDF
  rw [gaussianPDFReal_zero_one]

/-- Joint density of the Gaussian vector law in closed radial form. -/
theorem jointDensity_eq {d : ℕ} (x : Vector d) :
    (∏ j, gaussianPDF 0 1 (x j))
      = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ d
        * Real.exp (-(∑ j, (x j) ^ 2) / 2)) := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((x j) ^ 2) / 2) := by
    intro j _
    positivity
  simp only [gaussianPDF_zero_one]
  have hprod : (∏ j, ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((x j) ^ 2) / 2)))
      = ENNReal.ofReal (∏ j,
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((x j) ^ 2) / 2)) :=
    (ENNReal.ofReal_prod_of_nonneg hnn).symm
  rw [hprod]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  have h1 : (∑ j : Fin d, (-((x j) ^ 2) / 2))
      = ∑ j : Fin d, ((-1 / 2) * (x j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, ← Finset.mul_sum]
  ring

/-- The joint Gaussian density is invariant under orthogonal maps. -/
theorem jointDensity_invariant {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (x : Vector d) :
    (∏ j, gaussianPDF 0 1 ((Q *ᵥ x) j)) = ∏ j, gaussianPDF 0 1 (x j) := by
  rw [jointDensity_eq, jointDensity_eq,
    sum_sq_mulVec_of_transpose_mul_self_eq_one Q hQ x]

/-! ### Measurability (unconditional) -/

/-- Matrix-vector maps are measurable (via continuity of `mulVecLin`;
avoids unfolding `Matrix.mulVec`, whose equation lemma `simp only` could not
use). -/
theorem measurable_mulVec {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun x : Vector d => Q *ᵥ x) := by
  have hmeas : Measurable ⇑(Matrix.mulVecLin Q) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin Q)).measurable
  have heq : ⇑(Matrix.mulVecLin Q) = (fun x : Vector d => Q *ᵥ x) := by
    funext x
    exact Matrix.mulVecLin_apply Q x
  rwa [heq] at hmeas

/-! ### Explicit premises (ExternalInputs style) -/

/-- (P1) Joint-density premise: the Gaussian vector law is product volume
with the product density. The general `Measure.pi` + `withDensity`
interchange is missing in Mathlib. -/
def gaussianVectorLaw_density : Prop :=
  ∀ d : ℕ, gaussianVectorLaw d
    = (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).withDensity
      fun x => ∏ j, gaussianPDF 0 1 (x j)

/-- (P2) Volume-preservation premise: orthogonal maps preserve product
volume. Needs `LinearMap.det` of `Matrix.mulVecLin` and the
`IsAddHaarMeasure` instance for product volume. -/
def piVolume_orthogonal_invariant : Prop :=
  ∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ), Qᵀ * Q = 1 →
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).map
      (fun x : Vector d => Q *ᵥ x)
    = Measure.pi fun _ : Fin d => (volume : Measure ℝ)

/-- (P3) Lintegral-extensionality premise: measures agreeing on all
lintegrals are equal (true in general via indicators; missing in Mathlib). -/
def measure_eq_of_lintegral_eq : Prop :=
  ∀ {α : Type 0} [MeasurableSpace α] (μ ν : Measure α),
    (∀ g : α → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = ∫⁻ x, g x ∂ν) → μ = ν

/-! ### Main results (conditional) -/

/-- Lintegral agreement between the rotated law and the original law
(the change-of-variables chain). -/
theorem gaussianVectorLaw_lintegral_agreement (d : ℕ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ * Q = 1) (hQQ : Q * Qᵀ = 1)
    (p1 : gaussianVectorLaw_density) (p2 : piVolume_orthogonal_invariant) :
    ∀ g : (Vector d) → ℝ≥0∞, Measurable g →
      (∫⁻ y, g y ∂((gaussianVectorLaw d).map fun x => Q *ᵥ x))
        = ∫⁻ y, g y ∂(gaussianVectorLaw d) := by
  intro g hg
  set base : Measure (Vector d) :=
    Measure.pi fun _ : Fin d => (volume : Measure ℝ)
  set p : (Vector d) → ℝ≥0∞ := fun x => ∏ j, gaussianPDF 0 1 (x j) with hp
  have hdens : gaussianVectorLaw d = base.withDensity p := p1 d
  have hvol : base.map (fun x : Vector d => Q *ᵥ x) = base := p2 d Q hQ
  have hQTQ : (Qᵀ)ᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact hQQ
  have hQmeas : Measurable (fun x : Vector d => Q *ᵥ x) := measurable_mulVec Q
  have hQTmeas : Measurable (fun x : Vector d => Qᵀ *ᵥ x) :=
    measurable_mulVec Qᵀ
  have hPDFmeas : Measurable (gaussianPDF (0 : ℝ) (1 : ℝ≥0)) := by
    have hcomp : gaussianPDF 0 1
        = ENNReal.ofReal ∘ gaussianPDFReal 0 1 := rfl
    rw [hcomp]
    exact ENNReal.continuous_ofReal.measurable.comp
      (measurable_gaussianPDFReal 0 1)
  have hpmeas : Measurable p := by
    rw [hp]
    exact Finset.measurable_prod _ fun j _ =>
      hPDFmeas.comp (measurable_pi_apply j)
  have hinv_p : ∀ y, p (Qᵀ *ᵥ y) = p y := by
    intro y
    rw [hp]
    show (∏ j, gaussianPDF 0 1 ((Qᵀ *ᵥ y) j))
      = ∏ j, gaussianPDF 0 1 (y j)
    exact jointDensity_invariant Qᵀ hQTQ y
  have hgc : Measurable (fun x => g (Q *ᵥ x)) := hg.comp hQmeas
  have step1 : (∫⁻ y, g y ∂((gaussianVectorLaw d).map fun x => Q *ᵥ x))
      = ∫⁻ x, g (Q *ᵥ x) ∂(gaussianVectorLaw d) :=
    lintegral_map hg hQmeas
  rw [step1, hdens]
  have step2 : (∫⁻ x, g (Q *ᵥ x) ∂(base.withDensity p))
      = ∫⁻ x, p x * g (Q *ᵥ x) ∂base :=
    lintegral_withDensity_eq_lintegral_mul base hpmeas hgc
  rw [step2]
  set F : (Vector d) → ℝ≥0∞ := fun y => p (Qᵀ *ᵥ y) * g y with hF
  have hFmeas : Measurable F := (hpmeas.comp hQTmeas).mul hg
  have hFQ : ∀ x, F (Q *ᵥ x) = p x * g (Q *ᵥ x) := by
    intro x
    show p (Qᵀ *ᵥ (Q *ᵥ x)) * g (Q *ᵥ x) = p x * g (Q *ᵥ x)
    have hQx : Qᵀ *ᵥ (Q *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    rw [hQx]
  have step34 : (∫⁻ x, p x * g (Q *ᵥ x) ∂base)
      = ∫⁻ y, F y ∂(base.map fun x => Q *ᵥ x) := by
    have hcongr : (∫⁻ x, p x * g (Q *ᵥ x) ∂base)
        = ∫⁻ x, F (Q *ᵥ x) ∂base :=
      lintegral_congr_ae (Filter.Eventually.of_forall (fun x => (hFQ x).symm))
    rw [hcongr]
    exact (lintegral_map hFmeas hQmeas).symm
  rw [step34, hvol]
  have hFinv : ∀ y, F y = p y * g y := by
    intro y
    show p (Qᵀ *ᵥ y) * g y = p y * g y
    rw [hinv_p]
  have hcongr2 : (∫⁻ y, F y ∂base) = ∫⁻ y, p y * g y ∂base :=
    lintegral_congr_ae (Filter.Eventually.of_forall hFinv)
  rw [hcongr2]
  have step7 : (∫⁻ y, p y * g y ∂base)
      = ∫⁻ y, g y ∂(base.withDensity p) :=
    (lintegral_withDensity_eq_lintegral_mul base hpmeas hg).symm
  rw [step7]

/-- Rotation invariance of the standard Gaussian vector law, conditional on
P1 (joint density), P2 (volume preservation), P3 (lintegral extensionality),
and the right-inverse identity `Q * Qᵀ = 1`. -/
theorem gaussianVectorLaw_rotation (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (hQQ : Q * Qᵀ = 1)
    (p1 : gaussianVectorLaw_density) (p2 : piVolume_orthogonal_invariant)
    (p3 : measure_eq_of_lintegral_eq) :
    (gaussianVectorLaw d).map (fun x => Q *ᵥ x) = gaussianVectorLaw d :=
  p3 _ _ (gaussianVectorLaw_lintegral_agreement d Q hQ hQQ p1 p2)

end GaussianEllipsoid
