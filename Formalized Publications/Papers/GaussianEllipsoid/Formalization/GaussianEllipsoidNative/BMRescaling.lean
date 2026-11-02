import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Deterministic r = 1 part of Bandeira--Maillard Lemma 2.6

Source: https://arxiv.org/html/2310.05787v2, Section 2.4, Lemma 2.6.
The matrices, PSD constraints, rank-one observations, and residuals below
are concrete. No norm bound or positivity conclusion is assumed.
-/
noncomputable section
open scoped BigOperators Matrix

namespace BMRescaling

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev Vector (d : ℕ) := Fin d → ℝ

/-- The actual Loewner spectral box, matching the supplied interface. -/
def spectralBox (d : ℕ) (lo hi : ℝ) : Set (Square d) :=
  {S | (S - lo • (1 : Square d)).PosSemidef ∧
    (hi • (1 : Square d) - S).PosSemidef}

/-- Coordinate quadratic form. -/
def quadratic {d : ℕ} (S : Square d) (x : Vector d) : ℝ :=
  dotProduct x (S *ᵥ x)

/-- The centered rank-one observation used by BM. -/
def centeredObservation {d : ℕ} (x : Vector d) : Square d :=
  (Real.sqrt (d : ℝ))⁻¹ • (Matrix.vecMulVec x x - 1)

/-- BM's residual before its deterministic trace normalization. -/
def centeredResidual {d : ℕ} (S : Square d) (x : Vector d) : ℝ :=
  Matrix.trace (centeredObservation x * S) - 1

/-- The fitting residual in the supplied below-threshold interface. -/
def fittingResidual {d : ℕ} (S : Square d) (x : Vector d) : ℝ :=
  (quadratic S x - (d : ℝ)) / Real.sqrt (d : ℝ)

/-- BM's positive scaling factor. -/
def scale {d : ℕ} (S : Square d) : ℝ :=
  (d : ℝ) / (Matrix.trace S + Real.sqrt (d : ℝ))

/-- The actual matrix produced by Lemma 2.6. -/
def rescale {d : ℕ} (S : Square d) : Square d := scale S • S

/-- Nonnegative scalar multiplication preserves actual positive semidefiniteness. -/
theorem posSemidef_smul {d : ℕ} {S : Square d} (hS : S.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • S).PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  exact hS.smul hc

/-- The diagonal of a PSD matrix is nonnegative, proved by coordinate testing. -/
theorem diagonal_nonneg {d : ℕ} {S : Square d} (hS : S.PosSemidef)
    (i : Fin d) : 0 ≤ S i i := by
  exact hS.diag_nonneg

/-- Spectral constraints imply diagonal constraints without an extra hypothesis. -/
theorem box_diagonal_bounds {d : ℕ} {lo hi : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (i : Fin d) : lo ≤ S i i ∧ S i i ≤ hi := by
  have h₁ := diagonal_nonneg hS.1 i
  have h₂ := diagonal_nonneg hS.2 i
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h₁ h₂
  constructor <;> linarith

/-- The trace is trapped between dimension times the spectral endpoints. -/
theorem box_trace_bounds {d : ℕ} {lo hi : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    (d : ℝ) * lo ≤ Matrix.trace S ∧ Matrix.trace S ≤ (d : ℝ) * hi := by
  constructor
  · calc (d : ℝ) * lo = ∑ _i : Fin d, lo := by simp
         _ ≤ Matrix.trace S := Finset.sum_le_sum fun i _ => (box_diagonal_bounds hS i).1
  · calc Matrix.trace S ≤ ∑ _i : Fin d, hi :=
           Finset.sum_le_sum fun i _ => (box_diagonal_bounds hS i).2
         _ = (d : ℝ) * hi := by simp

/-- Every matrix in a box with nonnegative lower endpoint is PSD. -/
theorem box_posSemidef {d : ℕ} {lo hi : ℝ} {S : Square d}
    (hlo : 0 ≤ lo) (hS : S ∈ spectralBox d lo hi) : S.PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  have h := hS.1.add (posSemidef_smul (Matrix.PosSemidef.one :
    (1 : Square d).PosSemidef) hlo)
  simpa only [sub_add_cancel] using h

/-- Enlargement of the spectral interval follows from PSD arithmetic. -/
theorem box_mono {d : ℕ} {lo hi lo' hi' : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    S ∈ spectralBox d lo' hi' := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  have h₁ := hS.1.add (posSemidef_smul (Matrix.PosSemidef.one :
    (1 : Square d).PosSemidef) (sub_nonneg.mpr hlo))
  have h₂ := hS.2.add (posSemidef_smul (Matrix.PosSemidef.one :
    (1 : Square d).PosSemidef) (sub_nonneg.mpr hhi))
  constructor
  · convert h₁ using 1 <;> module
  · convert h₂ using 1 <;> module

/-- Nonnegative scaling sends the box to its correspondingly scaled box. -/
theorem box_smul {d : ℕ} {lo hi c : ℝ} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (hc : 0 ≤ c) :
    c • S ∈ spectralBox d (c * lo) (c * hi) := by
  constructor
  · convert posSemidef_smul hS.1 hc using 1 <;> module
  · convert posSemidef_smul hS.2 hc using 1 <;> module

/-- The normalization denominator is strictly positive in positive dimension. -/
theorem denominator_pos {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hS : S ∈ spectralBox d lo hi) :
    0 < Matrix.trace S + Real.sqrt (d : ℝ) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have htrace := (box_trace_bounds hS).1
  have hroot := Real.sqrt_nonneg (d : ℝ)
  have hprod := mul_pos hd' hlo
  linarith

/-- The scaling factor is strictly positive. -/
theorem scale_pos {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hS : S ∈ spectralBox d lo hi) : 0 < scale S :=
  div_pos (Nat.cast_pos.mpr hd) (denominator_pos hd hlo hS)

/-- Dimension-independent scalar bounds, valid already for every d ≥ 1. -/
theorem scale_bounds {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hS : S ∈ spectralBox d lo hi) :
    1 / (hi + 1) ≤ scale S ∧ scale S ≤ 1 / lo := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hsqrt : Real.sqrt (d : ℝ) ≤ d := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have hden := denominator_pos hd hlo hS
  have htr := box_trace_bounds hS
  constructor
  · rw [scale, div_le_div_iff₀ (by positivity : 0 < hi + 1) hden]
    nlinarith
  · rw [scale, div_le_div_iff₀ hden hlo]
    nlinarith [Real.sqrt_nonneg (d : ℝ)]

/-- A single positive interval works in all positive dimensions and sample sizes. -/
theorem rescale_mem_fixed_box {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hS : S ∈ spectralBox d lo hi) :
    rescale S ∈ spectralBox d (lo / (hi + 1)) (hi / lo) := by
  have hc := scale_bounds hd hlo hlohi hS
  apply box_mono (box_smul hS (scale_pos hd hlo hS).le)
  · have h := mul_le_mul_of_nonneg_right hc.1 hlo.le
    simpa [rescale, div_eq_mul_inv, mul_comm, mul_left_comm] using h
  · have h := mul_le_mul_of_nonneg_right hc.2 (hlo.le.trans hlohi)
    simpa [rescale, div_eq_mul_inv, mul_comm, mul_left_comm] using h

/-- The chosen fixed endpoints are positive and in the correct order. -/
theorem fixed_endpoints {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    0 < lo / (hi + 1) ∧ lo / (hi + 1) ≤ hi / lo := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity : 0 < hi + 1) hlo]
    nlinarith [mul_self_le_mul_self hlo.le hlohi]

/-- Trace of the actual rank-one product is the coordinate quadratic form. -/
theorem trace_rankOne_mul {d : ℕ} (S : Square d) (x : Vector d) :
    Matrix.trace (Matrix.vecMulVec x x * S) = quadratic S x := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec,
    quadratic, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (x j * x i) * S i j = x i * (S i j * x j)
  ring

/-- Centered observation residual in direct quadratic/trace coordinates. -/
theorem centeredResidual_eq {d : ℕ} (S : Square d) (x : Vector d) :
    centeredResidual S x =
      (quadratic S x - Matrix.trace S) / Real.sqrt (d : ℝ) - 1 := by
  simp only [centeredResidual, centeredObservation, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_sub, trace_rankOne_mul, smul_eq_mul]
  ring

@[simp] theorem quadratic_smul {d : ℕ} (S : Square d) (x : Vector d) (c : ℝ) :
    quadratic (c • S) x = c * quadratic S x := by
  simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Equality of the interface residual with BM's displayed sqrt(d) formula. -/
theorem fittingResidual_eq_sqrt_mul {d : ℕ} (hd : 0 < d) (S : Square d) (x : Vector d) :
    fittingResidual S x = Real.sqrt (d : ℝ) * (quadratic S x / (d : ℝ) - 1) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hs : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  unfold fittingResidual
  field_simp
  nlinarith [congrArg (fun a : ℝ => (quadratic S x - (d : ℝ)) * a) hs2]

/-- Exact BM Lemma 2.6 residual identity. -/
theorem fittingResidual_rescale {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hS : S ∈ spectralBox d lo hi) (x : Vector d) :
    fittingResidual (rescale S) x = scale S * centeredResidual S x := by
  have hden := ne_of_gt (denominator_pos hd hlo hS)
  have hs : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
  rw [fittingResidual, rescale, quadratic_smul, centeredResidual_eq]
  unfold scale
  field_simp
  ring

/-- Exact identity with the residual as displayed in BM. -/
theorem sqrt_mul_rescale {d : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hS : S ∈ spectralBox d lo hi) (x : Vector d) :
    Real.sqrt (d : ℝ) * (quadratic (rescale S) x / (d : ℝ) - 1) =
      scale S * (Matrix.trace (centeredObservation x * S) - 1) := by
  rw [← fittingResidual_eq_sqrt_mul hd]
  exact fittingResidual_rescale hd hlo hS x

/-- Finite empirical L1 risk, including the harmless n = 0 convention. -/
def empiricalL1 {n : ℕ} (r : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, |r i|

/-- The finite empirical L1 risks obey the same exact scaling relation. -/
theorem empiricalL1_rescale {d n : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hS : S ∈ spectralBox d lo hi) (x : Fin n → Vector d) :
    empiricalL1 (fun i => fittingResidual (rescale S) (x i)) =
      scale S * empiricalL1 (fun i => centeredResidual S (x i)) := by
  unfold empiricalL1
  simp_rw [fittingResidual_rescale hd hlo hS, abs_mul, abs_of_pos (scale_pos hd hlo hS)]
  rw [← Finset.mul_sum]
  ring

/-- The actual finite empirical r = 1 risk bound used after universality. -/
theorem empiricalL1_rescale_le {d n : ℕ} (hd : 0 < d) {lo hi : ℝ} {S : Square d}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hS : S ∈ spectralBox d lo hi)
    (x : Fin n → Vector d) :
    empiricalL1 (fun i => fittingResidual (rescale S) (x i)) ≤
      empiricalL1 (fun i => centeredResidual S (x i)) / lo := by
  rw [empiricalL1_rescale hd hlo hS]
  have hr : 0 ≤ empiricalL1 (fun i => centeredResidual S (x i)) := by
    unfold empiricalL1
    positivity
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right (scale_bounds hd hlo hlohi hS).2 hr

/-- Integration-ready deterministic implication from BM's centered fit to the
original fitting problem, with a fixed interval independent of d and n. -/
theorem exists_fitting_of_centered {d n : ℕ} (hd : 0 < d) {lo hi ε : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (x : Fin n → Vector d)
    (hfit : ∃ S ∈ spectralBox d lo hi,
      empiricalL1 (fun i => centeredResidual S (x i)) ≤ ε) :
    ∃ T ∈ spectralBox d (lo / (hi + 1)) (hi / lo),
      empiricalL1 (fun i => fittingResidual T (x i)) ≤ ε / lo := by
  obtain ⟨S, hS, hrisk⟩ := hfit
  refine ⟨rescale S, rescale_mem_fixed_box hd hlo hlohi hS, ?_⟩
  exact (empiricalL1_rescale_le hd hlo hlohi hS x).trans
    (div_le_div_of_nonneg_right hrisk hlo.le)

end BMRescaling
