/-
Rotation P2 + hQQ: orthogonal maps preserve product volume.

Discharge of premise P2 (`piVolume_orthogonal_invariant`) and the right-inverse
identity `hQQ` from `GaussRotation.lean` (conditional rotation invariance of
the standard Gaussian vector law).

Target P2 (paste-full, matching `GaussRotation.piVolume_orthogonal_invariant`):
  `∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ), Qᵀ * Q = 1 →
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).map
      (fun x : Vector d => Q *ᵥ x)
    = Measure.pi fun _ : Fin d => (volume : Measure ℝ)`

Target hQQ: `(Q : Matrix (Fin d) (Fin d) ℝ) → Qᵀ * Q = 1 → Q * Qᵀ = 1`.

Strategy for P2 (isometry route; avoids the missing `IsAddHaarMeasure` instance
for product volume and the missing `LinearMap.det (mulVecLin Q) = Q.det` link):
1. hQQ from `Matrix.nonsing_inv_mul` + `Matrix.inv_eq_right_inv` + `IsUnit det`
   (via `det ^ 2 = 1`, so `det ≠ 0`).
2. The orthogonal map as a linear map on `WithLp 2 (Fin d → ℝ)` (the
   `EuclideanSpace` type in `WithLp` spelling, so all `WithLp` congr lemmas
   match syntactically).
3. It is norm-preserving (`EuclideanSpace.norm_eq` + sum-of-squares
   preservation), hence a `LinearIsometryEquiv` via
   `LinearIsometry.toLinearIsometryEquiv` (needs only equal finranks, `rfl`).
4. Isometries preserve `volume` (`LinearIsometryEquiv.measurePreserving`).
5. Transfer `volume` on `WithLp 2` to `Measure.pi` via
   `PiLp.volume_preserving_ofLp` + `volume_pi`, chaining `Measure.map_map`.

All Mathlib names below were confirmed by `#check` probes against the pinned Mathlib;
PART 1 (hQQ + pi-lemmas) was verified green before the final assembly.
-/
import Mathlib
import GaussianEllipsoid.GaussianProbability

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

/-! ### PART 1: hQQ + pi-type lemmas -/

theorem rotP2_det_sq {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) : Q.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [pow_two]
  exact h

/-- hQQ: a left inverse is a right inverse for real square matrices. -/
theorem rotP2_mul_transpose {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) : Q * Qᵀ = 1 := by
  have h2 := rotP2_det_sq Q hQ
  have hne : Q.det ≠ 0 := by
    intro hz
    rw [hz] at h2
    norm_num at h2
  have hdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hne
  have hdetT : IsUnit (Qᵀ).det := by
    rw [Matrix.det_transpose]
    exact hdet
  have h := Matrix.nonsing_inv_mul Qᵀ hdetT
  rw [Matrix.inv_eq_right_inv hQ] at h
  exact h

theorem rotP2_dotProduct {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (x : Vector d) :
    dotProduct (Q *ᵥ x) (Q *ᵥ x) = dotProduct x x := by
  have hQx : Q *ᵥ x = x ᵥ* Qᵀ := by
    have h := Matrix.mulVec_transpose Qᵀ x
    rw [Matrix.transpose_transpose] at h
    exact h
  rw [Matrix.dotProduct_mulVec, hQx, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

theorem rotP2_sum_sq {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (x : Vector d) :
    ∑ j, ((Q *ᵥ x) j) ^ 2 = ∑ j, (x j) ^ 2 := by
  have e1 : ∀ y : Vector d, (∑ j, (y j) ^ 2) = dotProduct y y := by
    intro y
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e1, e1]
  exact rotP2_dotProduct Q hQ x

theorem rotP2_measurable {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (fun x : Vector d => Q *ᵥ x) := by
  have hmeas : Measurable ⇑(Matrix.mulVecLin Q) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.mulVecLin Q)).measurable
  have heq : ⇑(Matrix.mulVecLin Q) = (fun x : Vector d => Q *ᵥ x) := by
    funext x
    exact Matrix.mulVecLin_apply Q x
  rwa [heq] at hmeas

/-! ### PART 2: the orthogonal map as a linear isometry -/

/-- `EuclideanSpace ℝ (Fin d)` in `WithLp` spelling (syntactic match for all
`WithLp` congr lemmas; defeq to `EuclideanSpace` for the norm lemmas). -/
abbrev rotP2_E (d : ℕ) := WithLp 2 (Fin d → ℝ)

/-- The orthogonal map as a linear map on `WithLp 2` space. -/
def rotP2_linMap (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    rotP2_E d →ₗ[ℝ] rotP2_E d where
  toFun y := WithLp.toLp 2 (Q *ᵥ y.ofLp)
  map_add' := by
    intro x y
    show WithLp.toLp 2 (Q *ᵥ (x + y).ofLp)
      = WithLp.toLp 2 (Q *ᵥ x.ofLp) + WithLp.toLp 2 (Q *ᵥ y.ofLp)
    rw [WithLp.ofLp_add 2 x y, Matrix.mulVec_add Q _ _,
      WithLp.toLp_add 2 _ _]
  map_smul' := by
    intro c x
    show WithLp.toLp 2 (Q *ᵥ (c • x).ofLp)
      = c • WithLp.toLp 2 (Q *ᵥ x.ofLp)
    rw [WithLp.ofLp_smul 2 c x, Matrix.mulVec_smul Q c _,
      WithLp.toLp_smul 2 c _]

theorem rotP2_linMap_apply (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (y : rotP2_E d) :
    (rotP2_linMap d Q) y = WithLp.toLp 2 (Q *ᵥ y.ofLp) := rfl

/-- Orthogonal maps preserve the `EuclideanSpace` norm. -/
theorem rotP2_norm (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (y : rotP2_E d) :
    ‖(rotP2_linMap d Q) y‖ = ‖y‖ := by
  have hofLp : ((rotP2_linMap d Q) y).ofLp = Q *ᵥ y.ofLp := by
    rw [rotP2_linMap_apply d Q y, WithLp.ofLp_toLp 2 _]
  have e1 : ‖(rotP2_linMap d Q) y‖
      = √(∑ i, ‖((rotP2_linMap d Q) y).ofLp i‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have e2 : ‖y‖ = √(∑ i, ‖y.ofLp i‖ ^ 2) := EuclideanSpace.norm_eq _
  rw [e1, e2]
  congr 1
  rw [hofLp]
  have hsum := rotP2_sum_sq Q hQ (y.ofLp)
  simp only [Real.norm_eq_abs, sq_abs]
  exact hsum

/-- The orthogonal map as a linear isometry equiv (needs only equal finranks). -/
def rotP2_iso (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) : rotP2_E d ≃ₗᵢ[ℝ] rotP2_E d :=
  LinearIsometry.toLinearIsometryEquiv
    (LinearIsometry.mk (rotP2_linMap d Q) (rotP2_norm d Q hQ)) rfl

theorem rotP2_iso_apply (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) (y : rotP2_E d) :
    (rotP2_iso d Q hQ) y = (rotP2_linMap d Q) y :=
  LinearIsometry.toLinearIsometryEquiv_apply _ _ _

/-- The pi-type map is the isometry conjugated by `ofLp`/`toLp`. -/
theorem rotP2_congr (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) :
    (fun x : Vector d => Q *ᵥ x) ∘ WithLp.ofLp
      = WithLp.ofLp ∘ ⇑(rotP2_iso d Q hQ) := by
  funext y
  show Q *ᵥ y.ofLp = ((rotP2_iso d Q hQ) y).ofLp
  rw [rotP2_iso_apply d Q hQ y, rotP2_linMap_apply d Q y,
    WithLp.ofLp_toLp 2 _]

/-! ### PART 3: P2 (paste-full) -/

/-- (P2, paste-full) Orthogonal maps preserve product volume:
`GaussRotation.piVolume_orthogonal_invariant`, i.e.
`∀ (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ), Qᵀ * Q = 1 →
  (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).map
    (fun x : Vector d => Q *ᵥ x)
  = Measure.pi fun _ : Fin d => (volume : Measure ℝ)`. -/
theorem rotP2_piVolume (d : ℕ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Qᵀ * Q = 1) :
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).map
        (fun x : Vector d => Q *ᵥ x)
      = Measure.pi fun _ : Fin d => (volume : Measure ℝ) := by
  have heMP : MeasurePreserving ⇑(rotP2_iso d Q hQ) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have hE : (volume : Measure (rotP2_E d)).map ⇑(rotP2_iso d Q hQ)
      = volume :=
    heMP.map_eq
  have hψMP : MeasurePreserving (WithLp.ofLp : rotP2_E d → Vector d)
      volume volume :=
    PiLp.volume_preserving_ofLp (Fin d)
  have hpi : (volume : Measure (Vector d))
      = Measure.pi fun _ : Fin d => (volume : Measure ℝ) := volume_pi
  have hψ : (volume : Measure (rotP2_E d)).map WithLp.ofLp
      = Measure.pi fun _ : Fin d => (volume : Measure ℝ) := by
    have h := hψMP.map_eq
    rw [hpi] at h
    exact h
  have hFmeas : Measurable (fun x : Vector d => Q *ᵥ x) :=
    rotP2_measurable Q
  have hψmeas : Measurable (WithLp.ofLp : rotP2_E d → Vector d) :=
    hψMP.measurable
  have hemeas : Measurable ⇑(rotP2_iso d Q hQ) := heMP.measurable
  calc (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).map
          (fun x : Vector d => Q *ᵥ x)
        = ((volume : Measure (rotP2_E d)).map WithLp.ofLp).map
            (fun x : Vector d => Q *ᵥ x) := by rw [hψ]
      _ = (volume : Measure (rotP2_E d)).map
            ((fun x : Vector d => Q *ᵥ x) ∘ WithLp.ofLp) :=
          Measure.map_map hFmeas hψmeas
      _ = (volume : Measure (rotP2_E d)).map
            (WithLp.ofLp ∘ ⇑(rotP2_iso d Q hQ)) := by
          rw [rotP2_congr d Q hQ]
      _ = ((volume : Measure (rotP2_E d)).map
            ⇑(rotP2_iso d Q hQ)).map WithLp.ofLp :=
          (Measure.map_map hψmeas hemeas).symm
      _ = (volume : Measure (rotP2_E d)).map WithLp.ofLp := by rw [hE]
      _ = Measure.pi fun _ : Fin d => (volume : Measure ℝ) := hψ

end GaussianEllipsoid
