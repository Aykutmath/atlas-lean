import PaperAutomaticDerivativeSlices
import PaperSymmetricBasis
import PaperAffineSecondStein
import CanonicalSymGaussian

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory GaussianTensorMoments BMQuadraticStein BMSmoothQuadraticComposition
open PaperAutomaticDerivativeSlices PaperSymmetricDirections PaperSymmetricBasis
open PaperCavityThird PaperAffineSecondStein PaperNormalizedSecondStein
open GaussianEllipsoid GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.UCUniformContinuity
open scoped BigOperators InnerProductSpace ContDiff BoundedContinuousFunction
namespace GaussianEllipsoid.PaperSymmetricPullback

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Exactly C3 and bounded actual derivatives 1,2,3; Φ itself may be unbounded. -/
structure SourceDerivatives (Φ : E → ℝ) where
  smooth : ContDiff ℝ 3 Φ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  bound1 : ∀ x, ‖iteratedFDeriv ℝ 1 Φ x‖ ≤ C1
  bound2 : ∀ x, ‖iteratedFDeriv ℝ 2 Φ x‖ ≤ C2
  bound3 : ∀ x, ‖iteratedFDeriv ℝ 3 Φ x‖ ≤ C3

lemma derivative_pullback (Φ : E → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (L : (κ → ℝ) →L[ℝ] E) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (y : κ → ℝ) :
    iteratedFDeriv ℝ n (Φ ∘ L) y =
      (iteratedFDeriv ℝ n Φ (L y)).compContinuousLinearMap (fun _ => L) :=
  L.iteratedFDeriv_comp_right hΦ y hn

lemma derivative_pullback_bound (Φ : E → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (L : (κ → ℝ) →L[ℝ] E) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3)
    (C : ℝ) (hC : ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C) (y : κ → ℝ) :
    ‖iteratedFDeriv ℝ n (Φ ∘ L) y‖ ≤ C * ‖L‖^n := by
  rw [derivative_pullback Φ hΦ L n hn]
  have h := (iteratedFDeriv ℝ n Φ (L y)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hC (L y)) (by positivity))

def pullbackDerivatives {Φ : E → ℝ} (D : SourceDerivatives Φ)
    (L : (κ → ℝ) →L[ℝ] E) : BoundedDerivatives (Φ ∘ L) where
  smooth := D.smooth.comp L.contDiff
  C1 := D.C1 * ‖L‖
  C2 := D.C2 * ‖L‖^2
  C3 := D.C3 * ‖L‖^3
  bound1 y := by simpa using derivative_pullback_bound Φ D.smooth L 1 (by norm_num) D.C1 D.bound1 y
  bound2 y := derivative_pullback_bound Φ D.smooth L 2 (by norm_num) D.C2 D.bound2 y
  bound3 y := derivative_pullback_bound Φ D.smooth L 3 (by norm_num) D.C3 D.bound3 y

lemma coordinateSlice_pullback {Φ : E → ℝ} (D : SourceDerivatives Φ)
    (L : (κ → ℝ) →L[ℝ] E) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3)
    (u : Fin n → κ) (y : κ → ℝ) :
    PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ L) n u y =
      iteratedFDeriv ℝ n Φ (L y) (fun i => L (direction (u i))) := by
  unfold PaperAutomaticDerivativeSlices.coordinateSlice
  rw [derivative_pullback Φ D.smooth L n hn]
  rfl
end General

local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

abbrev Index (d : ℕ) := {a : Fin d × Fin d // a.1 ≤ a.2}
def qSym (d : ℕ) (a : Index d) : SymFrob d := ofMatrix (Q a.val.1 a.val.2) (Q_transpose _ _)

def synth (d : ℕ) : (Index d → ℝ) →L[ℝ] SymFrob d :=
  ∑ a, (ContinuousLinearMap.proj a : (Index d → ℝ) →L[ℝ] ℝ).smulRight (qSym d a)

lemma synth_apply (d : ℕ) (y : Index d → ℝ) : synth d y = ∑ a, y a • qSym d a := by
  simp [synth, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

lemma synth_direction (d : ℕ) (a : Index d) : synth d (direction a)=qSym d a := by
  rw [synth_apply]
  simp [direction, Pi.single_apply, ite_smul]

lemma symmetric_coordinate_derivative {d : ℕ} {Φ : SymFrob d → ℝ}
    (D : SourceDerivatives Φ) (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3)
    (u : Fin n → Index d) (y : Index d → ℝ) :
    PaperAutomaticDerivativeSlices.coordinateSlice (Φ ∘ synth d) n u y =
      iteratedFDeriv ℝ n Φ (synth d y) (fun i => qSym d (u i)) := by
  rw [coordinateSlice_pullback D _ n hn]
  simp only [synth_direction]

def matrixLinear (d : ℕ) : SymFrob d →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := matrix
  map_add' := matrix_add
  map_smul' := matrix_smul

lemma matrix_injective (d : ℕ) : Function.Injective (matrix (d := d)) := by
  intro A B h
  apply Subtype.ext
  ext j i
  exact congrFun (congrFun h i) j

lemma matrix_qSym (d : ℕ) (a : Index d) : matrix (qSym d a)=Q a.val.1 a.val.2 :=
  matrix_ofMatrix _ _

lemma matrix_synth (d : ℕ) (y : Index d → ℝ) :
    matrix (synth d y)=∑ a, y a • Q a.val.1 a.val.2 := by
  rw [synth_apply]
  change matrixLinear d (∑ a, y a • qSym d a)=_
  rw [map_sum]
  simp only [map_smul]
  simp only [matrixLinear, LinearMap.coe_mk, AddHom.coe_mk, matrix_qSym]

def coordinates {d : ℕ} (M : SymFrob d) (a : Index d) : ℝ :=
  frobInner (matrix M) (Q a.val.1 a.val.2)

lemma synth_coordinates {d : ℕ} (M : SymFrob d) : synth d (coordinates M)=M := by
  apply matrix_injective d
  rw [matrix_synth]
  have he := Q_expansion (matrix M) (matrix_transpose M)
  have hs := Finset.sum_subtype (p := fun a : Fin d × Fin d => a.1 ≤ a.2) (F := inferInstance)
    (Finset.univ.filter (fun a : Fin d × Fin d => a.1 ≤ a.2))
    (by intro a; simp) (fun a : Fin d × Fin d =>
      frobInner (matrix M) (Q a.1 a.2) • Q a.1 a.2)
  change (∑ a : Index d, frobInner (matrix M) (Q a.val.1 a.val.2) • Q a.val.1 a.val.2)=_
  rw [← hs]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  exact he.symm

#print axioms pullbackDerivatives
#print axioms synth_coordinates
#print axioms symmetric_coordinate_derivative
end GaussianEllipsoid.PaperSymmetricPullback
