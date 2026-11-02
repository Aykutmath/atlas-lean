/-
Above-threshold interface objects: the conic margin functional, the
Section 16 uniform-conic-bound proposition, and the pathwise
feasibility-to-margin bridge.

- `UniformConicBound` is the Section 16 uniform conic lower bound
  (main-theorem-11-3), stated faithfully.
`fit_subset_conic` (proved) is the final pathwise step: a feasible `T`
normalizes to a Frobenius-unit `S` with zero centered measurements,
contradicting any positive margin.
Mathematical source: paper.tex, Sections 13 and 16.
-/
import GaussianEllipsoid.Basic
import GaussianEllipsoid.Centering
import GaussianEllipsoid.Coordinates
import GaussianEllipsoid.ExactFit
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.NormBridges
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace GaussianEllipsoid

/-! ### Conic margin and the uniform conic bound -/

/-- The conic margin functional: `inf` over Frobenius-unit PSD matrices of
`(1/n) ‖Π₀ Q_d(S)‖₁`. -/
def conicInf (d n : Nat) (x : Sample d n) : ℝ :=
  sInf {t : ℝ | ∃ S : Square d, S.PosSemidef ∧ frobeniusNorm S = 1 ∧
    t = (1 / (n : ℝ)) * l1Size (center (measurementQ x S))}

/-- Section 16 (main-theorem-11-3): on every fixed aspect-ratio interval
above `1/4`, the conic margin has a uniform positive lower bound outside
an exponentially small failure event. -/
def UniformConicBound : Prop :=
  ∀ αm αp : ℝ, 1 / 4 < αm → αm ≤ αp →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ (d : Nat) in Filter.atTop, ∀ n : Nat,
      αm * (d : ℝ) ^ 2 ≤ (n : ℝ) → (n : ℝ) ≤ αp * (d : ℝ) ^ 2 →
      ((gaussianSampleLaw d n) {x | conicInf d n x < c}).toReal
        ≤ Real.exp (-C * (d : ℝ) ^ 2)

/-! ### Proved pathwise bridge -/

/-- The centered rank-one measurements commute with scaling. -/
theorem measurementQ_smul {d n : Nat} (c : ℝ) (x : Sample d n)
    (S : Square d) :
    measurementQ x (c • S) = c • measurementQ x S := by
  funext i
  unfold measurementQ
  rw [quadratic_smul, Matrix.trace_smul]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- A feasible sample lies below every positive conic margin: normalize
`T` to Frobenius norm one; its centered measurements vanish. -/
theorem fit_subset_conic {d n : Nat} {c : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hc : 0 < c) :
    {x : Sample d n | HasFit x} ⊆ {x | conicInf d n x < c} := by
  intro x hx
  obtain ⟨T, hT⟩ := hx
  obtain ⟨hTpsd, hTmeas⟩ := hT
  have hTne : T ≠ 0 := Feasible.ne_zero hd hn ⟨hTpsd, hTmeas⟩
  have hFne : frobeniusNorm T ≠ 0 := fun h =>
    hTne ((frobeniusNorm_eq_zero_iff T).mp h)
  set s : ℝ := (frobeniusNorm T)⁻¹ with hsdef
  have hsnn : 0 ≤ s := inv_nonneg.mpr (frobeniusNorm_nonneg T)
  have hS : (s • T).PosSemidef := hTpsd.smul hsnn
  have hnorm : frobeniusNorm (s • T) = 1 := by
    rw [frobeniusNorm_smul, Real.norm_eq_abs, abs_of_nonneg hsnn, hsdef]
    exact inv_mul_cancel₀ hFne
  have hQconst : measurementQ x T
      = fun _ => ((d : ℝ) - Matrix.trace T) / Real.sqrt 2 := by
    funext i
    unfold measurementQ
    rw [hTmeas i]
  have hQ0 : center (measurementQ x (s • T)) = 0 := by
    rw [measurementQ_smul, hQconst, center_smul, center_const hn _,
      smul_zero]
  have hval : (1 / (n : ℝ)) * l1Size (center (measurementQ x (s • T)))
      = 0 := by
    rw [hQ0]
    unfold l1Size
    simp
  have hbdd : BddBelow {t : ℝ | ∃ S : Square d,
      S.PosSemidef ∧ frobeniusNorm S = 1 ∧
        t = (1 / (n : ℝ)) * l1Size (center (measurementQ x S))} := by
    refine ⟨0, ?_⟩
    rintro t ⟨S, -, -, rfl⟩
    apply mul_nonneg
    · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · unfold l1Size
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmem : (0 : ℝ) ∈ {t : ℝ | ∃ S : Square d,
      S.PosSemidef ∧ frobeniusNorm S = 1 ∧
        t = (1 / (n : ℝ)) * l1Size (center (measurementQ x S))} :=
    ⟨s • T, hS, hnorm, hval.symm⟩
  have hle : conicInf d n x ≤ 0 := by
    unfold conicInf
    exact csInf_le hbdd hmem
  exact lt_of_le_of_lt hle hc

/-- The conic margin functional is nonnegative for `d ≥ 1`
(the rank-one projector onto `e₀` witnesses nonemptiness). -/
theorem conicInf_nonneg {d n : Nat} (hd : 0 < d) (x : Sample d n) :
    0 ≤ conicInf d n x := by
  unfold conicInf
  refine le_csInf ?_ ?_
  · -- Nonempty: the rank-one projector `e₀ e₀ᵀ` is PSD Frobenius-unit.
    set i₀ : Fin d := ⟨0, hd⟩ with hi₀
    set e : Vector d := Pi.single i₀ 1 with he
    have hsum : ∑ i, (e i) ^ 2 = 1 := by
      have hfun : (fun i => (e i) ^ 2) = Pi.single i₀ 1 := by
        funext i
        by_cases h : i = i₀
        · subst h
          simp [he]
        · simp [he, h]
      rw [hfun]
      simp
    have hpsd : (Matrix.vecMulVec e e).PosSemidef := by
      have h := Matrix.posSemidef_vecMulVec_self_star e
      have hstar : star e = e := by
        funext i
        simp [he]
      rw [hstar] at h
      exact h
    have hF : frobeniusNorm (Matrix.vecMulVec e e) = 1 := by
      have hsq : (frobeniusNorm (Matrix.vecMulVec e e)) ^ 2 = 1 := by
        rw [frobeniusNorm_vecMulVec_sq, hsum, mul_one]
      have hnn := frobeniusNorm_nonneg (Matrix.vecMulVec e e)
      conv_lhs => rw [← Real.sqrt_sq hnn]
      rw [hsq, Real.sqrt_one]
    exact ⟨(1 / (n : ℝ)) * l1Size (center (measurementQ x (Matrix.vecMulVec e e))),
      Matrix.vecMulVec e e, hpsd, hF, rfl⟩
  · rintro t ⟨S, -, -, rfl⟩
    apply mul_nonneg
    · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
    · show 0 ≤ l1Size (center (measurementQ x S))
      exact Finset.sum_nonneg fun i _ => abs_nonneg _

end GaussianEllipsoid
