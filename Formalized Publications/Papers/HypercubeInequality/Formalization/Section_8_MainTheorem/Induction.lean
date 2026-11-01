module

/-
# Finite-support main inequality (HI-MAIN-FIN, HI-INDUCTION core)

Paper Sections 6/8: for finitely supported laws, `oneStep` + `base_le`
assemble by induction into `S_d ≤ ((d+1)/2^d) ∏ D_j` with the exact
manuscript constant. The projection-gap identity `D_j(μ) = D_j(ν)` and
the constant reunion `((d+1)/(2d))·(d/2^{d-1}) = (d+1)/2^d` are proved
here. The extension to general Borel laws (HI-MAIN) additionally needs
the Section 7 approximation theory.
-/

public import Mathlib
public import Section_6_OneStep.Onestep

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

section ProjGap

variable {k N : ℕ} (c : Fin N → ℝ≥0∞)
  (W : Fin N → EuclideanSpace ℝ (Fin (k + 1)))

/-- Projected coordinate gaps agree with the original ones. -/
public theorem gap_proj_atomMeas (hc : ∀ i, c i ≠ ∞) (j : Fin k) :
    gap j (atomMeas c (Yatom W))
    = gap j.castSucc (atomMeas c W) := by
  rw [gap_atomMeas c (Yatom W) j hc, gap_atomMeas c W j.castSucc hc]
  rfl

end ProjGap

section MainInduction

/-- Constant reunion for the induction step. -/
public theorem scalar_induction (m : ℕ) :
    ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ)
        / (2 * ((((m + 1) + 1 : ℕ)) : ℝ)))
      * ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
    = ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ) / 2 ^ ((m + 1) + 1)) := by
  rw [show (m + 1) + 1 = m + 2 from rfl]
  have h2P : (2 : ℝ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ']
  rw [h2P]
  have hCpos : (0 : ℝ) < ((((m + 2 : ℕ)) : ℝ)) :=
    Nat.cast_pos.mpr (by omega)
  rw [← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (mul_pos (by norm_num) hCpos)))]
  congr 1
  have hC : ((((m + 2 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hCpos
  have hP : (2 : ℝ) ^ (m + 1) ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
  field_simp

/-- HI-MAIN-FIN: random-simplex inequality for finitely supported laws,
with the exact manuscript constant `(d+1)/2^d`. -/
public theorem main_fin_support (m : ℕ) :
    ∀ (N : ℕ) (p : Fin N → ℝ) (Z : Fin N → EuclideanSpace ℝ (Fin (m + 1))),
    (∀ i, 0 < p i) → (∑ i, p i = 1) →
    S (m + 1) (atomMeas (wgt p) Z)
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), gap j (atomMeas (wgt p) Z) := by
  induction m with
  | zero =>
    intro N p Z hpos hsum
    have hconst1 : ENNReal.ofReal (((((0 + 2 : ℕ)) : ℝ) / 2 ^ (0 + 1))) = 1 := by
      have e : ((((0 + 2 : ℕ)) : ℝ) / 2 ^ (0 + 1)) = 1 := by
        push_cast
        norm_num
      rw [e, ENNReal.ofReal_one]
    have hprod : (∏ j : Fin (0 + 1), gap j (atomMeas (wgt p) Z))
        = gap (Fin.last 0) (atomMeas (wgt p) Z) :=
      Fin.prod_univ_one _
    rw [hconst1, hprod, one_mul]
    exact base_le p Z hpos hsum
  | succ m ih =>
    intro N p Z hpos hsum
    have h1 := oneStep (m := m + 1) p Z hpos hsum
    have h2 := ih N p (Yatom Z) hpos hsum
    have hgap : ∀ j : Fin (m + 1),
        gap j (atomMeas (wgt p) (Yatom Z))
        = gap j.castSucc (atomMeas (wgt p) Z) := by
      intro j
      exact gap_proj_atomMeas (wgt p) Z (fun i => wgt_ne_top p i) j
    have hP : (∏ j : Fin (m + 1), gap j (atomMeas (wgt p) (Yatom Z)))
        = ∏ j : Fin (m + 1), gap j.castSucc (atomMeas (wgt p) Z) :=
      Finset.prod_congr rfl (fun j _ => hgap j)
    rw [hP] at h2
    have h3 := h1.trans (mul_le_mul_right h2 _)
    have hsplit : (∏ j : Fin (m + 1 + 1), gap j (atomMeas (wgt p) Z))
        = (∏ j : Fin (m + 1), gap j.castSucc (atomMeas (wgt p) Z))
          * gap (Fin.last (m + 1)) (atomMeas (wgt p) Z) :=
      Fin.prod_univ_castSucc _
    rw [hsplit]
    calc S (m + 1 + 1) (atomMeas (wgt p) Z)
        ≤ ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ)
            / (2 * ((((m + 1) + 1 : ℕ)) : ℝ)))
          * gap (Fin.last (m + 1)) (atomMeas (wgt p) Z)
          * (ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
            * ∏ j : Fin (m + 1), gap j.castSucc (atomMeas (wgt p) Z)) := h3
      _ = ENNReal.ofReal (((((m + 1) + 2 : ℕ)) : ℝ) / 2 ^ ((m + 1) + 1))
          * ((∏ j : Fin (m + 1), gap j.castSucc (atomMeas (wgt p) Z))
            * gap (Fin.last (m + 1)) (atomMeas (wgt p) Z)) := by
          rw [← scalar_induction m]
          ring

end MainInduction

end HypercubeInequality
