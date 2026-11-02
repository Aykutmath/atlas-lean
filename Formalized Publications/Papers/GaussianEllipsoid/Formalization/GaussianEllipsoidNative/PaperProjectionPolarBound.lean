/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Sharp polar proof; native verification result recorded separately. -/
import PaperCanonicalPolarFull
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open GaussianEllipsoid GaussianEllipsoid.PaperCanonicalPolar
open scoped Matrix.Norms.L2Operator MatrixOrder
namespace GaussianEllipsoid.PaperProjectionPolarAlgebra

def switch {d : ℕ} (P Q : Mat d d) : Mat d d := Q*P+(1-Q)*(1-P)
def defect {d : ℕ} (P Q : Mat d d) : Mat d d := 1-(P-Q)^2

theorem switch_intertwine {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : switch P Q * P = Q * switch P Q := by
  have hp (A : Mat d d) : P*(P*A)=P*A := by rw [← mul_assoc, hP.isIdempotentElem.eq]
  have hq (A : Mat d d) : Q*(Q*A)=Q*A := by rw [← mul_assoc, hQ.isIdempotentElem.eq]
  simp only [switch, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hp, hq]
  noncomm_ring

theorem switch_star_mul {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : star (switch P Q) * switch P Q = defect P Q := by
  have hp (A : Mat d d) : P*(P*A)=P*A := by rw [← mul_assoc, hP.isIdempotentElem.eq]
  have hq (A : Mat d d) : Q*(Q*A)=Q*A := by rw [← mul_assoc, hQ.isIdempotentElem.eq]
  simp only [switch, defect, pow_two, star_add, star_mul, star_sub, star_one,
    hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
    mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hp, hq]
  noncomm_ring

theorem defect_commute_left {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : Commute (defect P Q) P := by
  have hp (A : Mat d d) : P*(P*A)=P*A := by rw [← mul_assoc, hP.isIdempotentElem.eq]
  have hq (A : Mat d d) : Q*(Q*A)=Q*A := by rw [← mul_assoc, hQ.isIdempotentElem.eq]
  change defect P Q * P = P * defect P Q
  simp only [defect, pow_two, mul_sub, sub_mul, one_mul, mul_one, mul_assoc,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hp, hq]
  noncomm_ring

def polar {d : ℕ} (P Q : Mat d d) : Mat d d := switch P Q * inverseRoot (defect P Q)

theorem polar_intertwine {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : polar P Q * P = Q * polar P Q := by
  have hc := (defect_commute_left P Q hP hQ).cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)
  change switch P Q * inverseRoot (defect P Q) * P = Q * (switch P Q * inverseRoot (defect P Q))
  rw [mul_assoc, show inverseRoot (defect P Q) * P = P * inverseRoot (defect P Q) from hc.eq,
    ← mul_assoc, switch_intertwine P Q hP hQ, mul_assoc]

theorem defect_nonneg {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : 0 ≤ defect P Q := by
  rw [← switch_star_mul P Q hP hQ]
  exact star_mul_self_nonneg _

theorem defect_isUnit {d : ℕ} (P Q : Mat d d) (hδ : ‖P-Q‖ < 1) : IsUnit (defect P Q) := by
  apply isUnit_one_sub_of_norm_lt_one
  calc
    ‖(P-Q)^2‖ ≤ ‖P-Q‖^2 := (by simpa only [pow_two] using norm_mul_le (P-Q) (P-Q))
    _ < 1 := by nlinarith [norm_nonneg (P-Q)]

theorem inverseRoot_sandwich {d : ℕ} (V : Mat d d) (hV : IsSelfAdjoint V)
    (hpos : 0 ≤ V) (hunit : IsUnit V) : inverseRoot V * V * inverseRoot V = 1 := by
  have hf : (spectrum ℝ V).Finite := by
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hV]
    exact Set.finite_range _
  have hp (x : ℝ) (hx : x ∈ spectrum ℝ V) : 0 < x := by
    have hn := spectrum_nonneg_of_nonneg hpos hx
    have hz : x ≠ 0 := by
      intro hz
      subst x
      exact ((spectrum.zero_notMem_iff ℝ).mpr hunit) hx
    exact lt_of_le_of_ne hn (Ne.symm hz)
  unfold inverseRoot
  conv_lhs => arg 1; arg 2; rw [← cfc_id' ℝ V hV]
  rw [← cfc_mul _ _ V (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ V (hf.continuousOn _) (hf.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) V := by
      apply cfc_congr
      intro x hx
      have hs := Real.sq_sqrt (hp x hx).le
      have hn := (Real.sqrt_pos.mpr (hp x hx)).ne'
      dsimp
      field_simp
      nlinarith
    _ = 1 := cfc_const_one ℝ V hV

theorem polar_star_mul {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hδ : ‖P-Q‖ < 1) : star (polar P Q) * polar P Q = 1 := by
  have hV : IsSelfAdjoint (defect P Q) := by
    rw [← switch_star_mul P Q hP hQ]
    exact IsSelfAdjoint.star_mul_self _
  have hR : star (inverseRoot (defect P Q)) = inverseRoot (defect P Q) :=
    IsSelfAdjoint.cfc.star_eq
  simp only [polar, star_mul, hR]
  rw [mul_assoc, ← mul_assoc (star (switch P Q)), switch_star_mul P Q hP hQ, ← mul_assoc]
  exact inverseRoot_sandwich _ hV (defect_nonneg P Q hP hQ) (defect_isUnit P Q hδ)

theorem switch_mul_star {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : switch P Q * star (switch P Q) = defect P Q := by
  have hp (A : Mat d d) : P*(P*A)=P*A := by rw [← mul_assoc, hP.isIdempotentElem.eq]
  have hq (A : Mat d d) : Q*(Q*A)=Q*A := by rw [← mul_assoc, hQ.isIdempotentElem.eq]
  simp only [switch, defect, pow_two, star_add, star_mul, star_sub, star_one,
    hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
    mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, mul_assoc,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hp, hq]
  noncomm_ring

theorem switch_add_star {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : switch P Q + star (switch P Q) = (2:ℝ) • defect P Q := by
  simp only [switch, defect, pow_two, two_smul, star_add, star_mul, star_sub, star_one,
    hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
    mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
    hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  noncomm_ring

theorem defect_commute_switch {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : Commute (defect P Q) (switch P Q) := by
  change defect P Q * switch P Q = switch P Q * defect P Q
  calc
    _ = (switch P Q * star (switch P Q)) * switch P Q := by rw [switch_mul_star P Q hP hQ]
    _ = switch P Q * (star (switch P Q) * switch P Q) := mul_assoc _ _ _
    _ = _ := by rw [switch_star_mul P Q hP hQ]

theorem mul_inverseRoot_eq_root {d : ℕ} (V : Mat d d) (hV : IsSelfAdjoint V)
    (hpos : 0 ≤ V) : V * inverseRoot V = cfc Real.sqrt V := by
  have hf : (spectrum ℝ V).Finite := by
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hV]
    exact Set.finite_range _
  unfold inverseRoot
  conv_lhs => arg 1; rw [← cfc_id' ℝ V hV]
  rw [← cfc_mul _ _ V (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x hx
  have hx0 := spectrum_nonneg_of_nonneg hpos hx
  dsimp
  by_cases hz : x=0
  · simp [hz]
  · have hs := Real.sq_sqrt hx0
    have hn := (Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm hz))).ne'
    field_simp
    nlinarith

theorem polar_add_star {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : polar P Q + star (polar P Q) = (2:ℝ) • cfc Real.sqrt (defect P Q) := by
  have hV : IsSelfAdjoint (defect P Q) := by
    rw [← switch_star_mul P Q hP hQ]
    exact IsSelfAdjoint.star_mul_self _
  have hR : star (inverseRoot (defect P Q)) = inverseRoot (defect P Q) := IsSelfAdjoint.cfc.star_eq
  have hc := (defect_commute_switch P Q hP hQ).cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)
  have hcs : inverseRoot (defect P Q) * star (switch P Q) =
      star (switch P Q) * inverseRoot (defect P Q) := by
    have hc' : inverseRoot (defect P Q) * switch P Q = switch P Q * inverseRoot (defect P Q) := hc.eq
    have hh := congrArg star hc'
    simpa only [star_mul, hR] using hh.symm
  simp only [polar, star_mul, hR]
  rw [hcs, ← add_mul, switch_add_star P Q hP hQ, smul_mul_assoc,
    mul_inverseRoot_eq_root _ hV (defect_nonneg P Q hP hQ)]

theorem sqrt_gap_norm_le {d : ℕ} (V : Mat d d) (hV : IsSelfAdjoint V)
    (hpos : 0 ≤ V) : ‖1-cfc Real.sqrt V‖ ≤ ‖1-V‖ := by
  have hf : (spectrum ℝ V).Finite := by
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hV]
    exact Set.finite_range _
  have he : cfc (fun x : ℝ => 1-Real.sqrt x) V = 1-cfc Real.sqrt V := by
    rw [cfc_sub _ _ V (hf.continuousOn _) (hf.continuousOn _), cfc_const_one ℝ V hV]
  rw [← he]
  apply norm_cfc_le (norm_nonneg _)
  intro x hx
  have hn := norm_apply_le_norm_cfc (fun x : ℝ => 1-x) V hx (hf.continuousOn _) hV
  rw [cfc_sub _ _ V (hf.continuousOn _) (hf.continuousOn _), cfc_const_one ℝ V hV,
    cfc_id' ℝ V hV] at hn
  apply le_trans _ hn
  simp only [Real.norm_eq_abs]
  have hx0 := spectrum_nonneg_of_nonneg hpos hx
  have hs := Real.sq_sqrt hx0
  have hfactor : 1-x=(1-Real.sqrt x)*(1+Real.sqrt x) := by nlinarith
  rw [hfactor, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1+Real.sqrt x)]
  nlinarith [abs_nonneg (1-Real.sqrt x),Real.sqrt_nonneg x]

theorem polar_norm_sub_one_le {d : ℕ} (P Q : Mat d d) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hδ : ‖P-Q‖ < 1) :
    ‖polar P Q-1‖ ≤ Real.sqrt 2*‖P-Q‖ := by
  have hV : IsSelfAdjoint (defect P Q) := by
    rw [← switch_star_mul P Q hP hQ]
    exact IsSelfAdjoint.star_mul_self _
  have he : star (polar P Q-1)*(polar P Q-1) = (2:ℝ) • (1-cfc Real.sqrt (defect P Q)) := by
    rw [star_sub,star_one,mul_sub,sub_mul,sub_mul,mul_one,one_mul,one_mul,
      polar_star_mul P Q hP hQ hδ]
    calc
      _ = (2:ℝ) • (1 : Mat d d) - (polar P Q+star (polar P Q)) := by simp only [two_smul]; noncomm_ring
      _ = _ := by rw [polar_add_star P Q hP hQ, smul_sub]
  have hsq : ‖polar P Q-1‖^2 ≤ 2*‖P-Q‖^2 := by
    calc
      _ = ‖star (polar P Q-1)*(polar P Q-1)‖ := by rw [CStarRing.norm_star_mul_self, pow_two]
      _ = 2*‖1-cfc Real.sqrt (defect P Q)‖ := by rw [he,norm_smul]; norm_num
      _ ≤ 2*‖1-defect P Q‖ := mul_le_mul_of_nonneg_left
        (sqrt_gap_norm_le _ hV (defect_nonneg P Q hP hQ)) (by norm_num)
      _ = 2*‖(P-Q)^2‖ := by simp only [defect, sub_sub_cancel]
      _ ≤ 2*‖P-Q‖^2 := mul_le_mul_of_nonneg_left ((by simpa only [pow_two] using norm_mul_le (P-Q) (P-Q))) (by norm_num)
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 2*‖P-Q‖ := by positivity
  nlinarith [norm_nonneg (polar P Q-1)]

end GaussianEllipsoid.PaperProjectionPolarAlgebra

#print axioms GaussianEllipsoid.PaperProjectionPolarAlgebra.polar_intertwine
#print axioms GaussianEllipsoid.PaperProjectionPolarAlgebra.polar_star_mul
#print axioms GaussianEllipsoid.PaperProjectionPolarAlgebra.polar_norm_sub_one_le
