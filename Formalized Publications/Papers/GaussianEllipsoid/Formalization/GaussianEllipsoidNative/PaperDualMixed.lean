import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.Discretize

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid

theorem mixedNorm_le_l1 {d n : ℕ} {η : ℝ} (hη : 0 ≤ η) (y : Vector n) :
    mixedNorm η d n y ≤ η * Real.sqrt d * l1Size y := by
  unfold mixedNorm
  apply csInf_le
  · exact ⟨0, by rintro w ⟨u,v,_,rfl⟩; exact add_nonneg (mul_nonneg (mul_nonneg hη (Real.sqrt_nonneg _)) (Finset.sum_nonneg fun i _ => abs_nonneg (u i))) (mul_nonneg (Nat.cast_nonneg _) (euclidNorm_nonneg v))⟩
  · exact ⟨y,0,by simp,by simp [euclidNorm]⟩

theorem mixedNorm_le_l2 {d n : ℕ} {η : ℝ} (hη : 0 ≤ η) (y : Vector n) :
    mixedNorm η d n y ≤ d * euclidNorm y := by
  unfold mixedNorm
  apply csInf_le
  · exact ⟨0, by rintro w ⟨u,v,_,rfl⟩; exact add_nonneg (mul_nonneg (mul_nonneg hη (Real.sqrt_nonneg _)) (Finset.sum_nonneg fun i _ => abs_nonneg (u i))) (mul_nonneg (Nat.cast_nonneg _) (euclidNorm_nonneg v))⟩
  · exact ⟨0,y,by simp,by simp [l1Size]⟩

/-- Exact least Hölder constant on the full coefficient space. -/
theorem dualMixed_le_iff_holder {d n : ℕ} {η C : ℝ} (hη : 0 < η)
    (hd : 0 < d) (hC : 0 ≤ C) (e : Vector n) :
    dualMixed η d n e ≤ C ↔
      ∀ y : Vector n, |∑ i, e i * y i| ≤ C * mixedNorm η d n y := by
  constructor
  · intro h y
    exact (mixedNorm_holder hη hd).trans
      (mul_le_mul_of_nonneg_right h (mixedNorm_nonneg hη.le y))
  · intro h
    have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
    have ha : 0 < η * Real.sqrt d := mul_pos hη (Real.sqrt_pos.mpr hdR)
    unfold dualMixed
    apply max_le
    · apply (div_le_iff₀ ha).mpr
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC ha.le)).mpr
      intro i
      have hi := (h (Pi.single i 1)).trans
        (mul_le_mul_of_nonneg_left (mixedNorm_le_l1 hη.le (Pi.single i 1)) hC)
      simpa [l1Size, Real.norm_eq_abs, Pi.single_apply, Finset.mul_sum, apply_ite abs] using hi
    · apply (div_le_iff₀ hdR).mpr
      have he := (h e).trans (mul_le_mul_of_nonneg_left (mixedNorm_le_l2 hη.le e) hC)
      have hsq : (∑ i, e i * e i) = euclidNorm e ^ 2 := by
        rw [euclidNorm_sq]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hsq, abs_of_nonneg (sq_nonneg _)] at he
      have hn := euclidNorm_nonneg e
      by_cases hz : euclidNorm e = 0
      · simpa [hz] using mul_nonneg hC hdR.le
      · have hp : 0 < euclidNorm e := lt_of_le_of_ne hn (Ne.symm hz)
        apply (mul_le_mul_iff_right₀ hp).mp
        nlinarith only [he]
theorem dualMixed_le_iff_unit_support {d n : ℕ} {η C : ℝ} (hη : 0 < η)
    (hd : 0 < d) (hC : 0 ≤ C) (e : Vector n) :
    dualMixed η d n e ≤ C ↔
      ∀ y : Vector n, mixedNorm η d n y ≤ 1 → |∑ i, e i * y i| ≤ C := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha : 0 < η * Real.sqrt d := mul_pos hη (Real.sqrt_pos.mpr hdR)
  constructor
  · intro h y hy
    exact ((dualMixed_le_iff_holder hη hd hC e).mp h y).trans
      (by simpa using mul_le_mul_of_nonneg_left hy hC)
  · intro h
    unfold dualMixed
    apply max_le
    · apply (div_le_iff₀ ha).mpr
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC ha.le)).mpr
      intro i
      let y : Vector n := Pi.single i ((η * Real.sqrt d)⁻¹)
      have hy : mixedNorm η d n y ≤ 1 := by
        apply (mixedNorm_le_l1 hη.le y).trans
        simp [y,l1Size,Pi.single_apply,apply_ite abs,abs_of_pos (inv_pos.mpr ha),abs_of_pos hη,abs_of_nonneg (Real.sqrt_nonneg _),hη.ne', (Real.sqrt_pos.mpr hdR).ne']
        field_simp
        norm_num
      have hi := h y hy
      have hi' : |e i| * (η * Real.sqrt d)⁻¹ ≤ C := by
        simpa [y,Pi.single_apply,abs_mul,abs_of_pos (inv_pos.mpr ha),abs_of_pos hη,abs_of_nonneg (Real.sqrt_nonneg _)] using hi
      rw [← div_eq_mul_inv] at hi'
      simpa only [Real.norm_eq_abs] using (div_le_iff₀ ha).mp hi'
    · by_cases hz : euclidNorm e = 0
      · simp [hz,hC]
      have hp : 0 < euclidNorm e := lt_of_le_of_ne (euclidNorm_nonneg e) (Ne.symm hz)
      let a : ℝ := ((d:ℝ) * euclidNorm e)⁻¹
      have ha' : 0 < a := inv_pos.mpr (mul_pos hdR hp)
      let y : Vector n := a • e
      have hy : mixedNorm η d n y ≤ 1 := by
        apply (mixedNorm_le_l2 hη.le y).trans
        rw [show y = a • e from rfl, euclidNorm_smul, abs_of_pos ha']
        dsimp [a]
        field_simp
        norm_num
      have hi := h y hy
      have heq : (∑ i, e i * y i) = euclidNorm e / d := by
        simp only [y,Pi.smul_apply,smul_eq_mul]
        calc (∑ i, e i * (a * e i)) = a * ∑ i, e i ^ 2 := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          _ = a * euclidNorm e ^ 2 := by rw [euclidNorm_sq]
          _ = euclidNorm e / d := by dsimp [a]; field_simp
      rw [heq,abs_of_nonneg (div_nonneg hp.le hdR.le)] at hi
      exact hi

/-- Literal full-space dual support value; the empty coefficient space is included. -/
theorem paper_dual_mixed_norm {d n : ℕ} {η : ℝ} (hη : 0 < η)
    (hd : 0 < d) (e : Vector n) :
    sSup {v : ℝ | ∃ y : Vector n, mixedNorm η d n y ≤ 1 ∧ v = |∑ i, e i * y i|} =
      max (‖e‖ / (η * Real.sqrt d)) (euclidNorm e / d) := by
  let S : Set ℝ := {v | ∃ y : Vector n, mixedNorm η d n y ≤ 1 ∧ v = |∑ i, e i * y i|}
  have hM : 0 ≤ dualMixed η d n e := le_trans (div_nonneg (norm_nonneg _) (by positivity)) (le_max_left _ _)
  have hb : BddAbove S := ⟨dualMixed η d n e, by rintro v ⟨y,hy,rfl⟩; exact (dualMixed_le_iff_unit_support hη hd hM e).mp le_rfl y hy⟩
  have hz : (0:ℝ) ∈ S := ⟨0,by simp [mixedNorm_zero hη.le],by simp⟩
  change sSup S = dualMixed η d n e
  apply le_antisymm
  · apply csSup_le ⟨0,hz⟩
    rintro v ⟨y,hy,rfl⟩
    exact (dualMixed_le_iff_unit_support hη hd hM e).mp le_rfl y hy
  · apply (dualMixed_le_iff_unit_support hη hd (le_csSup hb hz) e).mpr
    intro y hy
    exact le_csSup hb ⟨y,hy,rfl⟩

/-- Literal intersection-of-balls polar description. -/
theorem paper_mixed_polar {d n : ℕ} {η : ℝ} (hη : 0 < η)
    (hd : 0 < d) (e : Vector n) :
    (∀ y : Vector n, mixedNorm η d n y ≤ 1 → |∑ i, e i*y i| ≤ 1) ↔
      ‖e‖ ≤ η*Real.sqrt d ∧ euclidNorm e ≤ d := by
  rw [← dualMixed_le_iff_unit_support hη hd (by norm_num) e]
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha : 0 < η*Real.sqrt d := mul_pos hη (Real.sqrt_pos.mpr hdR)
  simp only [dualMixed,max_le_iff,div_le_iff₀ ha,div_le_iff₀ hdR,one_mul]

/-- Restriction to any coefficient subspace, including the centered subspace,
can only reduce the dual support. -/
theorem paper_restricted_dual_support_le {d n : ℕ} {η : ℝ} (hη : 0 < η)
    (hd : 0 < d) (e : Vector n) (W : Submodule ℝ (Vector n)) :
    sSup {v : ℝ | ∃ y ∈ W, mixedNorm η d n y ≤ 1 ∧ v = |∑ i, e i*y i|} ≤
      dualMixed η d n e := by
  have hM : 0 ≤ dualMixed η d n e := le_trans (div_nonneg (norm_nonneg _) (by positivity)) (le_max_left _ _)
  apply csSup_le
  · exact ⟨0,0,W.zero_mem,by simp [mixedNorm_zero hη.le],by simp⟩
  · rintro v ⟨y,_,hy,rfl⟩
    exact (dualMixed_le_iff_unit_support hη hd hM e).mp le_rfl y hy
end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_dual_mixed_norm
#print axioms GaussianEllipsoid.paper_mixed_polar
#print axioms GaussianEllipsoid.paper_restricted_dual_support_le
