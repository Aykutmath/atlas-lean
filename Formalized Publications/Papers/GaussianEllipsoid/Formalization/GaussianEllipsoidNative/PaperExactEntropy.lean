import PaperNuisanceNet
import UCDiffuseNets

noncomputable section
open Module
open scoped BigOperators
namespace GaussianEllipsoid.PaperExactEntropy

/-- The displayed entropy constant in paper Lemma nets-entropy, with no
sample-size-dependent nuisance logarithm and no additional additive constant. -/
theorem paper_entropy_bound {d n M I J : ℕ} {a r B s : ℝ}
    (hn : 0 < n) (ha : 0 < a) (hr : 0 < r) (hr1 : r ≤ 1)
    (hB : 0 ≤ B) (hs : 0 < s) (hM : M ≤ n)
    (haspect : a*(d:ℝ)^2 ≤ n)
    (hI : (I:ℝ) ≤ (1+2/r)^(d*d))
    (hJ : (J:ℝ) ≤ (1+2*B/s)^M) :
    Real.log ((I*J:ℕ):ℝ)/(n:ℝ) ≤
      (1/a)*Real.log (3/r)+Real.log (1+2*B/s) := by
  have hbase : 1 ≤ 3/r := (le_div_iff₀ hr).mpr (by linarith)
  have hlogr : 0 ≤ Real.log (3/r) := Real.log_nonneg hbase
  have hlogs : 0 ≤ Real.log (1+2*B/s) := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hright : 0 ≤ (1/a)*Real.log (3/r)+Real.log (1+2*B/s) := by positivity
  by_cases hi : I=0
  · simpa only [hi, zero_mul, Nat.cast_zero, Real.log_zero, zero_div] using hright
  by_cases hj : J=0
  · simpa only [hj, mul_zero, Nat.cast_zero, Real.log_zero, zero_div] using hright
  have hi0 : (0:ℝ) < I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi)
  have hj0 : (0:ℝ) < J := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)
  have hlI := Real.log_le_log hi0 hI
  have hlJ := Real.log_le_log hj0 hJ
  rw [Real.log_pow] at hlI hlJ
  have hb : 1+2/r ≤ 3/r := by
    apply (le_div_iff₀ hr).mpr
    have he : (1+2/r)*r=r+2 := by field_simp
    rw [he]
    linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<1+2/r) hb
  have hl' := mul_le_mul_of_nonneg_left hl (sq_nonneg (d:ℝ))
  have hli : Real.log (I:ℝ) ≤ (d:ℝ)^2*Real.log (3/r) := by
    have he : ((d*d:ℕ):ℝ)=(d:ℝ)^2 := by push_cast; ring
    rw [he] at hlI
    exact hlI.trans hl'
  have hMm : (M:ℝ) ≤ n := by exact_mod_cast hM
  have hlj := hlJ.trans (mul_le_mul_of_nonneg_right hMm hlogs)
  have hd : (d:ℝ)^2 ≤ (n:ℝ)/a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hdm := mul_le_mul_of_nonneg_right hd hlogr
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ)<n)).mpr
  rw [Nat.cast_mul, Real.log_mul hi0.ne' hj0.ne']
  calc
    _ ≤ ((n:ℝ)/a)*Real.log (3/r)+(n:ℝ)*Real.log (1+2*B/s) := by linarith
    _ = _ := by ring

/-- Full paper net construction: internal r-separated covering of the diffuse
matrix class, intrinsic l1 nuisance cover, and the exact displayed R* bound. -/
theorem paper_joint_nets (d n : ℕ) (hn : 0 < n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a τ r B s : ℝ) (ha : 0 < a) (hr : 0 < r) (hr1 : r ≤ 1)
    (hB : 0 ≤ B) (hs : 0 < s) (hsB : s ≤ B)
    (haspect : a*(d:ℝ)^2 ≤ n) :
    ∃ ND : Finset (UCContinuityGeometry.SymFrob d),
    ∃ NL : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ A ∈ ND, A ∈ UCDiffuseNets.diffuseClass d τ) ∧
      (∀ A ∈ UCDiffuseNets.diffuseClass d τ, ∃ D ∈ ND, ‖A-D‖ < r) ∧
      (∀ A ∈ ND, ∀ D ∈ ND, A ≠ D → r ≤ ‖A-D‖) ∧
      (∀ v ∈ NL, v ∈ L ∧ (∑ i, |v i|) ≤ B*n) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), v ∈ L → (∑ i, |v i|) ≤ B*n →
        ∃ w ∈ NL, (∑ i, |v i-w i|) < s*n) ∧
      Real.log ((ND.card*NL.card:ℕ):ℝ)/(n:ℝ) ≤
        (1/a)*Real.log (3/r)+Real.log (1+2*B/s) := by
  obtain ⟨ND,hND,hDcard,hDcover,hDsep⟩ := exists_internal_net
    (UCDiffuseNets.diffuseClass d τ) (R := 1) (ε := r) (by norm_num) hr
      (fun A hA => hA.2.1.le)
  have hDcard' : (ND.card:ℝ) ≤ (1+2/r)^(d*d) := by
    simp only [mul_one] at hDcard
    exact hDcard.trans (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
      (UCContinuityGeometry.symFrob_finrank_le d))
  obtain ⟨NL,hNL,hLcard,hLcover⟩ :=
    PaperNuisanceNet.exists_intrinsic_l1_net n hn L B s hB hs
  refine ⟨ND,NL,hND,?_,?_,hNL,hLcover,?_⟩
  · simpa only [dist_eq_norm] using hDcover
  · simpa only [dist_eq_norm] using hDsep
  · apply paper_entropy_bound hn ha hr hr1 hB hs ?_ haspect hDcard' hLcard
    simpa only [finrank_euclideanSpace_fin] using Submodule.finrank_le L

#print axioms paper_joint_nets
#print axioms paper_entropy_bound
end GaussianEllipsoid.PaperExactEntropy
