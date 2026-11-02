import ActualCrossScalars
import AdaptedPrefixWitness

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Concrete actual-group scalar bounds and the fully constructed prefix
witness martingale give the required quadratic/log Gaussian tail. A fixed
permutation is allowed, so ordered dyadic supports can be fed in directly. -/
theorem actual_postprefix_cross_tail {ι : Type*} [Fintype ι] {n d : ℕ}
    (u witnessCoefficients : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hd : 0 < (d:ℝ)) (hlog : 0 < Real.log (d:ℝ))
    (hS : ∀ r, p ≤ r → r < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups r)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (e : Equiv.Perm (Fin n)) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | prefixWitnessCross witnessCoefficients
        (fun i => postprefixCoefficients u amp groups T p (e i) / Real.sqrt d) lo hi X ≤
          -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} ≤
      Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ))) := by
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let w := postprefixCoefficients u amp groups T p
  let α := 131072*(T:ℝ)*Real.log (d:ℝ)/(d:ℝ)
  let V := (2:ℝ)^17*T*Real.log (d:ℝ)/(d:ℝ)*M^2
  let b := (2:ℝ)^18*T*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)*M
  let x := (1/2:ℝ)^24*M*Real.sqrt d
  let v : Fin n → ℝ := fun i => w (e i)/Real.sqrt d
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hα : 0 < α := by dsimp [α]; positivity
  have hbounds := actual_postprefix_log_cap_energy u amp groups T p hT hreg d hd hlog hS
  have hparams := actual_cross_chernoff_exponent d T M hd hT' hM hlog
  change 0 < V ∧ 0 < b ∧ 0 ≤ x ∧ _ at hparams
  have hcoef : ∀ i, (v i)^2 ≤ b^2/2 := by
    intro i
    have hc : |v i| ≤ b/2 := by
      dsimp [v]
      rw [abs_div, abs_of_pos hs]
      apply (div_le_iff₀ hs).mpr
      have hh := hbounds.1 (e i)
      have heq : b/2*Real.sqrt (d:ℝ) = α*M := by
        dsimp [b, α]
        field_simp [hd.ne', hs.ne']
        ring
      rw [heq]
      exact hh
    have hb0 := hparams.2.1
    have hh := pow_le_pow_left₀ (abs_nonneg (v i)) hc 2
    rw [sq_abs] at hh
    nlinarith [sq_nonneg b]
  have hsum : (∑ i, (v i)^2) = (∑ i, (w i)^2)/(d:ℝ) := by
    dsimp [v]
    simp_rw [div_pow, Real.sq_sqrt hd.le]
    rw [← Finset.sum_div, Equiv.sum_comp e (fun i => (w i)^2)]
  have hvar : (2*(d/4):ℕ)*∑ i, (v i)^2 ≤ V := by
    rw [hsum]
    have hdim : ((2*(d/4):ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast (show 2*(d/4) ≤ d by omega)
    have he := hbounds.2
    change (∑ i, (w i)^2) ≤ α*M^2 at he
    have hn : 0 ≤ ∑ i, (w i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc
      ((2*(d/4):ℕ):ℝ)*((∑ i, (w i)^2)/(d:ℝ)) ≤
          (d:ℝ)*((∑ i, (w i)^2)/(d:ℝ)) :=
        mul_le_mul_of_nonneg_right hdim (div_nonneg hn hd.le)
      _ = ∑ i, (w i)^2 := mul_div_cancel₀ _ hd.ne'
      _ ≤ α*M^2 := he
      _ = V := by norm_num [α, V]
  have hp := prefixWitnessCross_lower_tail (r:=2*(d/4)) (q:=2*(d/4)) witnessCoefficients v lo hi hlo hsep
    V b x hparams.1 hparams.2.1 hparams.2.2.1 hcoef hvar
  rw [hparams.2.2.2] at hp
  exact hp

end GaussianEllipsoidCandidate
