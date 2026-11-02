import ClippingConsequences
import FinalPassageParameters
import FinalPassageScalar
import GaussianLocalizedUnconditional
import GaussianExtractedRowsLaw

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.Localized
open GaussianMixedNormHelpers GaussianEllipsoidFinalPassage
open GaussianTensorMoments GaussianBilinearTransport
open scoped BigOperators Topology

namespace GaussianEllipsoidStandalone

/-- Explicit finite-vector infimal mixed norm with the paper's exact weights. -/
def mixedNorm (η : ℝ) (d n : ℕ) (y : Fin n → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ u v : Fin n → ℝ, y = u + v ∧
    w = η * Real.sqrt d * (∑ i, |u i|) + d * Real.sqrt (∑ i, v i ^ 2)}

theorem mixedNorm_eq_infimalCost (η : ℝ) (d n : ℕ) (y : Fin n → ℝ) :
    mixedNorm η d n y = infimalCost (η * Real.sqrt d) d y := rfl

theorem l2_eq_norm {n : ℕ} (y : Coeff n) : l2 (fun i => y i) = ‖y‖ := by
  apply (sq_eq_sq₀ (l2_nonneg _) (norm_nonneg _)).mp
  rw [l2_sq, PiLp.norm_sq_eq_of_L2]
  simp [energy, Real.norm_eq_abs]

def asCoeff {n : ℕ} (y : Fin n → ℝ) : Coeff n := (WithLp.equiv 2 _).symm y

@[simp] theorem asCoeff_apply {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    asCoeff y i = y i := rfl

@[simp] theorem asCoeff_add {n : ℕ} (u v : Fin n → ℝ) :
    asCoeff (u + v) = asCoeff u + asCoeff v := rfl

@[simp] theorem l2_asCoeff {n : ℕ} (y : Fin n → ℝ) : l2 y = ‖asCoeff y‖ :=
  l2_eq_norm _

theorem mixedNorm_nonneg {η : ℝ} (hη : 0 ≤ η) (d n : ℕ) (y : Fin n → ℝ) :
    0 ≤ mixedNorm η d n y := by
  rw [mixedNorm_eq_infimalCost]
  apply le_csInf
  · exact ⟨_, y, 0, by simp, rfl⟩
  · rintro w ⟨u,v,_,rfl⟩
    exact add_nonneg (mul_nonneg (mul_nonneg hη (Real.sqrt_nonneg _)) (l1_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (l2_nonneg _))

theorem nuclear_tail_bound {n r d : ℕ} (hrd : r ≤ d)
    (T : Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (hT : ∀ x, ‖T x‖ ≤ 96 * Real.sqrt d * ‖x‖) (v : Coeff n) :
    spectralNuclearNorm (T v) ≤ 96 * d * ‖v‖ := by
  have hs : Real.sqrt (r:ℝ) ≤ Real.sqrt (d:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hrd)
  calc
    _ ≤ Real.sqrt r * ‖T v‖ := spectralNuclear_le_sqrt_dim_mul_frobenius _
    _ ≤ Real.sqrt d * (96 * Real.sqrt d * ‖v‖) :=
      mul_le_mul hs (hT v) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = 96*d*‖v‖ := by
      calc
        _ = 96 * (Real.sqrt (d:ℝ))^2 * ‖v‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]

/-- Deterministic Section 11 assembly. Both probabilistic input events are
literal events of the actual linear observation, not renamed assumptions. -/
theorem mixed_lower_of_three_events {Ω : Type*} {n r d : ℕ}
    (hd : 0 < d) (hrd : r ≤ d) (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    {η cH cS : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hcH : 0 ≤ cH)
    (ω : Ω)
    (hcont : ω ∈ frobeniusContinuity T 96 d)
    (hhead : ∀ (I : Finset (Fin n)) (u : Coeff n),
      (I.card:ℝ) ≤ (d:ℝ)/η^2 → (∀ i ∉ I, u i = 0) →
      cH * (η*Real.sqrt d*(∑ i, |u i|)) ≤ spectralNuclearNorm (T ω u))
    (hsmall : ω ∉ homogeneousBad T (1/η) (2*η) 1 (1/η^2) cS d)
    (y : Fin n → ℝ) :
    min cS (cH*(1-2*η)-96*(2*η)) * mixedNorm η d n y ≤
      spectralNuclearNorm (T ω (asCoeff y)) := by
  classical
  let M := mixedNorm η d n y
  have hM : 0 ≤ M := mixedNorm_nonneg hη.le d n y
  by_cases hy : y = 0
  · subst y
    have hzero : mixedNorm η d n (0 : Fin n → ℝ) = 0 := by
      apply le_antisymm _ (mixedNorm_nonneg hη.le d n 0)
      rw [mixedNorm_eq_infimalCost]
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro w ⟨u,v,_,rfl⟩
        exact add_nonneg (mul_nonneg (mul_nonneg hη.le (Real.sqrt_nonneg _)) (l1_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (l2_nonneg _))
      · exact ⟨0,0,by simp,by simp [l1,l2,energy]⟩
    simp only [hzero, mul_zero]
    exact spectralNuclear_nonneg _
  have hMp : 0 < M := by
    have hl := mixed_cost_lower hd hη.le hη1 y
    have hp := mul_pos (mul_pos hη (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)))
      (l2_pos_of_ne_zero hy)
    exact hp.trans_le hl
  obtain ⟨I,U,V,hyUV,hU,hV,hI,hdef,hheadM,htail,hcap⟩ :=
    exists_mixed_disjoint_decomposition hd hη y
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hMdef : infimalCost (η*Real.sqrt d) d y = M := rfl
  rw [hMdef] at hdef hheadM htail hcap
  have hnorm : l2 V = ‖asCoeff V‖ := l2_asCoeff V
  have huvn : asCoeff y = asCoeff U + asCoeff V := by rw [hyUV, asCoeff_add]
  apply combine_branches (M := M) (t := d*l2 V) (beta := 2*η) hM
  · intro hlarge
    have hq : 0 < M/(d:ℝ) := div_pos hMp hdR
    have hbound : cS*M ≤ spectralNuclearNorm (T ω (asCoeff y)) := by
      apply le_of_not_gt
      intro hn
      apply hsmall
      refine ⟨M/d,hq,I,?_,asCoeff U,asCoeff V,hU,hV,?_,?_,?_,?_,?_⟩
      · simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hI
      · change l1 U ≤ (1/η)*(M/d)*Real.sqrt d
        have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdR
        calc
          l1 U ≤ M/(η*Real.sqrt d) := (le_div_iff₀ (mul_pos hη hs)).mpr (by nlinarith)
          _ = (1/η)*(M/d)*Real.sqrt d := by
            field_simp [hdR.ne']
            nlinarith [Real.sq_sqrt hdR.le]
      · rw [← hnorm]
        calc
          2*η*(M/d) = (2*η*M)/d := by ring
          _ ≤ l2 V := (div_le_iff₀ hdR).mpr (by nlinarith)
      · rw [one_mul, ← hnorm]
        apply (le_div_iff₀ hdR).mpr
        simpa [mul_comm] using htail
      · apply (coordinate_cap_iff _ hdR.le).mp
        intro i
        have hh : η*M/d ≤ l2 V := by
          have hmη : 0 ≤ η*M := mul_nonneg hη.le hM
          apply (div_le_iff₀ hdR).mpr
          nlinarith
        exact (hcap i).trans (by simpa [hnorm] using hh)
      · rw [← huvn]
        have hc : cS*(M/(d:ℝ))*(d:ℝ) = cS*M := by field_simp
        rw [hc]
        exact hn
    exact hbound
  · intro htailSmall
    have hH := hhead I (asCoeff U) hI hU
    have hH' : cH*(M-d*l2 V) ≤ spectralNuclearNorm (T ω (asCoeff U)) :=
      (mul_le_mul_of_nonneg_left hdef hcH).trans hH
    have hT := nuclear_tail_bound hrd (T ω) hcont (asCoeff V)
    rw [← hnorm] at hT
    have htri := spectralNuclear_add_le (T ω (asCoeff y)) (-(T ω (asCoeff V)))
    have heq : T ω (asCoeff y) + -(T ω (asCoeff V)) = T ω (asCoeff U) := by
      rw [huvn, map_add]; abel
    rw [heq, spectralNuclear_neg] at htri
    exact small_tail_scalar hcH (by norm_num) htailSmall.le hH'
      (by convert hT using 1 <;> ring) (by linarith)

end GaussianEllipsoidStandalone
