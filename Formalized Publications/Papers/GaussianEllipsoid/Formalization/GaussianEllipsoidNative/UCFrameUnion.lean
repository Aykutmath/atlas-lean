import UCFrameAlignment
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite-frame union bound with an actual O_K(d) covering exponent and a
positive d² failure exponent after absorption. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCFrameUnion

 def frameBase (j : ℕ) (t : ℝ) : ℝ :=
  1+2*Real.sqrt (j:ℝ)/(min 1 t/(9:ℝ)^j)

 def frameEntropy (K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), (j:ℝ)*Real.log (frameBase j t)

 theorem frameBase_pos (j : ℕ) {t : ℝ} (ht : 0 < t) : 0 < frameBase j t := by
  unfold frameBase
  positivity

 theorem frameBase_one_le (j : ℕ) {t : ℝ} (ht : 0 < t) : 1 ≤ frameBase j t := by
  unfold frameBase
  exact le_add_of_nonneg_right (by positivity)

 theorem frameEntropy_term_le {K j : ℕ} {t : ℝ} (ht : 0 < t) (hj : j ≤ K) :
    (j:ℝ)*Real.log (frameBase j t) ≤ frameEntropy K t := by
  unfold frameEntropy
  exact Finset.single_le_sum
    (fun i _ => mul_nonneg (Nat.cast_nonneg i) (Real.log_nonneg (frameBase_one_le i ht)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

 theorem frame_power_le_exp {d K j : ℕ} {t : ℝ} (ht : 0 < t) (hj : j ≤ K) :
    (frameBase j t)^(d*j) ≤ Real.exp (frameEntropy K t*(d:ℝ)) := by
  have hbase : 0 < frameBase j t := frameBase_pos j ht
  have he : (frameBase j t)^(d*j) = Real.exp (((d*j:ℕ):ℝ)*Real.log (frameBase j t)) := by
    rw [Real.exp_nat_mul,Real.exp_log hbase]
  rw [he]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (frameEntropy_term_le ht hj) (Nat.cast_nonneg d)
  push_cast
  nlinarith

/-- Union over every actual center of every j-frame net, j≤K. -/
theorem finite_frame_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d K : ℕ) (t C : ℝ) (ht : 0 < t)
    (N : (j : Fin (K+1)) → Finset (FrobeniusMatrix d j.val))
    (hcard : ∀ j, ((N j).card:ℝ) ≤ (frameBase j.val t)^(d*j.val))
    (bad : (j : Fin (K+1)) → FrobeniusMatrix d j.val → Set Ω)
    (hprob : ∀ j, ∀ U ∈ N j, μ.real (bad j U) ≤ Real.exp (-C*(d:ℝ)^2)) :
    μ.real (⋃ j, ⋃ U ∈ N j, bad j U) ≤
      (K+1:ℕ)*Real.exp (frameEntropy K t*(d:ℝ))*Real.exp (-C*(d:ℝ)^2) := by
  have hj (j : Fin (K+1)) : μ.real (⋃ U ∈ N j, bad j U) ≤
      Real.exp (frameEntropy K t*(d:ℝ))*Real.exp (-C*(d:ℝ)^2) := by
    calc
      _ ≤ ∑ U ∈ N j, μ.real (bad j U) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _U ∈ N j, Real.exp (-C*(d:ℝ)^2) := Finset.sum_le_sum fun U hU => hprob j U hU
      _ = ((N j).card:ℝ)*Real.exp (-C*(d:ℝ)^2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((hcard j).trans (frame_power_le_exp ht (by omega))) (Real.exp_nonneg _)
  calc
    _ ≤ ∑ j : Fin (K+1), μ.real (⋃ U ∈ N j, bad j U) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin (K+1), Real.exp (frameEntropy K t*(d:ℝ))*Real.exp (-C*(d:ℝ)^2) :=
      Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp; ring

/-- Linear covering entropy is absorbed by any positive quadratic failure
rate. No asymptotic probability input is assumed. -/
theorem linear_entropy_absorption (R A C : ℝ) (hR : 0 < R) (hC : 0 < C) :
    ∀ᶠ d : ℕ in atTop,
      R*Real.exp (A*(d:ℝ))*Real.exp (-C*(d:ℝ)^2) ≤ Real.exp (-(C/2)*(d:ℝ)^2) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (2*(|A|+|Real.log R|)/C),eventually_ge_atTop 1] with d hd hd1
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd1
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hb := (div_le_iff₀ hC).mp hd
  have hm := mul_le_mul_of_nonneg_right hb hd0
  have h1 : A*(d:ℝ) ≤ |A| *(d:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self A) hd0
  have h2 : Real.log R ≤ |Real.log R| *(d:ℝ) := by nlinarith [le_abs_self (Real.log R),abs_nonneg (Real.log R)]
  have hbudget : Real.log R+A*(d:ℝ) ≤ (C/2)*(d:ℝ)^2 := by nlinarith
  calc
    _ = Real.exp (Real.log R+A*(d:ℝ)-C*(d:ℝ)^2) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_add,Real.exp_log hR]
      rw [neg_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

 theorem frame_entropy_absorption (K : ℕ) (t C : ℝ) (hC : 0 < C) :
    ∀ᶠ d : ℕ in atTop,
      (K+1:ℕ)*Real.exp (frameEntropy K t*(d:ℝ))*Real.exp (-C*(d:ℝ)^2) ≤
        Real.exp (-(C/2)*(d:ℝ)^2) :=
  linear_entropy_absorption (K+1:ℕ) (frameEntropy K t) C (by positivity) hC

#print axioms finite_frame_union_bound
#print axioms frame_entropy_absorption
end GaussianEllipsoid.UCFrameUnion
