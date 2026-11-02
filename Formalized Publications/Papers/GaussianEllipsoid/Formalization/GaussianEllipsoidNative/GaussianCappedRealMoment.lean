import CappedDeterminantReal
import SelectedRealMoment
import RealGammaRatio
import PaperThetaCap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Reconstructed proof development, 2026-10-03. Not original recovered source.
The proofs below are draft/unverified pending recovered prerequisite compilation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open GaussianTensorMoments GaussianEllipsoid.CappedSimplex
namespace GaussianMixedNormHelpers

/-- Reciprocal caps have a genuine uniform-subset extremizer at every positive
real exponent, with the same infinity convention as the recovered source. -/
theorem reconstructed_extendedRealMoment_le_uniform_subset
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (s : ℝ) (hs : 0 < s) (m : ℕ) (hm : 0 < m)
    {w : κ → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1)
    (T : Finset κ) (hT : T.card = m) :
    extendedRealMoment (Measure.pi (fun _ : κ => μ)) s w ≤
      extendedRealMoment (Measure.pi (fun _ : κ => μ)) s
        (fun i => if i ∈ T then (m : ℝ)⁻¹ else 0) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  apply extendedRealMoment_le_capped_vertex μ (inv_pos.mpr hmR) hs hw
  · constructor
    · intro i
      dsimp only
      by_cases hi : i ∈ T <;> simp [hi, inv_nonneg.mpr hmR.le]
    · simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul, hT]
      exact mul_inv_cancel₀ hmR.ne'
  · have hempty : interior ((m : ℝ)⁻¹)
        (fun i => if i ∈ T then (m : ℝ)⁻¹ else 0) = ∅ := by
      ext i
      simp only [GaussianEllipsoid.CappedSimplex.mem_interior]
      split_ifs <;> simp
    rw [hempty]
    simp

/-- A scalar Bartlett factor estimate at any real inverse exponent ≥1. -/
theorem reconstructed_gamma_factor_bound (q s : ℝ) (hq : 0 < q) (hs : 1 ≤ s) :
    (2 : ℝ)^(-s) * (Real.Gamma (q/2) / Real.Gamma (q/2+s)) ≤ q^(-s) := by
  calc
    _ ≤ (2 : ℝ)^(-s) * (q/2)^(-s) :=
      mul_le_mul_of_nonneg_left
        (gamma_real_inverse_ratio_upper (by positivity : 0 < q/2) hs) (by positivity)
    _ = (2 * (q/2))^(-s) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : 0 ≤ q/2)]
    _ = q^(-s) := by congr 1; ring

/-- Finite nonnegative products commute with a fixed real power. -/
theorem reconstructed_prod_rpow {κ : Type*} [DecidableEq κ]
    (T : Finset κ) (f : κ → ℝ) (hf : ∀ i ∈ T, 0 ≤ f i) (s : ℝ) :
    (∏ i ∈ T, f i)^s = ∏ i ∈ T, (f i)^s := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
      rw [Finset.prod_insert hi, Real.mul_rpow (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        Finset.prod_insert hi, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The descending residual dimensions have factorial product. -/
theorem reconstructed_prod_residual (r : ℕ) :
    (∏ j : Fin r, ((r-j.val : ℕ) : ℝ)) = (r.factorial : ℝ) := by
  have he : (∏ j : Fin r, ((r-j.val : ℕ) : ℝ)) =
      ∏ j : Fin r, ((j.val : ℝ)+1) := by
    rw [← Equiv.prod_comp Fin.revPerm (fun j : Fin r => ((r-j.val : ℕ) : ℝ))]
    apply Finset.prod_congr rfl
    intro j _
    have hnat : r - (Fin.revPerm j).val = j.val + 1 := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    rw [hnat]
    push_cast
    rfl
  rw [he]
  calc
    _ = ∏ k ∈ Finset.range r, ((k:ℝ)+1) :=
      Fin.prod_univ_eq_prod_range (fun k : ℕ => (k:ℝ)+1) r
    _ = _ := by exact_mod_cast Finset.prod_range_add_one_eq_factorial r

/-- The real-exponent Bartlett product bound, retaining odd row dimensions. -/
theorem reconstructed_endpoint_gamma_product_le (r : ℕ) (hr : 2 ≤ r) :
    (∏ j : Fin r, (2:ℝ)^(-((r:ℝ)/2)) *
      (Real.Gamma (((2*r-j.val:ℕ):ℝ)/2-(r:ℝ)/2) /
        Real.Gamma (((2*r-j.val:ℕ):ℝ)/2))) ≤
      ((r.factorial:ℝ))^(-((r:ℝ)/2)) := by
  have hfactor : ∀ j : Fin r,
      (2:ℝ)^(-((r:ℝ)/2)) *
        (Real.Gamma (((2*r-j.val:ℕ):ℝ)/2-(r:ℝ)/2) /
          Real.Gamma (((2*r-j.val:ℕ):ℝ)/2)) ≤
      (((r-j.val:ℕ):ℝ))^(-((r:ℝ)/2)) := by
    intro j
    have hj : j.val ≤ r := by omega
    have hshape : (((2*r-j.val:ℕ):ℝ)/2-(r:ℝ)/2) = ((r-j.val:ℕ):ℝ)/2 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hj]
      push_cast
      ring
    have hshape' : (((2*r-j.val:ℕ):ℝ)/2) = ((r-j.val:ℕ):ℝ)/2 + (r:ℝ)/2 := by
      linarith [hshape]
    rw [hshape, hshape']
    apply reconstructed_gamma_factor_bound
    · exact_mod_cast (show 0 < r-j.val by omega)
    · have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
      linarith
  calc
    _ ≤ ∏ j : Fin r, (((r-j.val:ℕ):ℝ))^(-((r:ℝ)/2)) := by
      apply Finset.prod_le_prod
      · intro j _
        apply mul_nonneg (by positivity)
        apply div_nonneg
        · apply (Real.Gamma_pos_of_pos _).le
          rw [Nat.cast_sub (by omega)]
          have hj : (j.val:ℝ) < r := by exact_mod_cast j.isLt
          push_cast
          linarith
        · apply (Real.Gamma_pos_of_pos _).le
          have hj : 0 < 2*r-j.val := by omega
          positivity
      · exact fun j _ => hfactor j
    _ = _ := by
      rw [← reconstructed_prod_rpow Finset.univ
        (fun j : Fin r => ((r-j.val:ℕ):ℝ)) (fun _ _ => Nat.cast_nonneg _) _,
        reconstructed_prod_residual]

/-- Scaling the endpoint Bartlett product gives the exponential constant. -/
theorem reconstructed_endpoint_scaled_gamma_le (r : ℕ) (hr : 0 < r) :
    ((((2*(r:ℝ))⁻¹)^r)^(-((r:ℝ)/2)) *
      ∏ j : Fin r, (2:ℝ)^(-((r:ℝ)/2)) *
        (Real.Gamma (((2*r-j.val:ℕ):ℝ)/2-(r:ℝ)/2) /
          Real.Gamma (((2*r-j.val:ℕ):ℝ)/2))) ≤
      (2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2)) := by
  by_cases hr2 : 2 ≤ r
  · calc
      _ ≤ ((((2*(r:ℝ))⁻¹)^r)^(-((r:ℝ)/2))) *
          (r.factorial:ℝ)^(-((r:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left (reconstructed_endpoint_gamma_product_le r hr2)
          (by positivity)
      _ = ((2*(r:ℝ))^r/(r.factorial:ℝ))^((r:ℝ)/2) := by
        rw [inv_pow, Real.rpow_neg_eq_inv_rpow, inv_inv,
          Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
        rfl
      _ ≤ ((2*Real.exp 1)^r)^((r:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) (scaled_factorial_ratio_le r) (by positivity)
      _ = _ := (Real.rpow_natCast_mul (by positivity) r ((r:ℝ)/2)).symm
  · have hr1 : r = 1 := by omega
    subst r
    norm_num only [Nat.cast_one, mul_one, pow_one, Fin.prod_univ_one,
      Fin.val_zero, Nat.sub_zero, Nat.cast_ofNat, show (2:ℝ)/2 = 1 by norm_num,
      show (1:ℝ)-1/2 = 1/2 by norm_num, Real.Gamma_one, div_one,
      Real.Gamma_one_half_eq]
    have hscale : ((1/2:ℝ))^(-(1/2:ℝ)) * (2:ℝ)^(-(1/2:ℝ)) = 1 := by
      rw [← Real.mul_rpow (by positivity : (0:ℝ) ≤ (1/2:ℝ))
        (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [← mul_assoc, hscale, one_mul, ← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    have hp : Real.pi < 4 := Real.pi_lt_four
    have he : 2 < Real.exp 1 := Real.exp_one_gt_two
    linarith

/-- Endpoint-cap moment with the true real exponent r/2 for every positive
row dimension, including one row and odd dimensions. -/
theorem gaussian_capped_real_moment
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : ℕ) (hr : 0 < r) {w : κ → ℝ}
    (hw : w ∈ slice ((2*(r:ℝ))⁻¹) 1) :
    extendedRealMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r)))
        ((r:ℝ)/2) w ≤ ENNReal.ofReal ((2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2))) := by
  have hw' : w ∈ slice (((2*r:ℕ):ℝ)⁻¹) 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hw
  obtain ⟨T, hT⟩ := exists_card_subset_of_reciprocal_cap (by omega : 0 < 2*r) hw'
  have hcard : Fintype.card T = 2*r := by rw [Fintype.card_coe, hT]
  let e : Fin (2*r) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  have hshape : ∀ j : Fin r, (r:ℝ)/2 < ((2*r-j.val:ℕ):ℝ)/2 := by
    intro j
    rw [Nat.cast_sub (by omega)]
    have hj : (j.val:ℝ) < r := by exact_mod_cast j.isLt
    push_cast
    linarith
  calc
    _ ≤ extendedRealMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r)))
        ((r:ℝ)/2) (fun i => if i ∈ T then ((2*r:ℕ):ℝ)⁻¹ else 0) :=
      reconstructed_extendedRealMoment_le_uniform_subset _ _ (by positivity) _
        (by omega) hw' T hT
    _ = ENNReal.ofReal (((((2*(r:ℝ))⁻¹)^r)^(-((r:ℝ)/2))) *
        ∏ j : Fin r, (2:ℝ)^(-((r:ℝ)/2)) *
          (Real.Gamma (((2*r-j.val:ℕ):ℝ)/2-(r:ℝ)/2) /
            Real.Gamma (((2*r-j.val:ℕ):ℝ)/2))) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        selected_uniform_extended_real_moment r (2*r) (by omega)
          ((r:ℝ)/2) (((2*r:ℕ):ℝ)⁻¹) (by positivity) (by positivity) hshape T e
    _ ≤ _ := ENNReal.ofReal_le_ofReal (reconstructed_endpoint_scaled_gamma_le r hr)

end GaussianMixedNormHelpers

#print axioms GaussianMixedNormHelpers.gaussian_capped_real_moment
