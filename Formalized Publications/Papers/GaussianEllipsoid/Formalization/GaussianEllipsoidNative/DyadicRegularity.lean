import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace GaussianEllipsoidCandidate

open Finset

/-- Finite geometric tails suffice even when coefficient dynamic range is arbitrary. -/
theorem finite_geometric_domination (f : ℕ → ℝ) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (m n : ℕ)
    (hf : ∀ j ∈ Finset.Ico m n, f j ≤ C * q ^ j) :
    ∑ j ∈ Finset.Ico m n, f j ≤ C * q ^ m / (1 - q) := by
  calc
    ∑ j ∈ Finset.Ico m n, f j ≤ ∑ j ∈ Finset.Ico m n, C * q ^ j :=
      Finset.sum_le_sum hf
    _ = C * ∑ j ∈ Finset.Ico m n, q ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (q ^ m / (1 - q)) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq hq1) hC
    _ = C * q ^ m / (1 - q) := by ring

/-- A dyadic group has omitted l1 mass at most 8 lambda S 2^(-T). -/
theorem dyadic_omitted_mass (f : ℕ → ℝ) (amp S : ℝ)
    (ha : 0 ≤ amp) (hS : 0 ≤ S) (T N : ℕ)
    (hf : ∀ j ∈ Finset.Ico T N, f j ≤ 4 * amp * S * (1 / 2 : ℝ) ^ j) :
    ∑ j ∈ Finset.Ico T N, f j ≤ 8 * amp * S * (1 / 2 : ℝ) ^ T := by
  have h := finite_geometric_domination f (4 * amp * S) (1 / 2) (by positivity)
      (by norm_num) (by norm_num) T N hf
  convert h using 1 <;> ring

/-- Sum of the energies of retained dyadic bins. -/
theorem dyadic_energy_sum (f : ℕ → ℝ) (amp S : ℝ)
    (hS : 0 ≤ S) (T : ℕ)
    (hf : ∀ j ∈ Finset.range T, f j ≤ 8 * amp ^ 2 * S * (1 / 4 : ℝ) ^ j) :
    ∑ j ∈ Finset.range T, f j ≤ (32 / 3 : ℝ) * amp ^ 2 * S := by
  have hf' : ∀ j ∈ Finset.Ico 0 T, f j ≤ 8 * amp ^ 2 * S * (1 / 4 : ℝ) ^ j := by
    simpa using hf
  have h := finite_geometric_domination f (8 * amp ^ 2 * S) (1 / 4) (by positivity)
      (by norm_num) (by norm_num) 0 T hf'
  norm_num at h
  convert h using 1 <;> ring

/-- Dyadic l1 mass bound without any dependence on the number of retained levels. -/
theorem dyadic_mass_sum (f : ℕ → ℝ) (amp S : ℝ)
    (ha : 0 ≤ amp) (hS : 0 ≤ S) (T : ℕ)
    (hf : ∀ j ∈ Finset.range T, f j ≤ 4 * amp * S * (1 / 2 : ℝ) ^ j) :
    ∑ j ∈ Finset.range T, f j ≤ 8 * amp * S := by
  have hf' : ∀ j ∈ Finset.Ico 0 T, f j ≤ 4 * amp * S * (1 / 2 : ℝ) ^ j := by
    simpa using hf
  have h := finite_geometric_domination f (4 * amp * S) (1 / 2) (by positivity)
      (by norm_num) (by norm_num) 0 T hf'
  norm_num at h
  convert h using 1 <;> ring

/-- All rational effective-support and cap bounds of one regular dyadic group.
The hypotheses are precisely the mass/energy bounds proved from its bins. -/
theorem dyadic_effective_support (amp S m Q cap : ℝ)
    (ha : 0 < amp) (hS : 0 < S)
    (hmlo : amp * S ≤ m) (hmhi : m ≤ 8 * amp * S)
    (hQlo : amp ^ 2 * S ≤ Q) (hQhi : Q ≤ (32 / 3 : ℝ) * amp ^ 2 * S)
    (hcap : cap ≤ 2 * amp) :
    0 < m ∧ 0 < Q ∧
    (3 / 32 : ℝ) * S ≤ m ^ 2 / Q ∧
    m ^ 2 / Q ≤ 64 * S ∧
    cap ≤ 16 * Q / m ∧
    Q ≤ (32 / 3 : ℝ) * m ^ 2 / S ∧
    cap ≤ 2 * m / S := by
  have hm : 0 < m := lt_of_lt_of_le (mul_pos ha hS) hmlo
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (sq_pos_of_pos ha) hS) hQlo
  have hm2lo : (amp * S) ^ 2 ≤ m ^ 2 := sq_le_sq₀ (by positivity) hm.le |>.2 hmlo
  have hm2hi : m ^ 2 ≤ (8 * amp * S) ^ 2 := sq_le_sq₀ hm.le (by positivity) |>.2 hmhi
  refine ⟨hm, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hQ).2
    have hs := mul_le_mul_of_nonneg_left hQhi hS.le
    nlinarith
  · apply (div_le_iff₀ hQ).2
    have hs := mul_le_mul_of_nonneg_left hQlo hS.le
    nlinarith
  · apply (le_div_iff₀ hm).2
    have hmul := mul_le_mul_of_nonneg_right hcap hm.le
    have hmass := mul_le_mul_of_nonneg_left hmhi (by positivity : 0 ≤ 2 * amp)
    nlinarith
  · apply (le_div_iff₀ hS).2
    have hs := mul_le_mul_of_nonneg_right hQhi hS.le
    nlinarith
  · apply (le_div_iff₀ hS).2
    have hmul := mul_le_mul_of_nonneg_right hcap hS.le
    nlinarith

/-- Coordinate magnitude bounds imply the corresponding mass bound on one bin. -/
theorem bin_mass_le {ι : Type*} (I : Finset ι) (u : ι → ℝ)
    (B : ℝ) (hB : ∀ i ∈ I, |u i| ≤ B) :
    ∑ i ∈ I, |u i| ≤ (I.card : ℝ) * B := by
  calc
    ∑ i ∈ I, |u i| ≤ ∑ _i ∈ I, B := Finset.sum_le_sum hB
    _ = (I.card : ℝ) * B := by simp [nsmul_eq_mul]

/-- Coordinate magnitude bounds imply the energy bound on one bin. -/
theorem bin_energy_le {ι : Type*} (I : Finset ι) (u : ι → ℝ)
    (B : ℝ) (hBnn : 0 ≤ B) (hB : ∀ i ∈ I, |u i| ≤ B) :
    ∑ i ∈ I, (u i)^2 ≤ (I.card : ℝ) * B^2 := by
  calc
    ∑ i ∈ I, (u i)^2 ≤ ∑ _i ∈ I, B^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (sq_le_sq₀ (abs_nonneg (u i)) hBnn).2 (hB i hi)
      simpa using h
    _ = (I.card : ℝ) * B^2 := by simp [nsmul_eq_mul]

/-- Actual finite coefficient bins imply both dyadic upper bounds. No bound
on their depth N is required, and empty intervening levels are permitted. -/
theorem dyadic_bins_upper {ι : Type*} (bins : ℕ → Finset ι) (u : ι → ℝ)
    (amp S : ℝ) (ha : 0 ≤ amp) (hS : 0 ≤ S) (N : ℕ)
    (hcard : ∀ j ∈ Finset.range N, ((bins j).card : ℝ) ≤ 2 * S)
    (hcap : ∀ j ∈ Finset.range N, ∀ i ∈ bins j,
      |u i| ≤ 2 * amp * (1 / 2 : ℝ)^j) :
    (∑ j ∈ Finset.range N, ∑ i ∈ bins j, |u i|) ≤ 8 * amp * S ∧
    (∑ j ∈ Finset.range N, ∑ i ∈ bins j, (u i)^2) ≤
      (32 / 3 : ℝ) * amp^2 * S := by
  constructor
  · apply dyadic_mass_sum _ amp S ha hS N
    intro j hj
    calc
      ∑ i ∈ bins j, |u i| ≤ ((bins j).card : ℝ) * (2 * amp * (1 / 2 : ℝ)^j) :=
        bin_mass_le _ _ _ (hcap j hj)
      _ ≤ (2 * S) * (2 * amp * (1 / 2 : ℝ)^j) :=
        mul_le_mul_of_nonneg_right (hcard j hj) (by positivity)
      _ = 4 * amp * S * (1 / 2 : ℝ)^j := by ring
  · apply dyadic_energy_sum _ amp S hS N
    intro j hj
    have hp : ((1 / 2 : ℝ)^j)^2 = (1 / 4 : ℝ)^j := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    calc
      ∑ i ∈ bins j, (u i)^2 ≤ ((bins j).card : ℝ) * (2 * amp * (1 / 2 : ℝ)^j)^2 :=
        bin_energy_le _ _ _ (by positivity) (hcap j hj)
      _ ≤ (2 * S) * (2 * amp * (1 / 2 : ℝ)^j)^2 :=
        mul_le_mul_of_nonneg_right (hcard j hj) (sq_nonneg _)
      _ = 8 * amp^2 * S * (1 / 4 : ℝ)^j := by
        simp only [mul_pow, hp]
        ring

/-- A nonempty base bin gives the mass and energy lower bounds. -/
theorem dyadic_bins_lower {ι : Type*} (bins : ℕ → Finset ι) (u : ι → ℝ)
    (amp : ℝ) (ha : 0 ≤ amp) (N : ℕ) (hN : 0 < N)
    (hbase : ∀ i ∈ bins 0, amp ≤ |u i|) :
    amp * ((bins 0).card : ℝ) ≤ (∑ j ∈ Finset.range N, ∑ i ∈ bins j, |u i|) ∧
    amp^2 * ((bins 0).card : ℝ) ≤ (∑ j ∈ Finset.range N, ∑ i ∈ bins j, (u i)^2) := by
  constructor
  · calc
      amp * ((bins 0).card : ℝ) = ∑ _i ∈ bins 0, amp := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ bins 0, |u i| := Finset.sum_le_sum hbase
      _ ≤ ∑ j ∈ Finset.range N, ∑ i ∈ bins j, |u i| :=
        Finset.single_le_sum (f := fun j => ∑ i ∈ bins j, |u i|) (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg (u i)) (Finset.mem_range.mpr hN)
  · calc
      amp^2 * ((bins 0).card : ℝ) = ∑ _i ∈ bins 0, amp^2 := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ bins 0, (u i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := (sq_le_sq₀ ha (abs_nonneg (u i))).2 (hbase i hi)
        simpa using h
      _ ≤ ∑ j ∈ Finset.range N, ∑ i ∈ bins j, (u i)^2 :=
        Finset.single_le_sum (f := fun j => ∑ i ∈ bins j, (u i)^2) (fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg (u i)) (Finset.mem_range.mpr hN)

#print axioms bin_mass_le
#print axioms bin_energy_le
#print axioms dyadic_bins_upper
#print axioms dyadic_bins_lower
#print axioms finite_geometric_domination
#print axioms dyadic_omitted_mass
#print axioms dyadic_energy_sum
#print axioms dyadic_mass_sum
#print axioms dyadic_effective_support

end GaussianEllipsoidCandidate

