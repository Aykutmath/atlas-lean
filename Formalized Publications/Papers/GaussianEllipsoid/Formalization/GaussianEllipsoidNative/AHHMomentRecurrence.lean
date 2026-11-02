import AHHCanonicalMoves
import AHHScalarElimination
import Mathlib.Algebra.BigOperators.Field

/-! Normalization and conservative finite-order constants for the AHH word recurrence. -/
noncomputable section
open scoped BigOperators
namespace AHH

/-- Divide the unnormalized trace recurrence by its dimension factor exactly. -/
theorem normalize_recurrence (E : ℕ → ℝ) {D A B : ℝ} (hD : 0 < D) (n : ℕ)
    (h : E (n + 1) ≤ (A / D) * ∑ i ∈ Finset.range n, E i * E (n - i) + B * E n) :
    E (n + 1) / D ≤ A * ∑ i ∈ Finset.range n,
      (E i / D) * (E (n - i) / D) + B * (E n / D) := by
  apply (div_le_iff₀ hD).mpr
  calc
    _ ≤ _ := h
    _ = _ := by
      simp_rw [div_mul_div_comm]
      rw [← Finset.sum_div]
      field_simp

/-- Conservative scalar error estimate, valid uniformly at all finite orders up to `M`.
The intermediate bound `4 J³/H` is already more than sufficient. -/
theorem finite_error_le {H N M : ℝ} (hH : 1 ≤ H) (hN : 0 ≤ N)
    (hNM : N + 1 ≤ M) :
    ((1 + Real.sqrt H) * N / H ^ 2) * (N + 1) ^ 2 +
      ((1 + 1 / Real.sqrt H) / H ^ 2) * (N + 1) ^ 3 ≤
      4 * M ^ 5 / Real.sqrt H := by
  have hHp : 0 < H := by linarith
  have hs : 1 ≤ Real.sqrt H := Real.one_le_sqrt.mpr hH
  have hsp : 0 < Real.sqrt H := by linarith
  have hsH : Real.sqrt H ≤ H := Real.sqrt_le_iff.mpr ⟨hHp.le, by nlinarith⟩
  have hsmall : 1 / Real.sqrt H ≤ 1 := (div_le_one hsp).mpr hs
  have hJ : 0 ≤ N + 1 := by linarith
  have hM : 1 ≤ M := by linarith
  have hc : (1 + Real.sqrt H) * N * (N + 1) ^ 2 +
      (1 + 1 / Real.sqrt H) * (N + 1) ^ 3 ≤ 4 * (N + 1) ^ 3 * H := by
    have h₁ : (1 + Real.sqrt H) * N * (N + 1) ^ 2 ≤
        (2 * H) * (N + 1) * (N + 1) ^ 2 := by
      gcongr <;> linarith
    have h₂ : (1 + 1 / Real.sqrt H) * (N + 1) ^ 3 ≤ 2 * (N + 1) ^ 3 := by
      gcongr; linarith
    have h₃ : 2 * (N + 1) ^ 3 ≤ 2 * (N + 1) ^ 3 * H := by
      nlinarith [pow_nonneg hJ 3]
    nlinarith
  have hpow : (N + 1) ^ 3 ≤ M ^ 5 :=
    (pow_le_pow_left₀ hJ hNM 3).trans (pow_le_pow_right₀ hM (by norm_num))
  calc
    _ = ((1 + Real.sqrt H) * N * (N + 1) ^ 2 +
        (1 + 1 / Real.sqrt H) * (N + 1) ^ 3) / H ^ 2 := by ring
    _ ≤ (4 * (N + 1) ^ 3 * H) / H ^ 2 :=
      (div_le_div_iff_of_pos_right (pow_pos hHp 2)).mpr hc
    _ = 4 * (N + 1) ^ 3 / H := by field_simp
    _ ≤ 4 * M ^ 5 / H := by gcongr
    _ ≤ 4 * M ^ 5 / Real.sqrt H := by
      apply div_le_div_of_nonneg_left (by positivity) hsp hsH

/-- The local word identities and the proved encodings imply the conservative
normalized recurrence used by the generating-sum theorem. -/
theorem normalized_word_recurrence {α : Type*} [Fintype α]
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → S d.L d.R = T d.L * T d.R)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output)
    {H : ℝ} (hH : 1 ≤ H) (m n : ℕ) (hnm : n < m)
    (hsingle : ∀ s : α, ∀ w ∈ words α n, s ∉ w → T (s :: w) = (1 / H ^ 2) * T w)
    (helim : ∀ d ∈ repeatedSplits α n,
      T d.original ≤ ((1 + 1 / Real.sqrt H) / H ^ 2) * S d.L d.R +
        (((1 + Real.sqrt H) * n) / H ^ 2) * ∑ r ∈ d.moves, T r.output) :
    wordSum T (n + 1) / H ^ 2 ≤
      (1 + 1 / Real.sqrt H) * ∑ i ∈ Finset.range n,
        (wordSum T i / H ^ 2) * (wordSum T (n - i) / H ^ 2) +
      ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) *
        (wordSum T n / H ^ 2) := by
  have hHp : 0 < H := by linarith
  have hHsq : 0 < H ^ 2 := pow_pos hHp 2
  have hsp : 0 < Real.sqrt H := Real.sqrt_pos.mpr hHp
  have hr := word_recurrence T S hT hdisjoint hmerge WordSplit.moves n
    (fun d _ r hr => d.mem_moves_original r hr)
    (q := 1 / H ^ 2) (c := (1 + 1 / Real.sqrt H) / H ^ 2)
    (k := ((1 + Real.sqrt H) * n) / H ^ 2)
    (by positivity) (by positivity) (by positivity) hsingle helim
  have hnorm := normalize_recurrence (wordSum T) hHsq n hr
  have he := finite_error_le hH (N := (n : ℝ)) (M := (m : ℝ)) (by positivity)
    (by exact_mod_cast hnm)
  have hnpos : 0 ≤ wordSum T n / H ^ 2 := div_nonneg (wordSum_nonneg T hT n) hHsq.le
  push_cast at hnorm
  push_cast at he
  have hb : (Fintype.card α : ℝ) * (1 / H ^ 2) +
      ((1 + Real.sqrt H) * (n : ℝ) / H ^ 2) * ((n : ℝ) + 1) ^ 2 +
      ((1 + 1 / Real.sqrt H) / H ^ 2) * ((n : ℝ) + 1) ^ 3 ≤
      (Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H := by
    convert add_le_add_right he ((Fintype.card α : ℝ) / H ^ 2) using 1 <;> ring
  exact hnorm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hnpos))

@[simp] theorem words_zero (α : Type*) [Fintype α] : words α 0 = {[]} := by
  classical
  ext w
  simp only [mem_words, Finset.mem_singleton, List.length_eq_zero_iff]

@[simp] theorem wordSum_zero {α : Type*} [Fintype α] (T : List α → ℝ) :
    wordSum T 0 = T [] := by simp [wordSum]

/-- The finite sharp moment bound from explicitly stated local word identities. -/
theorem moment_bound_of_local_identities {α : Type*} [Fintype α]
    (T : List α → ℝ) (S : List α → List α → ℝ) (hT : ∀ w, 0 ≤ T w)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → S d.L d.R = T d.L * T d.R)
    (hmerge : ∀ c : Collision α, S c.left c.right = T c.output)
    {H : ℝ} (hH : 1 ≤ H) (hzero : T [] = H ^ 2) (m : ℕ)
    (hsingle : ∀ n < m, ∀ s : α, ∀ w ∈ words α n,
      s ∉ w → T (s :: w) = (1 / H ^ 2) * T w)
    (helim : ∀ n < m, ∀ d ∈ repeatedSplits α n,
      T d.original ≤ ((1 + 1 / Real.sqrt H) / H ^ 2) * S d.L d.R +
        (((1 + Real.sqrt H) * n) / H ^ 2) * ∑ r ∈ d.moves, T r.output) :
    wordSum T m ≤ H ^ 2 * edgeR (1 + 1 / Real.sqrt H)
      ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) *
      edgeL (1 + 1 / Real.sqrt H)
        ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) ^ m := by
  have hHp : 0 < H := by linarith
  have hHsq : 0 < H ^ 2 := pow_pos hHp 2
  have hsp : 0 < Real.sqrt H := Real.sqrt_pos.mpr hHp
  have hh := moment_le_edge (fun n => wordSum T n / H ^ 2)
    (fun n => div_nonneg (wordSum_nonneg T hT n) hHsq.le)
    (by rw [wordSum_zero, hzero, div_self (ne_of_gt hHsq)])
    (A := 1 + 1 / Real.sqrt H)
    (B := (Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H)
    (by positivity) (by positivity) m
    (fun n hn => by
      simpa only [add_comm] using normalized_word_recurrence T S hT hdisjoint hmerge
        hH m n hn (hsingle n hn) (helim n hn))
  have hh' := (div_le_iff₀ hHsq).mp hh
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh'

/-- Squared one-subsystem loop identities suffice for the full moment bound.
All integration obligations remain explicit local equalities, rather than an assumed recurrence. -/
theorem moment_bound_of_one_subsystem_laws {α : Type*} [Fintype α]
    (f : List α → ℝ) (g : List α → List α → ℝ)
    {H : ℝ} (hH : 1 ≤ H) (hzero : f [] = H) (m : ℕ)
    (hsingle : ∀ n < m, ∀ s : α, ∀ w ∈ words α n,
      s ∉ w → f (s :: w) = f w / H)
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → g d.L d.R = f d.L * f d.R)
    (hmerge : ∀ c : Collision α, g c.left c.right = f c.output)
    (hloop : ∀ n < m, ∀ d ∈ repeatedSplits α n,
      f d.original = (g d.L d.R + ∑ r ∈ d.moves, f r.output) / H) :
    wordSum (fun w => f w ^ 2) m ≤ H ^ 2 * edgeR (1 + 1 / Real.sqrt H)
      ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) *
      edgeL (1 + 1 / Real.sqrt H)
        ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) ^ m := by
  apply moment_bound_of_local_identities (fun w => f w ^ 2) (fun u v => g u v ^ 2)
    (fun w => sq_nonneg (f w))
  · intro d hd
    rw [hdisjoint d hd, mul_pow]
  · intro c
    rw [hmerge c]
  · exact hH
  · rw [hzero]
  · intro n hn s w hw hs
    rw [hsingle n hn s w hw hs, div_pow]
    ring
  · intro n hn d hd
    have hlen := repeatedSplits_length n d hd
    have hlen' : d.original.length - 1 = n := by
      simp only [WordSplit.original, List.length_append, List.length_singleton]
      omega
    have h := word_square_elimination d (fun r => f r.output) (f d.original) (g d.L d.R)
      (by linarith : 0 < H) (hloop n hn d hd)
    simpa only [hlen'] using h

end AHH
