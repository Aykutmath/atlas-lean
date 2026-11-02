import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BMFiniteSoftMin
variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The actual minimum on a finite nonempty state set. -/
def ground (E : κ → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty E

/-- Uniform-prior negative free energy with inverse temperature β and volume v.
For BM the volume is d² and E is the normalized empirical potential. -/
def freeEnergy (β v : ℝ) (E : κ → ℝ) : ℝ :=
  -Real.log ((∑ a, Real.exp (-β*v*E a))/(Fintype.card κ : ℝ))/(β*v)

theorem ground_le (E : κ → ℝ) (a : κ) : ground E ≤ E a :=
  Finset.inf'_le E (Finset.mem_univ a)

theorem ground_attained (E : κ → ℝ) : ∃ a, ground E = E a := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty E
  exact ⟨a,ha⟩

/-- Sharp finite-state soft-min bounds for the actual log partition. -/
theorem ground_le_freeEnergy_le (β v : ℝ) (hβ : 0 < β) (hv : 0 < v)
    (E : κ → ℝ) :
    ground E ≤ freeEnergy β v E ∧
      freeEnergy β v E ≤ ground E + Real.log (Fintype.card κ : ℝ)/(β*v) := by
  let Z := ∑ a, Real.exp (-β*v*E a)
  let N : ℝ := Fintype.card κ
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast (Fintype.card_pos (α := κ))
  have hZ : 0 < Z := Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  have hβv : 0 < β*v := mul_pos hβ hv
  have hu : Z / N ≤ Real.exp (-β*v*ground E) := by
    apply (div_le_iff₀ hN).2
    calc
      Z ≤ ∑ _a : κ, Real.exp (-β*v*ground E) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Real.exp_le_exp.mpr (by nlinarith [ground_le E a])
      _ = _ := by simp [N]; ring
  obtain ⟨a,ha⟩ := ground_attained E
  have hl : Real.exp (-β*v*ground E) ≤ Z := by
    rw [ha]
    exact Finset.single_le_sum (fun b _ => (Real.exp_pos (-β*v*E b)).le) (Finset.mem_univ a)
  have hlogu := Real.log_le_log (div_pos hZ hN) hu
  rw [Real.log_exp] at hlogu
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  rw [Real.log_exp] at hlogl
  constructor
  · change ground E ≤ -Real.log (Z/N)/(β*v)
    apply (le_div_iff₀ hβv).2
    nlinarith
  · change -Real.log (Z/N)/(β*v) ≤ ground E + Real.log N/(β*v)
    rw [Real.log_div (ne_of_gt hZ) (ne_of_gt hN)]
    apply (div_le_iff₀ hβv).2
    have he : (ground E + Real.log N/(β*v))*(β*v) = ground E*(β*v)+Real.log N := by
      field_simp
    rw [he]
    nlinarith

/-- The soft-min error is logarithmic in state count, not polynomial. -/
theorem abs_freeEnergy_sub_ground_le (β v : ℝ) (hβ : 0 < β) (hv : 0 < v)
    (E : κ → ℝ) :
    |freeEnergy β v E-ground E| ≤ Real.log (Fintype.card κ : ℝ)/(β*v) := by
  obtain ⟨hl,hu⟩ := ground_le_freeEnergy_le β v hβ hv E
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

/-- Finite soft-min comparison already in the two-law triangle form. -/
theorem ground_comparison_of_freeEnergy {gW gG fW fG δ ε : ℝ}
    (hW : |gW-fW| ≤ δ) (hG : |gG-fG| ≤ δ) (hF : |fW-fG| ≤ ε) :
    |gW-gG| ≤ ε+2*δ := by
  calc
    _ = |(gW-fW)+(fW-fG)+(fG-gG)| := by congr 1; ring
    _ ≤ |gW-fW|+|fW-fG|+|fG-gG| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ δ+ε+δ := by rw [abs_sub_comm fG gG]; gcongr
    _ = _ := by ring

#print axioms ground_le_freeEnergy_le
#print axioms abs_freeEnergy_sub_ground_le
end BMFiniteSoftMin
