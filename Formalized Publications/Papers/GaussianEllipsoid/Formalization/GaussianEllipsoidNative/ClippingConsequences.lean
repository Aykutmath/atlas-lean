import Clipping

noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

namespace GaussianMixedNormHelpers

theorem abs_add_eq_of_product_nonneg {x y : ℝ} (h : 0 ≤ x * y) :
    |x + y| = |x| + |y| := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · simp [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx hy)]
    · have hzero : x = 0 := by nlinarith
      simp [hzero]
  · by_cases hy : 0 ≤ y
    · have hzero : y = 0 := by nlinarith
      simp [hzero]
    · simp [abs_of_nonpos (le_of_not_ge hx), abs_of_nonpos (le_of_not_ge hy),
        abs_of_nonpos (add_nonpos (le_of_not_ge hx) (le_of_not_ge hy)), add_comm]

theorem abs_eq_of_matching {t u v : ℝ} (ht : 0 ≤ t) (hu : u ≠ 0)
    (hmatch : v * u = t * |u|) : |v| = t := by
  have h := congrArg abs hmatch
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_abs] at h
  exact mul_right_cancel₀ (abs_ne_zero.mpr hu) h

variable {ι : Type*} [Fintype ι]

theorem l2_le_l1 (y : ι → ℝ) : l2 y ≤ l1 y := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => |y i|) (fun i _ => abs_nonneg (y i))
  simp only [sq_abs] at h
  change energy y ≤ l1 y ^ 2 at h
  rw [← l2_sq] at h
  nlinarith [l2_nonneg y, l1_nonneg y]

theorem l2_add_le (u v : ι → ℝ) : l2 (u + v) ≤ l2 u + l2 v := by
  have he : l2 (u + v) ^ 2 = l2 u ^ 2 + 2 * (∑ i, u i * v i) + l2 v ^ 2 := by
    simp [l2_sq, energy, Pi.add_apply, add_sq, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  nlinarith [pairing_le_l2 u v, l2_nonneg (u + v), l2_nonneg u, l2_nonneg v]

theorem l2_pos_of_ne_zero {y : ι → ℝ} (hy : y ≠ 0) : 0 < l2 y := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have he : energy y = 0 := le_antisymm (le_of_not_gt h) (energy_nonneg y)
  apply hy
  ext i
  have hterm : y i ^ 2 ≤ energy y :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  rw [he] at hterm
  simp only [Pi.zero_apply]
  nlinarith [sq_nonneg (y i)]

theorem infimalCost_lower_l2 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (y : ι → ℝ) : a * l2 y ≤ infimalCost a b y := by
  apply le_csInf
  · exact ⟨a * l1 y + b * l2 0, y, 0, by simp, rfl⟩
  · rintro w ⟨u, v, hy, rfl⟩
    rw [hy]
    have h1 := mul_le_mul_of_nonneg_left (l2_add_le u v) ha
    have h2 := mul_le_mul_of_nonneg_left (l2_le_l1 u) ha
    have h3 := mul_le_mul_of_nonneg_right hab (l2_nonneg v)
    nlinarith

theorem infimalCost_pos_of_ne_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {y : ι → ℝ} (hy : y ≠ 0) : 0 < infimalCost a b y :=
  lt_of_lt_of_le (mul_pos ha (l2_pos_of_ne_zero hy)) (infimalCost_lower_l2 ha.le hab y)

variable [DecidableEq ι]

def restrictCoords (I : Finset ι) (z : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ I then z i else 0

theorem restrict_add_compl (I : Finset ι) (z : ι → ℝ) :
    restrictCoords I z + restrictCoords Iᶜ z = z := by
  ext i
  by_cases hi : i ∈ I <;> simp [restrictCoords, hi]

theorem energy_restrict_add_compl (I : Finset ι) (z : ι → ℝ) :
    energy (restrictCoords I z) + energy (restrictCoords Iᶜ z) = energy z := by
  unfold energy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I <;> simp [restrictCoords, hi]

theorem l2_restrict_le (I : Finset ι) (z : ι → ℝ) :
    l2 (restrictCoords I z) ≤ l2 z := by
  have h := energy_restrict_add_compl I z
  rw [← l2_sq, ← l2_sq, ← l2_sq] at h
  nlinarith [l2_nonneg (restrictCoords I z), l2_nonneg z,
    sq_nonneg (l2 (restrictCoords Iᶜ z))]

theorem l1_head_identity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    {y u v : ι → ℝ} (hy : y = u + v)
    (hm : ∀ i, v i * u i = (a / b) * l2 v * |u i|) :
    let I := Finset.univ.filter (fun i => u i ≠ 0)
    l1 (restrictCoords I y) = l1 u + l1 (restrictCoords I v) := by
  dsimp
  unfold l1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u i = 0
  · simp [restrictCoords, hu]
  · have hmul : 0 ≤ u i * v i := by
      rw [mul_comm, hm]
      exact mul_nonneg (mul_nonneg (div_nonneg ha hb.le) (l2_nonneg v))
        (abs_nonneg _)
    simpa [restrictCoords, hu, hy] using abs_add_eq_of_product_nonneg hmul

theorem head_energy_identity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (u v : ι → ℝ)
    (hm : ∀ i, v i * u i = (a / b) * l2 v * |u i|) :
    let I := Finset.univ.filter (fun i => u i ≠ 0)
    b * energy (restrictCoords I v) = a * l2 v * l1 (restrictCoords I v) := by
  dsimp
  unfold energy l1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u i = 0
  · simp [restrictCoords, hu]
  · have habs : |v i| = (a / b) * l2 v :=
      abs_eq_of_matching (mul_nonneg (div_nonneg ha hb.le) (l2_nonneg v)) hu (hm i)
    have hsq : v i ^ 2 = ((a / b) * l2 v) * |v i| := by
      calc
        _ = |v i| * |v i| := by rw [← sq_abs]; ring
        _ = _ := by rw [habs]
    simp only [restrictCoords, Finset.mem_filter, Finset.mem_univ, true_and,
      if_pos hu]
    rw [hsq]
    field_simp

/-- The exact disjoint-support consequences needed by Section 11.
No probabilistic assumptions occur in this theorem. -/
theorem exists_optimal_disjoint_decomposition {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (y : ι → ℝ) :
    ∃ (I : Finset ι) (U V : ι → ℝ),
      y = U + V ∧
      (∀ i, i ∉ I → U i = 0) ∧
      (∀ i, i ∈ I → V i = 0) ∧
      (I.card : ℝ) ≤ (b / a) ^ 2 ∧
      infimalCost a b y - b * l2 V ≤ a * l1 U ∧
      a * l1 U ≤ infimalCost a b y ∧
      b * l2 V ≤ infimalCost a b y ∧
      (∀ i, |V i| ≤ (a / b ^ 2) * infimalCost a b y) := by
  obtain ⟨u, v, hy, hcost, hcard, hcap, hmatch⟩ :=
    exists_optimal_sparse_capped_decomposition ha hb y
  let I := Finset.univ.filter (fun i => u i ≠ 0)
  let U := restrictCoords I y
  let V := restrictCoords Iᶜ y
  let W := restrictCoords I v
  have hV : V = restrictCoords Iᶜ v := by
    ext i
    by_cases hu : u i = 0 <;> simp [V, I, restrictCoords, hy, hu]
  have hUnorm : l1 U = l1 u + l1 W := l1_head_identity ha.le hb hy hmatch
  have henergy : b * energy W = a * l2 v * l1 W :=
    head_energy_identity ha.le hb u v hmatch
  have hsplit : l2 W ^ 2 + l2 V ^ 2 = l2 v ^ 2 := by
    rw [hV, l2_sq, l2_sq, l2_sq]
    exact energy_restrict_add_compl I v
  have hVnorm : l2 V ≤ l2 v := by
    rw [hV]
    exact l2_restrict_le _ _
  have hMv : b * l2 v ≤ infimalCost a b y := by
    rw [hcost]
    nlinarith [mul_nonneg ha.le (l1_nonneg u)]
  have hdeficit :
      (infimalCost a b y - a * l1 U) * l2 v = b * l2 V ^ 2 := by
    rw [hcost, hUnorm]
    rw [← l2_sq W] at henergy
    nlinarith [henergy, congrArg (fun z : ℝ => b * z) hsplit]
  have hhead_le : a * l1 U ≤ infimalCost a b y := by
    by_cases hz : l2 v = 0
    · have hvzero : v = 0 := by
        ext i
        have h := hcap i
        simpa [hz] using (abs_nonpos_iff.mp (by simpa [hz] using h))
      rw [hcost, hUnorm]
      simp [W, restrictCoords, hvzero, l1, l2, energy]
    · have hvpos : 0 < l2 v := lt_of_le_of_ne (l2_nonneg v) (Ne.symm hz)
      have hnn : 0 ≤ b * l2 V ^ 2 := mul_nonneg hb.le (sq_nonneg _)
      nlinarith
  have hhead_ge : infimalCost a b y - b * l2 V ≤ a * l1 U := by
    by_cases hz : l2 v = 0
    · have hVzero : l2 V = 0 := le_antisymm (by simpa [hz] using hVnorm)
        (l2_nonneg V)
      have hvzero : v = 0 := by
        ext i
        exact abs_nonpos_iff.mp (by simpa [hz] using hcap i)
      rw [hVzero, mul_zero, sub_zero, hcost, hUnorm]
      simp [W, restrictCoords, hvzero, l1, l2, energy]
    · have hvpos : 0 < l2 v := lt_of_le_of_ne (l2_nonneg v) (Ne.symm hz)
      have hbound := mul_le_mul_of_nonneg_left hVnorm
        (mul_nonneg hb.le (l2_nonneg V))
      nlinarith
  refine ⟨I, U, V, (restrict_add_compl I y).symm, ?_, ?_, hcard,
    hhead_ge, hhead_le, (mul_le_mul_of_nonneg_left hVnorm hb.le).trans hMv, ?_⟩
  · intro i hi
    simp [U, restrictCoords, hi]
  · intro i hi
    simp [V, restrictCoords, hi]
  · intro i
    have hcapV : |V i| ≤ (a / b) * l2 v := by
      rw [hV]
      by_cases hi : i ∈ I
      · simp [restrictCoords, hi]
        exact mul_nonneg (div_pos ha hb).le (l2_nonneg v)
      · simpa [restrictCoords, hi] using hcap i
    have hvbound : l2 v ≤ infimalCost a b y / b := by
      apply (le_div_iff₀ hb).2
      simpa [mul_comm] using hMv
    calc
      |V i| ≤ (a / b) * l2 v := hcapV
      _ ≤ (a / b) * (infimalCost a b y / b) :=
        mul_le_mul_of_nonneg_left hvbound (div_pos ha hb).le
      _ = (a / b ^ 2) * infimalCost a b y := by ring

/-- Specialization to the weights eta * sqrt d and d, without redefining
the project mixed norm. Its definitional transport remains a separate step. -/
theorem exists_mixed_disjoint_decomposition {d : ℕ} (hd : 0 < d)
    {eta : ℝ} (heta : 0 < eta) (y : ι → ℝ) :
    ∃ (I : Finset ι) (U V : ι → ℝ),
      y = U + V ∧
      (∀ i, i ∉ I → U i = 0) ∧
      (∀ i, i ∈ I → V i = 0) ∧
      (I.card : ℝ) ≤ (d : ℝ) / eta ^ 2 ∧
      infimalCost (eta * Real.sqrt d) d y - d * l2 V ≤ eta * Real.sqrt d * l1 U ∧
      eta * Real.sqrt d * l1 U ≤ infimalCost (eta * Real.sqrt d) d y ∧
      d * l2 V ≤ infimalCost (eta * Real.sqrt d) d y ∧
      (∀ i, Real.sqrt d * |V i| ≤ eta * infimalCost (eta * Real.sqrt d) d y / d) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have ha : 0 < eta * Real.sqrt (d : ℝ) := mul_pos heta hs
  obtain ⟨I, U, V, hy, hU, hV, hcard, hlow, hhigh, htail, hcap⟩ :=
    exists_optimal_disjoint_decomposition ha hdR y
  have hratio : ((d : ℝ) / (eta * Real.sqrt d)) ^ 2 = (d : ℝ) / eta ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hdR.le]
    field_simp <;> ring
  rw [hratio] at hcard
  refine ⟨I, U, V, hy, hU, hV, hcard, hlow, hhigh, htail, ?_⟩
  intro i
  calc
    Real.sqrt d * |V i| ≤ Real.sqrt d *
        (((eta * Real.sqrt d) / (d : ℝ) ^ 2) * infimalCost (eta * Real.sqrt d) d y) :=
      mul_le_mul_of_nonneg_left (hcap i) hs.le
    _ = eta * infimalCost (eta * Real.sqrt d) d y * (Real.sqrt d) ^ 2 / (d : ℝ) ^ 2 := by
      ring
    _ = eta * infimalCost (eta * Real.sqrt d) d y / d := by
      rw [Real.sq_sqrt hdR.le]
      field_simp <;> ring

omit [DecidableEq ι] in
theorem mixed_cost_lower {d : ℕ} (hd : 0 < d)
    {eta : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (y : ι → ℝ) :
    eta * Real.sqrt d * l2 y ≤ infimalCost (eta * Real.sqrt d) d y := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hweight : eta * Real.sqrt d ≤ (d : ℝ) := by
    calc
      eta * Real.sqrt d ≤ 1 * Real.sqrt d :=
        mul_le_mul_of_nonneg_right heta1 (Real.sqrt_nonneg _)
      _ = Real.sqrt d := one_mul _
      _ ≤ d := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith
  exact infimalCost_lower_l2 (mul_nonneg heta (Real.sqrt_nonneg _)) hweight y

end GaussianMixedNormHelpers
