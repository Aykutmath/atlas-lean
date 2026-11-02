import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Sym.Card
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal
namespace BMUniformMoment

lemma multiset_prod_eq_univ_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [CommMonoid M] (s : Multiset ι) (f : ι → M) :
    (s.map f).prod = ∏ i, f i ^ s.count i := by
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [Multiset.mem_toFinset] at hi
  simp [Multiset.count_eq_zero.mpr hi]

lemma multiset_multinomial_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Multiset ι) :
    s.countPerms * (∏ i, (s.count i).factorial) = s.card.factorial := by
  have h := Nat.multinomial_spec s.toFinset (fun i => s.count i)
  have hsum : ∑ i ∈ s.toFinset, s.count i = s.card :=
    Multiset.sum_count_eq_card (by simp)
  have hprod : ∏ i ∈ s.toFinset, (s.count i).factorial = ∏ i, (s.count i).factorial := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [Multiset.mem_toFinset] at hi
    simp [Multiset.count_eq_zero.mpr hi]
  have heq : s.countPerms = Nat.multinomial s.toFinset (fun i => s.count i) := by
    simp [Multiset.countPerms, Finsupp.multinomial_eq, Multiset.toFinsupp_support,
      Multiset.toFinsupp_apply]
    exact Nat.multinomial_congr (fun i _ => Multiset.toFinsupp_apply s i)
  rw [heq, mul_comm, ← hprod, h, hsum]

/-- All required product-sum moments are integrable from the scalar moments. -/
theorem independent_sum_integrable_pow {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (Y : ι → Ω → ℝ) (m : ℕ)
    (hI : ∀ i k, k ≤ m → Integrable (fun x => (Y i x)^k) μ) :
    Integrable (fun x : ι → Ω => (∑ i, Y i (x i))^m) (Measure.pi (fun _ => μ)) := by
  classical
  have hexp (x : ι → Ω) :
      (∑ i, Y i (x i))^m = ∑ s : Sym ι m,
        (s.val.countPerms : ℝ) * ∏ i, Y i (x i)^s.val.count i := by
    rw [Finset.sum_pow, Finset.sym_univ]
    apply Finset.sum_congr rfl
    intro s _
    rw [multiset_prod_eq_univ_count]
  simp_rw [hexp]
  apply integrable_finset_sum
  intro s _
  apply Integrable.const_mul
  exact Integrable.fintype_prod_dep
    (fun i => hI i _ (by simpa only [s.property] using Multiset.count_le_card i s.val))

/-- The exact finite-product moment estimate. Independence is the displayed
product measure; the proof expands the multinomial and counts weak compositions.
Only moments of orders at most m are used. -/
theorem independent_sum_moment_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (Y : ι → Ω → ℝ) (m : ℕ) (C : ℝ)
    (hY : ∀ i x, 0 ≤ Y i x) (hC : 0 ≤ C)
    (hI : ∀ i k, k ≤ m → Integrable (fun x => (Y i x)^k) μ)
    (hM : ∀ i k, k ≤ m → (∫ x, (Y i x)^k ∂μ) ≤ (k.factorial : ℝ)*C^k) :
    (∫ x : ι → Ω, (∑ i, Y i (x i))^m ∂Measure.pi (fun _ => μ)) ≤
      (Fintype.card ι + m - 1).choose m * (m.factorial : ℝ)*C^m := by
  classical
  letI : MeasureSpace Ω := ⟨μ⟩
  letI : SigmaFinite (volume : Measure Ω) := inferInstanceAs (SigmaFinite μ)
  have hprodI (s : Sym ι m) : Integrable
      (fun x : ι → Ω => ∏ i, Y i (x i)^s.val.count i) (Measure.pi (fun _ => μ)) := by
    exact Integrable.fintype_prod_dep
      (fun i => hI i _ (by simpa only [s.property] using Multiset.count_le_card i s.val))
  have hexp (x : ι → Ω) :
      (∑ i, Y i (x i))^m = ∑ s : Sym ι m,
        (s.val.countPerms : ℝ) * ∏ i, Y i (x i)^s.val.count i := by
    rw [Finset.sum_pow, Finset.sym_univ]
    apply Finset.sum_congr rfl
    intro s _
    rw [multiset_prod_eq_univ_count]
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun s _ => (hprodI s).const_mul _)]
  calc
    (∑ s : Sym ι m, ∫ x : ι → Ω, (s.val.countPerms : ℝ) *
        ∏ i, Y i (x i)^s.val.count i ∂Measure.pi (fun _ => μ))
      ≤ ∑ _s : Sym ι m, (m.factorial : ℝ)*C^m := by
      apply Finset.sum_le_sum
      intro s _
      rw [integral_const_mul]
      have hfub : (∫ x : ι → Ω, ∏ i, Y i (x i)^s.val.count i
          ∂Measure.pi (fun _ => μ)) = ∏ i, ∫ x, (Y i x)^s.val.count i ∂μ := by
        exact integral_fintype_prod_eq_prod (fun i x => Y i x^s.val.count i)
      rw [hfub]
      calc
        (s.val.countPerms : ℝ) * (∏ i, ∫ x, Y i x^s.val.count i ∂μ)
          ≤ (s.val.countPerms : ℝ) * ∏ i, ((s.val.count i).factorial : ℝ)*C^(s.val.count i) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply Finset.prod_le_prod
            · intro i _
              exact integral_nonneg (fun x => pow_nonneg (hY i x) _)
            · intro i _
              exact hM i _ (by simpa only [s.property] using Multiset.count_le_card i s.val)
        _ = (m.factorial : ℝ)*C^m := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
          have hs : ∑ i, s.val.count i = m :=
            (Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)).trans s.property
          rw [hs, ← mul_assoc, ← Nat.cast_prod, ← Nat.cast_mul,
            multiset_multinomial_factorial, s.property]
    _ = (Fintype.card ι + m - 1).choose m * (m.factorial : ℝ)*C^m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Sym.card_sym_eq_choose]
      ring

/-- At moment order equal to sample size, stars and bars costs only 4^n. -/
theorem independent_sum_diagonal_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (n : ℕ) (hn : 0 < n)
    (Y : Fin n → Ω → ℝ) (C : ℝ) (hY : ∀ i x, 0 ≤ Y i x) (hC : 0 ≤ C)
    (hI : ∀ i k, k ≤ n → Integrable (fun x => (Y i x)^k) μ)
    (hM : ∀ i k, k ≤ n → (∫ x, (Y i x)^k ∂μ) ≤ (k.factorial : ℝ)*C^k) :
    (∫ x : Fin n → Ω, (∑ i, Y i (x i))^n ∂Measure.pi (fun _ => μ)) ≤
      (4*C*n)^n := by
  apply (independent_sum_moment_le μ Y n C hY hC hI hM).trans
  have hchoose : ((n+n-1).choose n : ℝ) ≤ (4:ℝ)^n := by
    have hpos : 0 < n+n-1 := by omega
    have h := (Nat.choose_le_two_pow (n+n-1) n).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : n+n-1 ≤ 2*n))
    have hp : (2:ℕ)^(2*n) = 4^n := by rw [pow_mul]; norm_num
    rw [hp] at h
    exact_mod_cast h
  have hfac : (n.factorial : ℝ) ≤ (n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  simp only [Fintype.card_fin]
  calc
    ((n+n-1).choose n : ℝ) * n.factorial * C^n
      ≤ (4:ℝ)^n * (n:ℝ)^n * C^n :=
        mul_le_mul_of_nonneg_right (mul_le_mul hchoose hfac (Nat.cast_nonneg _) (by positivity))
          (pow_nonneg hC _)
    _ = (4*C*n)^n := by rw [← mul_pow, ← mul_pow]; congr 1; ring

/-- Polynomial Markov with a freely chosen fixed threshold gives an exponential
sample-size probability, sufficient to pay any fixed volumetric entropy. -/
theorem independent_sum_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (Y : Fin n → Ω → ℝ) (C T : ℝ) (hY : ∀ i x, 0 ≤ Y i x)
    (hC : 0 ≤ C) (hT : 0 < T)
    (hI : ∀ i k, k ≤ n → Integrable (fun x => (Y i x)^k) μ)
    (hM : ∀ i k, k ≤ n → (∫ x, (Y i x)^k ∂μ) ≤ (k.factorial : ℝ)*C^k) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | T*n < ∑ i, Y i (x i)} ≤ (4*C/T)^n := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have ht : 0 < T*n := mul_pos hT hnR
  have hsub : {x : Fin n → Ω | T*n < ∑ i, Y i (x i)} ⊆
      {x : Fin n → Ω | (T*n)^n ≤ (∑ i, Y i (x i))^n} := by
    intro x hx
    exact pow_le_pow_left₀ ht.le hx.le n
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := ν) (ae_of_all _ (fun x => pow_nonneg (Finset.sum_nonneg (fun i _ => hY i (x i))) n))
    (independent_sum_integrable_pow μ Y n hI) ((T*n)^n)
  have hm : (T*n)^n * ν.real {x | T*n < ∑ i, Y i (x i)} ≤ (4*C*n)^n := by
    calc
      _ ≤ (T*n)^n * ν.real {x | (T*n)^n ≤ (∑ i, Y i (x i))^n} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg ht.le _)
      _ ≤ _ := hmark.trans (independent_sum_diagonal_moment_le μ n hn Y C hY hC hI hM)
  have heq : (4*C/T)^n = (4*C*n)^n / (T*n)^n := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [heq]
  exact (le_div_iff₀ (pow_pos ht n)).2 (by simpa [mul_comm] using hm)

#print axioms independent_sum_integrable_pow
#print axioms independent_sum_moment_le
#print axioms independent_sum_diagonal_moment_le
#print axioms independent_sum_tail_le
end BMUniformMoment
