import SpectralBlocks
import EntropyArithmetic

noncomputable section
open Set Metric Module
open scoped BigOperators
namespace GaussianEllipsoid

/-- A universal Frobenius cover of the genuine singular-value nuclear ball.
The centers are arbitrary matrices; the entropy constant is 256. -/
theorem exists_nuclear_frobenius_cover (r : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r r),
      (s.card : ℝ) ≤ Real.exp (256 * r * R ^ 2 / ε ^ 2) ∧
      (∀ A : FrobeniusMatrix r r, spectralNuclearNorm A ≤ R →
        ∃ B ∈ s, ‖A - B‖ ≤ ε) := by
  classical
  by_cases hεR : R ≤ ε
  · refine ⟨{0}, ?_, ?_⟩
    · simpa only [Finset.card_singleton, Nat.cast_one] using
        Real.one_le_exp (by positivity : 0 ≤ 256 * (r : ℝ) * R ^ 2 / ε ^ 2)
    · intro A hA
      exact ⟨0, by simp, by simpa using ((frobenius_le_spectralNuclear A).trans hA).trans hεR⟩
  have hεR' : ε < R := lt_of_not_ge hεR
  have hRpos : 0 < R := hε.trans hεR'
  obtain ⟨J, hscale, hsize⟩ := exists_fourAdic_scale hRpos hε hεR'
  have hRad (j : ℕ) : 0 ≤ fourAdicRadius R j := by dsimp [fourAdicRadius]; positivity
  have hErr (j : ℕ) : 0 < fourAdicError ε J j := by dsimp [fourAdicError]; positivity
  choose s hs hcard hnet using fun j : Fin (J + 1) =>
    exists_square_lowRank_frobenius_cover r (4 ^ j.val) (hRad j.val) (hErr j.val)
  let C : Finset (FrobeniusMatrix r r) :=
    Finset.univ.image (fun f : (∀ j : Fin (J + 1), s j) => ∑ j, (f j).val)
  refine ⟨C, ?_, ?_⟩
  · have hcardC : (C.card : ℝ) ≤ ∏ j : Fin (J + 1), ((s j).card : ℝ) := by
      calc
        (C.card : ℝ) ≤ (Fintype.card (∀ j : Fin (J + 1), s j) : ℝ) := by
          exact_mod_cast (Finset.card_image_le (s := Finset.univ)
            (f := fun f : (∀ j : Fin (J + 1), s j) => ∑ j, (f j).val))
        _ = ∏ j : Fin (J + 1), ((s j).card : ℝ) := by
          rw [Fintype.card_pi]
          simp only [Fintype.card_coe, Nat.cast_prod]
    have hprod : (∏ j : Fin (J + 1), ((s j).card : ℝ)) ≤
        Real.exp (16 * r * (4 : ℝ) ^ J) := by
      calc
        ∏ j : Fin (J + 1), ((s j).card : ℝ) ≤
            ∏ j : Fin (J + 1),
              (1 + 4 * fourAdicRadius R j.val / fourAdicError ε J j.val) ^ (2 * r * 4 ^ j.val) :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => hcard j)
        _ = Real.exp (∑ j : Fin (J + 1), ((2 * r * 4 ^ j.val : ℕ) : ℝ) *
            Real.log (1 + 4 * fourAdicRadius R j.val / fourAdicError ε J j.val)) := by
          rw [Real.exp_sum]
          apply Finset.prod_congr rfl
          intro j _
          rw [Real.exp_nat_mul, Real.exp_log (by
            dsimp [fourAdicRadius, fourAdicError]
            positivity)]
        _ ≤ Real.exp (16 * r * (4 : ℝ) ^ J) := by
          apply Real.exp_le_exp.mpr
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((2 * r * 4 ^ j : ℕ) : ℝ) *
            Real.log (1 + 4 * fourAdicRadius R j / fourAdicError ε J j))]
          exact fourAdic_entropy_sum_le hRpos hε r J hscale
    apply hcardC.trans (hprod.trans (Real.exp_le_exp.mpr ?_))
    calc
      16 * r * (4 : ℝ) ^ J ≤ 16 * r * (16 * R ^ 2 / ε ^ 2) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = 256 * r * R ^ 2 / ε ^ 2 := by ring
  · intro A hA
    have happ (j : Fin (J + 1)) :
        ∃ B ∈ s j, ‖fourAdicBlock A j.val - B‖ < fourAdicError ε J j.val :=
      hnet j (fourAdicBlock A j.val) (rank_fourAdicBlock_le A j.val)
        (norm_fourAdicBlock_le A hR hA j.val)
    choose b hb herr using happ
    let f : ∀ j : Fin (J + 1), s j := fun j => ⟨b j, hb j⟩
    refine ⟨∑ j, b j, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩, ?_⟩
    have hsumB : (∑ j : Fin (J + 1), fourAdicBlock A j.val) = spectralPrefix A (4 ^ J) := by
      rw [Fin.sum_univ_eq_sum_range, sum_fourAdicBlock]
    have hfiniteError :
        ‖(∑ j : Fin (J + 1), fourAdicBlock A j.val) - ∑ j, b j‖ < ε / 2 := by
      calc
        ‖(∑ j : Fin (J + 1), fourAdicBlock A j.val) - ∑ j, b j‖ =
            ‖∑ j : Fin (J + 1), (fourAdicBlock A j.val - b j)‖ := by rw [Finset.sum_sub_distrib]
        _ ≤ ∑ j : Fin (J + 1), ‖fourAdicBlock A j.val - b j‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin (J + 1), fourAdicError ε J j.val :=
          Finset.sum_le_sum (fun j _ => (herr j).le)
        _ < ε / 2 := by rw [Fin.sum_univ_eq_sum_range]; exact sum_fourAdicError_lt hε J
    have htail : ‖A - spectralPrefix A (4 ^ J)‖ ≤ ε / 2 := by
      have ht := norm_spectralTail_sq_le A hR hA (show 0 < 4 ^ J by positivity)
      have hp : (0 : ℝ) < 2 ^ J := by positivity
      have hpow : ((4 ^ J : ℕ) : ℝ) = ((2 : ℝ) ^ J) ^ 2 := by
        push_cast
        rw [← pow_mul, mul_comm J 2, pow_mul]
        norm_num
      rw [hpow] at ht
      have hrad : R / (2 : ℝ) ^ J ≤ ε / 2 := by
        apply (div_le_iff₀ hp).mpr
        nlinarith
      have htsq : ‖A - spectralPrefix A (4 ^ J)‖ ^ 2 ≤ (R / (2 : ℝ) ^ J) ^ 2 := by
        simpa only [div_pow] using ht
      exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mp htsq).trans hrad
    have hid : A - (∑ j, b j) =
        (A - spectralPrefix A (4 ^ J)) +
        ((∑ j : Fin (J + 1), fourAdicBlock A j.val) - ∑ j, b j) := by rw [hsumB]; abel
    rw [hid]
    exact ((norm_add_le _ _).trans_lt (by linarith)).le


/-- Logarithmic form of the entropy bound, including the empty-dimensional case. -/
theorem exists_nuclear_frobenius_log_cover (r : ℕ) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ s : Finset (FrobeniusMatrix r r),
      Real.log (s.card : ℝ) ≤ 256 * r * R ^ 2 / ε ^ 2 ∧
      (∀ A : FrobeniusMatrix r r, spectralNuclearNorm A ≤ R →
        ∃ B ∈ s, ‖A - B‖ ≤ ε) := by
  obtain ⟨s, hcard, hnet⟩ := exists_nuclear_frobenius_cover r hR hε
  refine ⟨s, ?_, hnet⟩
  by_cases hs : s.card = 0
  · simp only [hs, Nat.cast_zero, Real.log_zero]
    positivity
  · have hpos : (0 : ℝ) < s.card := by exact_mod_cast Nat.pos_of_ne_zero hs
    exact (Real.log_le_log hpos hcard).trans_eq (Real.log_exp _)

end GaussianEllipsoid
#print axioms GaussianEllipsoid.exists_nuclear_frobenius_cover

#print axioms GaussianEllipsoid.exists_nuclear_frobenius_log_cover
