import WishartDivergence

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset Module
open InnerProductSpace
namespace GaussianMixedNormHelpers

/-- Tonelli and the proved Bartlett law give the extended determinant moment
as a product of scalar moments, without an integrability assumption. -/
theorem gaussianRows_extended_negative_real_det_factorization (r k : ℕ) (hkr : r ≤ k)
    (s : ℝ) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) =
    ∏ j : Fin r, ∫⁻ x : ℝ, (ENNReal.ofReal x)^(-s)
      ∂gammaMeasure (((k-j.val : ℕ):ℝ)/2) (1/2) := by
  let μ := Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))
  let ν := fun j : Fin r => gammaMeasure (((k-j.val : ℕ):ℝ)/2) (1/2)
  let T := fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
    fun j : Fin r => ‖gramSchmidt ℝ f j‖^2
  letI (j : Fin r) : IsProbabilityMeasure (ν j) :=
    isProbabilityMeasure_gammaMeasure (by
      have hj : 0 < k-j.val := by omega
      positivity) (by norm_num)
  have hmap : μ.map T = Measure.pi ν := gaussianRows_map_gramSchmidt_norm_sq r k hkr
  have hm : Measurable (fun x : Fin r → ℝ => ∏ j, (ENNReal.ofReal (x j))^(-s)) := by
    fun_prop
  have hi := lintegral_map (μ := μ) hm measurable_gramSchmidt_norm_sq
  change (∫⁻ x : Fin r → ℝ, ∏ j, (ENNReal.ofReal (x j))^(-s) ∂μ.map T) = _ at hi
  rw [hmap] at hi
  have heq : (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      ∏ j : Fin r, (ENNReal.ofReal (‖gramSchmidt ℝ f j‖^2))^(-s)) =
      (fun f => (ENNReal.ofReal (realGramMatrix f).det)^(-s)) := by
    funext f
    rw [ENNReal.prod_rpow_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => sq_nonneg _),
      ← det_realGramMatrix_eq_prod_gramSchmidt_norm_sq]
  change _ = (∫⁻ f, ∏ j : Fin r,
    (ENNReal.ofReal (‖gramSchmidt ℝ f j‖^2))^(-s) ∂μ) at hi
  rw [heq] at hi
  exact hi.symm.trans (lintegral_fin_prod_eq_prod ν
    (fun _ x => (ENNReal.ofReal x)^(-s)) (by intro; fun_prop))

/-- The divergence half of the exact Wishart moment formula, including the
critical boundary. Positive row count is explicit: the empty determinant is 1. -/
theorem gaussianRows_extended_negative_real_det_diverges (r k : ℕ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s) (hcrit : (k:ℝ) ≤ (r:ℝ)+2*s-1) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) = ⊤ := by
  by_cases hkr : r ≤ k
  · rw [gaussianRows_extended_negative_real_det_factorization r k hkr s]
    let j : Fin r := ⟨r-1, by omega⟩
    have hshape : ∀ i : Fin r, 0 < ((k-i.val : ℕ):ℝ)/2 := by
      intro i
      have hi : 0 < k-i.val := by omega
      positivity
    have hj : ((k-j.val : ℕ):ℝ)/2 ≤ s := by
      dsimp [j]
      rw [Nat.cast_sub (by omega : r-1 ≤ k), Nat.cast_sub (by omega : 1 ≤ r)]
      push_cast
      linarith
    apply WithTop.prod_eq_top (Finset.mem_univ j)
      (gamma_extended_negative_real_eq_top _ s (hshape j) hj)
    intro i _
    exact gamma_extended_negative_real_ne_zero _ s (hshape i)
  · exact gaussianRows_extended_negative_real_det_singular r k (by omega) s hs

/-- The product formula with exactly the paper's `2^(-r*s)` prefactor. -/
theorem gaussianRows_extended_negative_real_det_finite_formula (r k : ℕ)
    (s : ℝ) (hs : 0 < s) (hcrit : (r:ℝ)+2*s-1 < (k:ℝ)) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) =
    ENNReal.ofReal ((2:ℝ)^(-(r:ℝ)*s) * ∏ j : Fin r,
      Real.Gamma (((k-j.val : ℕ):ℝ)/2-s) / Real.Gamma (((k-j.val : ℕ):ℝ)/2)) := by
  obtain ⟨hkr,hshape⟩ := wishart_shape_gt r k s hs hcrit
  rw [gaussianRows_extended_negative_real_det_moment r k hkr s hs.le hshape,
    Finset.prod_mul_distrib]
  congr 2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

/-- The paper's complete finite/divergent formula for positive matrix dimension.
Gamma factors use zero-based j; `(k-j)/2` equals the paper's one-based `(k-j+1)/2`. -/
theorem gaussianRows_extended_negative_real_det_exact (r k : ℕ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) =
    if (r:ℝ)+2*s-1 < (k:ℝ) then
      ENNReal.ofReal ((2:ℝ)^(-(r:ℝ)*s) * ∏ j : Fin r,
        Real.Gamma (((k-j.val : ℕ):ℝ)/2-s) / Real.Gamma (((k-j.val : ℕ):ℝ)/2))
    else ⊤ := by
  split_ifs with h
  · exact gaussianRows_extended_negative_real_det_finite_formula r k s hs h
  · exact gaussianRows_extended_negative_real_det_diverges r k hr s hs (le_of_not_gt h)

/-- Empty matrices have determinant 1 and moment 1, regardless of k or s.
This is why the divergent branch explicitly requires positive row dimension. -/
theorem gaussianRows_extended_negative_real_det_zero_rows (k : ℕ) (s : ℝ) :
    (∫⁻ f : Fin 0 → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin 0 => euclideanGaussianLaw (Fin k))) = 1 := by
  simp

#print axioms gaussianRows_extended_negative_real_det_exact
#print axioms gaussianRows_extended_negative_real_det_zero_rows
end GaussianMixedNormHelpers
