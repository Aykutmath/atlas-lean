import RealGammaMoment
import BartlettJointLaw
import GammaExtendedMoment

noncomputable section
open Finset MeasureTheory ProbabilityTheory Set Module
open InnerProductSpace
namespace GaussianMixedNormHelpers

/-- Exact real-exponent inverse moment of an arbitrary finite independent Gamma family. -/
theorem gamma_product_negative_real_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : ℝ) (hs : 0 ≤ s) (ha : ∀ i, s < a i) :
    (∫ x : ι → ℝ, ∏ i, (x i) ^ (-s)
      ∂Measure.pi (fun i => gammaMeasure (a i) (1/2))) =
    ∏ i, (2:ℝ)^(-s) * (Real.Gamma (a i-s) / Real.Gamma (a i)) := by
  letI (i : ι) : IsProbabilityMeasure (gammaMeasure (a i) (1/2)) :=
    isProbabilityMeasure_gammaMeasure (lt_of_le_of_lt hs (ha i)) (by norm_num)
  rw [integral_pi_prod_real (fun i => gammaMeasure (a i) (1/2)) (fun _ x => x^(-s))]
  apply Finset.prod_congr rfl
  intro i _
  have h := integral_gammaMeasure_half_negative_real (sub_pos.mpr (ha i)) s hs
  rw [sub_add_cancel] at h
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)] using h

/-- The finite real-exponent Bartlett moment is genuinely integrable. -/
theorem gamma_product_negative_real_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : ℝ) (hs : 0 ≤ s) (ha : ∀ i, s < a i) :
    Integrable (fun x : ι → ℝ => ∏ i, (x i)^(-s))
      (Measure.pi (fun i => gammaMeasure (a i) (1/2))) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_product_negative_real_moment a s hs ha]
  apply ne_of_gt
  apply Finset.prod_pos
  intro i _
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (div_pos (Real.Gamma_pos_of_pos (sub_pos.mpr (ha i)))
      (Real.Gamma_pos_of_pos (lt_of_le_of_lt hs (ha i))))


/-- Real-exponent Wishart determinant identity in the finite-moment regime.
The zero-based factor (k-j)/2 is the paper's (k-j+1)/2 with one-based j. -/
theorem gaussianRows_negative_real_det_moment (r k : ℕ) (hkr : r ≤ k)
    (s : ℝ) (hs : 0 ≤ s) (hshape : ∀ j : Fin r, s < ((k-j.val : ℕ):ℝ)/2) :
    (∫ f : Fin r → EuclideanSpace ℝ (Fin k), (realGramMatrix f).det ^ (-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) =
    ∏ j : Fin r, (2:ℝ)^(-s) *
      (Real.Gamma (((k-j.val : ℕ):ℝ)/2-s) / Real.Gamma (((k-j.val : ℕ):ℝ)/2)) := by
  let μ := Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))
  let T := fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
    fun j : Fin r => ‖gramSchmidt ℝ f j‖^2
  have hT : Measurable T := measurable_gramSchmidt_norm_sq
  have hi := integral_map (μ := μ) hT.aemeasurable
    (f := fun x : Fin r → ℝ => ∏ j, (x j)^(-s))
    ((Finset.measurable_prod Finset.univ (fun j _ => (measurable_pi_apply j).pow_const (-s))).aestronglyMeasurable)
  have hmap := gaussianRows_map_gramSchmidt_norm_sq r k hkr
  change μ.map T = _ at hmap
  rw [hmap] at hi
  have hf : (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      ∏ j : Fin r, (‖gramSchmidt ℝ f j‖^2)^(-s)) =
      (fun f => (realGramMatrix f).det^(-s)) := by
    funext f
    rw [det_realGramMatrix_eq_prod_gramSchmidt_norm_sq]
    exact Real.finsetProd_rpow _ _ (by intros; positivity) _
  change (∫ x : Fin r → ℝ, ∏ j, (x j)^(-s)
      ∂Measure.pi (fun j : Fin r => gammaMeasure (((k-j.val : ℕ):ℝ)/2) (1/2))) =
      (∫ f : Fin r → EuclideanSpace ℝ (Fin k),
        ∏ j : Fin r, (‖gramSchmidt ℝ f j‖^2)^(-s) ∂μ) at hi
  rw [hf] at hi
  exact hi.symm.trans (gamma_product_negative_real_moment _ s hs hshape)

/-- The paper's single strict dimension condition implies every Gamma factor is integrable. -/
theorem wishart_shape_gt (r k : ℕ) (s : ℝ) (hs : 0 < s)
    (h : (r:ℝ)+2*s-1 < k) :
    r ≤ k ∧ ∀ j : Fin r, s < ((k-j.val : ℕ):ℝ)/2 := by
  have hkr : r ≤ k := by
    have h' : (r:ℝ) < (k:ℝ)+1 := by linarith
    have hn : r < k+1 := by exact_mod_cast h'
    omega
  refine ⟨hkr, ?_⟩
  intro j
  have hjk : j.val ≤ k := by omega
  have hjr : (j.val:ℝ)+1 ≤ r := by exact_mod_cast j.isLt
  rw [Nat.cast_sub hjk]
  linarith

#print axioms gaussianRows_negative_real_det_moment
#print axioms wishart_shape_gt
#print axioms gamma_product_negative_real_moment
#print axioms gamma_product_negative_real_integrable
end GaussianMixedNormHelpers
