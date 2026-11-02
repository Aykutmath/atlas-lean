import RealGammaDivergence
import RealWishartExtended
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Reconstructed from preserved consumer interfaces on 2026-10-03.
This is new source, not a recovered original. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset Module
namespace GaussianMixedNormHelpers

/-- Tonelli factorization for a finite product of nonnegative extended-valued
functions. Measurability is enough; finite moments are not assumed. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E × (Fin n → E),
            f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
          have hg : Measurable (fun x : Fin n → E => ∏ i, f i.succ (x i)) :=
            Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
          rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i => μ i.succ))
            (f := f 0) (g := fun x : Fin n → E => ∏ i, f i.succ (x i))
            (hf 0).aemeasurable hg.aemeasurable]
          rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)]
        _ = _ := by rw [Fin.prod_univ_succ]

theorem gamma_extended_negative_real_eq_top (a s : ℝ)
    (ha : 0 < a) (has : a ≤ s) :
    (∫⁻ x : ℝ, (ENNReal.ofReal x)^(-s) ∂gammaMeasure a (1/2)) = ⊤ := by
  have heq : (fun x : ℝ => (ENNReal.ofReal x)^(-s)) =ᵐ[gammaMeasure a (1/2)]
      (fun x => ENNReal.ofReal (x^(-s))) := by
    filter_upwards [gammaMeasure_pos_ae a (1/2)] with x hx
    exact ENNReal.ofReal_rpow_of_pos hx
  rw [lintegral_congr_ae heq]
  by_contra h
  apply not_integrable_gammaMeasure_half_negative_real a s ha has
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_id.pow_const (-s)).aestronglyMeasurable) ?_).mp h
  filter_upwards [gammaMeasure_pos_ae a (1/2)] with x hx
  exact Real.rpow_nonneg hx.le _

theorem gamma_extended_negative_real_ne_zero (a s : ℝ) (ha : 0 < a) :
    (∫⁻ x : ℝ, (ENNReal.ofReal x)^(-s) ∂gammaMeasure a (1/2)) ≠ 0 := by
  letI : IsProbabilityMeasure (gammaMeasure a (1/2)) :=
    isProbabilityMeasure_gammaMeasure ha (by norm_num)
  intro h
  have hz := (lintegral_eq_zero_iff
    ((ENNReal.measurable_ofReal.comp measurable_id).pow_const (-s))).mp h
  have hf : ∀ᵐ x : ℝ ∂gammaMeasure a (1/2), False := by
    filter_upwards [gammaMeasure_pos_ae a (1/2), hz] with x hx he
    have hp : 0 < ENNReal.ofReal (x^(-s)) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hx _)
    rw [← ENNReal.ofReal_rpow_of_pos hx] at hp
    exact (ne_of_gt hp) he
  have hzero : gammaMeasure a (1/2) Set.univ = 0 := by
    simpa only [not_false_eq_true, Set.setOf_true] using ae_iff.mp hf
  have hone : gammaMeasure a (1/2) Set.univ = 1 := measure_univ
  rw [hone] at hzero
  exact one_ne_zero hzero

theorem gaussianRows_extended_negative_real_det_singular (r k : ℕ) (hkr : k < r)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) = ⊤ := by
  have hdet : ∀ f : Fin r → EuclideanSpace ℝ (Fin k), (realGramMatrix f).det = 0 := by
    intro f
    by_contra h
    have hli := Matrix.linearIndependent_of_det_gram_ne_zero (𝕜 := ℝ) (v := f) h
    have hc := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, finrank_euclideanSpace] at hc
    omega
  simp_rw [hdet, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hs)]
  simp

end GaussianMixedNormHelpers
#print axioms GaussianMixedNormHelpers.gamma_extended_negative_real_eq_top
#print axioms GaussianMixedNormHelpers.gamma_extended_negative_real_ne_zero
#print axioms GaussianMixedNormHelpers.gaussianRows_extended_negative_real_det_singular

#print axioms GaussianMixedNormHelpers.lintegral_fin_prod_eq_prod
