import PredictableGaussianBilinearMGF
import ConditionalMGFTail
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped ENNReal InnerProductSpace

namespace GaussianEllipsoidCandidate

/-- Split a finite tuple into its prefix and final coordinate. -/
def prefixLastEquiv {E : Type*} [MeasurableSpace E] (n : ℕ) :
    (Fin (n+1) → E) ≃ᵐ ((Fin n → E) × E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).trans
    MeasurableEquiv.prodComm

@[simp] theorem prefixLastEquiv_symm_apply {E : Type*} [MeasurableSpace E]
    (n : ℕ) (p : (Fin n → E) × E) :
    (prefixLastEquiv n).symm p = Fin.snoc p.1 p.2 := by
  change (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm (p.2,p.1) = _
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  change Fin.insertNth (α := fun _ : Fin (n+1) => E) (Fin.last n) p.2 p.1 = _
  exact Fin.insertNth_last' p.2 p.1

/-- Actual finite product-law decomposition into an independent last coordinate. -/
theorem pi_prefixLast_measurePreserving {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] (n : ℕ) :
    MeasurePreserving (prefixLastEquiv n) (Measure.pi fun _ : Fin (n+1) => ν)
      ((Measure.pi fun _ : Fin n => ν).prod ν) := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)
  exact hp.trans Measure.measurePreserving_swap

/-- A predictable Gaussian bilinear sum, revealed one row at a time. The
operator at row n is a measurable function of precisely the preceding n rows. -/
noncomputable def gaussianRowSum {r q : ℕ}
    (W : ∀ n : ℕ, (Fin n → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (u : ℕ → ℝ) : ∀ n : ℕ, (Fin n → Euclid q × Euclid r) → ℝ
  | 0, _ => 0
  | n+1, X => gaussianRowSum W u n (Fin.init X) +
      u n * ⟪W n (Fin.init X) (X (Fin.last n)).1,(X (Fin.last n)).2⟫_ℝ

/-- Adapted row sums are genuinely measurable under the finite Gaussian sample law. -/
theorem measurable_gaussianRowSum {r q : ℕ}
    (W : ∀ n : ℕ, (Fin n → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ n, Measurable (W n)) (u : ℕ → ℝ) (n : ℕ) :
    Measurable (gaussianRowSum W u n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (Fin.init : (Fin (n+1) → Euclid q × Euclid r) →
        (Fin n → Euclid q × Euclid r)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply i.castSucc
    have hlast : Measurable (fun X : Fin (n+1) → Euclid q × Euclid r => X (Fin.last n)) :=
      measurable_pi_apply _
    have hincr := (measurable_predictable_bilinear_row (W n) (hW n)).comp (hinit.prodMk hlast)
    exact (ih.comp hinit).add (hincr.const_mul (u n))

/-- Full adapted Gaussian row MGF under the actual finite product sample law.
The operators may depend arbitrarily and measurably on previous rows; only
their pathwise contraction and Frobenius-energy bounds are required. -/
theorem gaussianRowSum_lintegral_le {r q : ℕ}
    (W : ∀ n : ℕ, (Fin n → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ n, Measurable (W n))
    (hWnorm : ∀ n X, ‖W n X‖ ≤ 1) (R u : ℕ → ℝ)
    (hWenergy : ∀ n X, ‖operatorFrobenius (W n X)‖^2 ≤ R n)
    (t : ℝ) (hcap : ∀ k, (t*u k)^2 ≤ 1/2) (n : ℕ) :
    (∫⁻ X, ENNReal.ofReal (Real.exp (t * gaussianRowSum W u n X))
      ∂gaussianBilinearSampleLaw (Fin n) q r) ≤
        ENNReal.ofReal (Real.exp (t^2 * ∑ k ∈ Finset.range n, (u k)^2 * R k)) := by
  induction n with
  | zero => simp [gaussianRowSum]
  | succ n ih =>
    let ν := (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))
    have hp := pi_prefixLast_measurePreserving ν n
    have hp' := MeasurePreserving.symm (prefixLastEquiv n) hp
    have hF : Measurable (fun X : Fin n → Euclid q × Euclid r =>
        ENNReal.ofReal (Real.exp (t * gaussianRowSum W u n X))) :=
      ((measurable_gaussianRowSum W hW u n).const_mul t).exp.ennreal_ofReal
    calc
      (∫⁻ X, ENNReal.ofReal (Real.exp (t * gaussianRowSum W u (n+1) X))
          ∂gaussianBilinearSampleLaw (Fin (n+1)) q r)
          = ∫⁻ p : (Fin n → Euclid q × Euclid r) × (Euclid q × Euclid r),
              ENNReal.ofReal (Real.exp (t * gaussianRowSum W u (n+1) (Fin.snoc p.1 p.2)))
              ∂(gaussianBilinearSampleLaw (Fin n) q r).prod ν := by
        simpa only [prefixLastEquiv_symm_apply, gaussianBilinearSampleLaw] using
          (hp'.lintegral_comp_emb (prefixLastEquiv n).symm.measurableEmbedding
            (fun X => ENNReal.ofReal (Real.exp (t * gaussianRowSum W u (n+1) X)))).symm
      _ = ∫⁻ p : (Fin n → Euclid q × Euclid r) × (Euclid q × Euclid r),
            ENNReal.ofReal (Real.exp (t * gaussianRowSum W u n p.1)) *
              ENNReal.ofReal (Real.exp ((t*u n) * ⟪W n p.1 p.2.1,p.2.2⟫_ℝ))
            ∂(gaussianBilinearSampleLaw (Fin n) q r).prod ν := by
        apply lintegral_congr
        intro p
        rw [gaussianRowSum, Fin.init_snoc, Fin.snoc_last, mul_add, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (Real.exp ((t*u n)^2 * R n)) *
            ∫⁻ X, ENNReal.ofReal (Real.exp (t * gaussianRowSum W u n X))
              ∂gaussianBilinearSampleLaw (Fin n) q r :=
        predictable_gaussian_bilinear_row_step (gaussianBilinearSampleLaw (Fin n) q r)
          (W n) (hW n) (hWnorm n) (R n) (hWenergy n) (t*u n) (hcap n) _ hF
      _ ≤ ENNReal.ofReal (Real.exp ((t*u n)^2 * R n)) *
            ENNReal.ofReal (Real.exp (t^2 * ∑ k ∈ Finset.range n, (u k)^2 * R k)) :=
        mul_le_mul_right ih _
      _ = ENNReal.ofReal (Real.exp (t^2 * ∑ k ∈ Finset.range (n+1), (u k)^2 * R k)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, Finset.sum_range_succ]
        congr 2
        ring

/-- An actual Gaussian adapted-row Bernstein/Chernoff lower tail. This theorem
has no assumed MGF, conditional expectation, concentration, or integrability
hypothesis. The deterministic coefficient-radius and variance bounds are
precisely those established by the dyadic record bookkeeping. -/
theorem gaussianRowSum_lower_tail {r q : ℕ}
    (W : ∀ n : ℕ, (Fin n → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r))
    (hW : ∀ n, Measurable (W n))
    (hWnorm : ∀ n X, ‖W n X‖ ≤ 1) (R u : ℕ → ℝ)
    (hWenergy : ∀ n X, ‖operatorFrobenius (W n X)‖^2 ≤ R n)
    (n : ℕ) (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hcoef : ∀ k, (u k)^2 ≤ b^2 / 2)
    (hvar : (∑ k ∈ Finset.range n, (u k)^2 * R k) ≤ V) :
    (gaussianBilinearSampleLaw (Fin n) q r).real {X | gaussianRowSum W u n X ≤ -x} ≤
      Real.exp (-(1 / 4 : ℝ) * min (x^2 / V) (x / b)) := by
  have hlin : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      (∫⁻ X, ENNReal.ofReal (Real.exp ((-lam) * gaussianRowSum W u n X))
        ∂gaussianBilinearSampleLaw (Fin n) q r) ≤ ENNReal.ofReal (Real.exp (lam^2 * V)) := by
    intro lam hlam hlammax
    have hcap : ∀ k, ((-lam)*u k)^2 ≤ 1/2 := by
      intro k
      have hbprod : lam * b ≤ 1 := (le_div_iff₀ hb).1 hlammax
      have hsq : (lam*b)^2 ≤ 1 := by
        simpa using pow_le_pow_left₀ (mul_nonneg hlam hb.le) hbprod 2
      have hc := mul_le_mul_of_nonneg_left (hcoef k) (sq_nonneg lam)
      nlinarith
    have hh := gaussianRowSum_lintegral_le W hW hWnorm R u hWenergy (-lam) hcap n
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simpa only [neg_sq] using mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
  apply lower_tail_of_mgf_radius (gaussianBilinearSampleLaw (Fin n) q r)
    (gaussianRowSum W u n) V b x hV hb hx
  · intro lam hlam hlammax
    exact integrable_exp_of_lintegral_bound _ _ (measurable_gaussianRowSum W hW u n)
      (-lam) _ (hlin lam hlam hlammax)
  · intro lam hlam hlammax
    exact mgf_le_of_lintegral_bound _ _ (measurable_gaussianRowSum W hW u n)
      (-lam) _ (Real.exp_nonneg _) (hlin lam hlam hlammax)

#print axioms gaussianRowSum_lintegral_le
#print axioms gaussianRowSum_lower_tail

#print axioms prefixLastEquiv_symm_apply
#print axioms pi_prefixLast_measurePreserving
#print axioms measurable_gaussianRowSum

end GaussianEllipsoidCandidate
