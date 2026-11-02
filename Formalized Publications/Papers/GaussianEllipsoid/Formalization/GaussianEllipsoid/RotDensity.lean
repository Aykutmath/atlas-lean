/-
Discharge of rotation premises P1 (`gaussianVectorLaw_density`) and P3
(`measure_eq_of_lintegral_eq`) from `GaussRotation.lean`.

Provenance: `GaussRotation.olean` is not built in this checkout, so this file
imports `GaussianEllipsoid.GaussianProbability` and repeats the two premise
statements verbatim from `GaussRotation.lean` source (same names, same
namespace). On integration (once `GaussRotation` builds), delete the two `def`
copies below and keep the theorems: `measure_eq_of_lintegral_eq_true` and
`gaussianVectorLaw_density_true` then target `GaussRotation`'s defs directly.

- P3: measures agreeing on all lintegrals are equal, via `Measure.ext` plus
  indicators (`lintegral_indicator_one`).
- P1: the Gaussian vector law is product volume with the product density, by
  induction on `d`. The step uses the `Measure.pi` ↔ `prod` correspondence
  `measurePreserving_piFinSuccAbove` (found in Mathlib), binary Tonelli
  (`lintegral_prod`) for the `withDensity`/`prod` interchange, and
  `Fin.prod_univ_succAbove` for the density factorisation.
-/

import GaussianEllipsoid.GaussRotation

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal


/-! ### P3 (lintegral extensionality) -/

/-- P3 holds: lintegral agreement on all measurable functions determines
the measure. -/
theorem measure_eq_of_lintegral_eq_true : measure_eq_of_lintegral_eq := by
  unfold measure_eq_of_lintegral_eq
  intro α _ μ ν h
  apply Measure.ext
  intro s hs
  have h1 := h (s.indicator (1 : α → ℝ≥0∞)) ((measurable_const).indicator hs)
  rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h1
  exact h1

/-! ### Density measurability -/

/-- The standard Gaussian density is measurable. -/
theorem gaussianPDF_measurable :
    Measurable (gaussianPDF (0 : ℝ) (1 : ℝ≥0)) := by
  have hcomp : gaussianPDF 0 1
      = ENNReal.ofReal ∘ gaussianPDFReal 0 1 := rfl
  rw [hcomp]
  exact ENNReal.continuous_ofReal.measurable.comp
    (measurable_gaussianPDFReal 0 1)

/-! ### Binary `withDensity` / `prod` interchange -/

/-- Binary interchange: a product of tilted measures is the tilt of the
product by the product density. Proved via P3 and binary Tonelli. -/
theorem withDensity_prod_interchange {α β : Type 0} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite μ]
    [SFinite ν] (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (hf : Measurable f)
    (hg : Measurable g) :
    (μ.withDensity f).prod (ν.withDensity g)
      = (μ.prod ν).withDensity (fun p : α × β => f p.1 * g p.2) := by
  have P3 : ∀ {α : Type 0} [MeasurableSpace α] (μ ν : Measure α),
      (∀ g : α → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = ∫⁻ x, g x ∂ν) →
        μ = ν :=
    measure_eq_of_lintegral_eq_true
  apply P3
  intro t ht
  have htm : AEMeasurable t ((μ.withDensity f).prod (ν.withDensity g)) :=
    ht.aemeasurable
  rw [lintegral_prod t htm]
  have hinner : ∀ x, Measurable (fun y => t (x, y)) :=
    fun x => ht.comp (measurable_prodMk_left (x := x))
  have hstep1 : (∫⁻ x, ∫⁻ y, t (x, y) ∂(ν.withDensity g) ∂(μ.withDensity f))
      = ∫⁻ x, ∫⁻ y, g y * t (x, y) ∂ν ∂(μ.withDensity f) := by
    apply lintegral_congr_ae
    filter_upwards with x
    exact lintegral_withDensity_eq_lintegral_mul ν hg (hinner x)
  rw [hstep1]
  have houter : Measurable (fun x => ∫⁻ y, g y * t (x, y) ∂ν) := by
    have h0 : Measurable (fun p : α × β => g p.2 * t p) :=
      (hg.comp measurable_snd).mul ht
    have heq : (fun p : α × β => g p.2 * t (p.1, p.2))
        = (fun p : α × β => g p.2 * t p) := by
      funext p
      obtain ⟨a, b⟩ := p
      rfl
    have hunc : Measurable
        (Function.uncurry (fun x y => g y * t (x, y))) := by
      show Measurable (fun p : α × β => g p.2 * t (p.1, p.2))
      rw [heq]
      exact h0
    exact Measurable.lintegral_prod_right
      (f := fun x y => g y * t (x, y)) hunc
  rw [lintegral_withDensity_eq_lintegral_mul μ hf houter]
  simp only [Pi.mul_apply]
  have hpull : ∀ x, f x * (∫⁻ y, g y * t (x, y) ∂ν)
      = ∫⁻ y, (fun p : α × β => f p.1 * (g p.2 * t p)) (x, y) ∂ν := by
    intro x
    exact (lintegral_const_mul _ (hg.mul (hinner x))).symm
  have hcongr : (∫⁻ x, f x * (∫⁻ y, g y * t (x, y) ∂ν) ∂μ)
      = ∫⁻ x, ∫⁻ y, (fun p : α × β => f p.1 * (g p.2 * t p)) (x, y) ∂ν ∂μ :=
    lintegral_congr_ae (Filter.Eventually.of_forall (fun x => hpull x))
  rw [hcongr]
  have hprod : AEMeasurable (fun p : α × β => f p.1 * (g p.2 * t p))
      (μ.prod ν) := by
    have h0 : Measurable (fun p : α × β => (f p.1 * g p.2) * t p) :=
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul ht
    simp only [mul_assoc] at h0
    exact h0.aemeasurable
  rw [← lintegral_prod (fun p : α × β => f p.1 * (g p.2 * t p)) hprod]
  have hmeas : Measurable (fun p : α × β => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [lintegral_withDensity_eq_lintegral_mul _ hmeas ht]
  simp only [Pi.mul_apply]
  refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show f z.1 * (g z.2 * t z) = f z.1 * g z.2 * t z
  exact (mul_assoc _ _ _).symm

/-! ### Pushforward through a measurable equivalence and `withDensity` -/

/-- Pushing a tilted pushforward back along a measurable equivalence moves
the tilt to the composition. Proved via P3 and `lintegral_map`. -/
theorem map_withDensity_equiv {α β : Type 0} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (B : Measure α) (h : β → ℝ≥0∞)
    (hh : Measurable h) :
    Measure.map ⇑e.symm ((Measure.map ⇑e B).withDensity h)
      = B.withDensity (h ∘ e) := by
  have P3 : ∀ {α : Type 0} [MeasurableSpace α] (μ ν : Measure α),
      (∀ g : α → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = ∫⁻ x, g x ∂ν) →
        μ = ν :=
    measure_eq_of_lintegral_eq_true
  apply P3
  intro g hg
  have he : Measurable (⇑e) := e.measurable
  have hes : Measurable (⇑e.symm) := e.symm.measurable
  have hg2 : Measurable (fun y => g (e.symm y)) := hg.comp hes
  rw [lintegral_map hg hes]
  rw [lintegral_withDensity_eq_lintegral_mul _ hh hg2]
  simp only [Pi.mul_apply]
  have hF : Measurable (fun y => h y * g (e.symm y)) := hh.mul hg2
  rw [lintegral_map hF he]
  have hhe : Measurable (h ∘ e) := hh.comp he
  rw [lintegral_withDensity_eq_lintegral_mul _ hhe hg]
  simp only [Pi.mul_apply, Function.comp_apply]
  refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hcancel : ∀ x, e.symm (e x) = x := fun x => e.symm_apply_apply x
  show h (e x) * g (e.symm (e x)) = h (e x) * g x
  rw [hcancel x]

/-! ### P1 base case (`d = 0`) -/

/-- P1 at `d = 0`: both sides are determined by their value on `univ`. -/
theorem gaussianVectorLaw_density_zero : gaussianVectorLaw 0
    = (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)).withDensity
      fun x => ∏ j, gaussianPDF 0 1 (x j) := by
  apply Measure.ext
  intro s hs
  by_cases hne : s.Nonempty
  · have hsu : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨x0, hx0⟩ := hne
      have hxx0 : x = x0 := Subsingleton.elim x x0
      rwa [hxx0]
    rw [hsu]
    have hL : gaussianVectorLaw 0 Set.univ = 1 := measure_univ
    have hPmeas0 : Measurable
        (fun x : Fin 0 → ℝ => ∏ j, gaussianPDF 0 1 (x j)) :=
      Finset.measurable_prod _ fun j _ => Fin.elim0 j
    have hR : ((Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)).withDensity
        fun x => ∏ j, gaussianPDF 0 1 (x j)) Set.univ = 1 := by
      have e := lintegral_withDensity_eq_lintegral_mul
        (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ))
        (f := fun x : Fin 0 → ℝ => ∏ j, gaussianPDF 0 1 (x j))
        (g := fun _ : Fin 0 → ℝ => (1 : ℝ≥0∞)) hPmeas0 measurable_const
      have e2 : ((Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)).withDensity
          fun x => ∏ j, gaussianPDF 0 1 (x j)) Set.univ
          = ∫⁻ x, (∏ j, gaussianPDF 0 1 (x j))
            ∂(Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) := by
        simpa [lintegral_one, Pi.mul_apply] using e
      rw [e2]
      have hcongr : (∫⁻ x, (∏ j, gaussianPDF 0 1 (x j))
            ∂(Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)))
          = ∫⁻ _ : (Fin 0 → ℝ), 1
            ∂(Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) := by
        apply lintegral_congr_ae
        filter_upwards with x
        simp
      rw [hcongr, lintegral_one]
      have hpi := Measure.pi_pi (fun _ : Fin 0 => (volume : Measure ℝ))
        (fun _ => Set.univ)
      rw [Set.pi_univ] at hpi
      simpa using hpi
    rw [hL, hR]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, measure_empty]

/-! ### P1 induction step -/

/-- P1 induction step: split off coordinate `i` with
`measurePreserving_piFinSuccAbove`, then reassemble with the binary
interchange and the density factorisation. -/
theorem gaussianVectorLaw_density_step (d : ℕ) (i : Fin (d + 1))
    (ih : gaussianVectorLaw d
      = (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).withDensity
        fun x => ∏ j, gaussianPDF 0 1 (x j)) :
    gaussianVectorLaw (d + 1)
      = (Measure.pi fun _ : Fin (d + 1) => (volume : Measure ℝ)).withDensity
        fun x => ∏ j, gaussianPDF 0 1 (x j) := by
  unfold gaussianVectorLaw at ih ⊢
  set e : (Fin (d + 1) → ℝ) ≃ᵐ (ℝ × (Fin d → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i with he
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hG : gaussianReal (0 : ℝ) (1 : ℝ≥0)
      = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 hv
  have hbG := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => gaussianReal 0 1) i).map_eq
  rw [← he] at hbG
  have hmap : Measure.map ⇑e.symm
      (Measure.map ⇑e (Measure.pi fun _ : Fin (d + 1) => gaussianReal 0 1))
      = Measure.pi fun _ : Fin (d + 1) => gaussianReal 0 1 :=
    MeasurableEquiv.map_symm_map e
  have hLHS : (Measure.pi fun _ : Fin (d + 1) => gaussianReal 0 1)
      = Measure.map ⇑e.symm
        ((gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin d => gaussianReal 0 1)) := by
    rw [← hmap, hbG]
  have hPmeas : Measurable
      (fun x : Fin d → ℝ => ∏ j, gaussianPDF 0 1 (x j)) :=
    Finset.measurable_prod _ fun j _ =>
      gaussianPDF_measurable.comp (measurable_pi_apply j)
  have hBin := withDensity_prod_interchange (volume : Measure ℝ)
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ))
    (gaussianPDF 0 1) (fun x : Fin d → ℝ => ∏ j, gaussianPDF 0 1 (x j))
    gaussianPDF_measurable hPmeas
  rw [← hG] at hBin
  rw [← ih] at hBin
  have hbV := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => (volume : Measure ℝ)) i).map_eq
  rw [← he] at hbV
  rw [← hbV] at hBin
  rw [hLHS, hBin]
  have hhmeas : Measurable (fun p : ℝ × (Fin d → ℝ) =>
      gaussianPDF 0 1 p.1
        * (fun x : Fin d → ℝ => ∏ j, gaussianPDF 0 1 (x j)) p.2) :=
    (gaussianPDF_measurable.comp measurable_fst).mul
      (hPmeas.comp measurable_snd)
  rw [map_withDensity_equiv e _ _ hhmeas]
  congr 1
  funext x
  have he1 : (e x).1 = x i := rfl
  have he2 : ∀ j, (e x).2 j = x (i.succAbove j) := fun j => rfl
  simp only [Function.comp_apply, he1, he2]
  exact (Fin.prod_univ_succAbove (fun k => gaussianPDF 0 1 (x k)) i).symm

/-! ### P1 assembly -/

/-- P1 holds for all `d`, by induction. -/
theorem gaussianVectorLaw_density_true : gaussianVectorLaw_density := by
  unfold gaussianVectorLaw_density
  intro d
  induction d with
  | zero => exact gaussianVectorLaw_density_zero
  | succ d ih =>
    exact gaussianVectorLaw_density_step d (Fin.last d) ih

end GaussianEllipsoid
