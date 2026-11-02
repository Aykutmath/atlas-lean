/-
Section 2 reductions: fitting-probability monotonicity in the sample size.

A fit for a larger sample restricts to a fit for any sub-sample
(`HasFit.restrict`, kernel-checked in Basic). Since the first-`m`
marginal of `gaussianSampleLaw d n` is `gaussianSampleLaw d m`
(`gaussianSample_restrict_map`), fitting probabilities are antitone in `n`.
Outer regularity (`measure_eq_iInf`) makes the transfer work without any
measurability assumption on the fitting events.

Serves both (B0) below-threshold enlargement and (A0) above-threshold
restriction: they are the same monotonicity fact used in opposite directions.

Mathematical source: paper.tex, Section 2.
-/
import GaussianEllipsoid.GaussianProbability

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory

/-- `Fin.castLE` is injective. -/
theorem castLE_injective {m n : Nat} (h : m ≤ n) :
    Function.Injective (Fin.castLE h) := by
  intro a b hab
  exact Fin.ext (by simpa using congrArg Fin.val hab)

/-- Restriction to the first `m` samples is measurable. -/
theorem restrict_firstM_measurable {d n m : Nat} (h : m ≤ n) :
    Measurable (fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (Fin.castLE h i))

/-- The first-`m` marginal of the sample law is the `m`-sample law. -/
theorem gaussianRestrict_castLE_map {d n m : Nat} (h : m ≤ n) :
    (gaussianSampleLaw d n).map (fun x i => x (Fin.castLE h i)) =
      gaussianSampleLaw d m :=
  gaussianSample_restrict_map (Fin.castLE h) (castLE_injective h)

/-- The `n`-sample fit is contained in the preimage of the `m`-sample fit. -/
theorem fit_subset_restrict_preimage {d n m : Nat} (h : m ≤ n) :
    {x : Sample d n | HasFit x} ⊆
      (fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) ⁻¹'
        {y : Sample d m | HasFit y} := by
  intro x hx
  exact HasFit.restrict hx (Fin.castLE h)

/-- The `n`-sample strict fit is contained in the preimage of the `m`-sample
strict fit. -/
theorem strictFit_subset_restrict_preimage {d n m : Nat} (h : m ≤ n) :
    {x : Sample d n | HasStrictFit x} ⊆
      (fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) ⁻¹'
        {y : Sample d m | HasStrictFit y} := by
  intro x hx
  exact HasStrictFit.restrict hx (Fin.castLE h)

/-- Transfer across restriction needs no measurability of the target event:
outer regularity reduces to measurable supersets, where the marginal
identity applies. -/
theorem measure_restrict_preimage_le {d n m : Nat} (h : m ≤ n)
    (F : Set (Sample d m)) :
    gaussianSampleLaw d n
        ((fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) ⁻¹' F)
      ≤ gaussianSampleLaw d m F := by
  have hmap := gaussianRestrict_castLE_map (d := d) (n := n) (m := m) h
  have hmeas := restrict_firstM_measurable (d := d) (n := n) (m := m) h
  have hreg : gaussianSampleLaw d m F =
      ⨅ (H') (_ : F ⊆ H') (_ : MeasurableSet H'), gaussianSampleLaw d m H' :=
    measure_eq_iInf F
  rw [hreg]
  simp only [le_iInf_iff]
  intro H' hsub hmeas'
  calc gaussianSampleLaw d n
          ((fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) ⁻¹' F)
        ≤ gaussianSampleLaw d n
            ((fun x : Sample d n => fun i : Fin m => x (Fin.castLE h i)) ⁻¹' H') :=
          measure_mono (Set.preimage_mono hsub)
      _ = gaussianSampleLaw d m H' := by
          rw [← hmap, Measure.map_apply hmeas hmeas']

/-- Fitting probabilities are antitone in the sample size (PSD version). -/
theorem measure_fit_mono {d n m : Nat} (h : m ≤ n) :
    gaussianSampleLaw d n {x : Sample d n | HasFit x} ≤
      gaussianSampleLaw d m {x : Sample d m | HasFit x} :=
  (measure_mono (fit_subset_restrict_preimage h)).trans
    (measure_restrict_preimage_le h _)

/-- Fitting probabilities are antitone in the sample size (PD version). -/
theorem measure_strictFit_mono {d n m : Nat} (h : m ≤ n) :
    gaussianSampleLaw d n {x : Sample d n | HasStrictFit x} ≤
      gaussianSampleLaw d m {x : Sample d m | HasStrictFit x} :=
  (measure_mono (strictFit_subset_restrict_preimage h)).trans
    (measure_restrict_preimage_le h _)

end GaussianEllipsoid
