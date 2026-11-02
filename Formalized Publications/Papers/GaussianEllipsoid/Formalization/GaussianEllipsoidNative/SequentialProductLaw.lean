import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianMixedNormHelpers

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A Fubini skew-product step: a fibre law independent of the old state yields
an independent new output, even though its defining function depends on that state. -/
theorem constant_fibre_skew_product {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C} {σ : Measure D}
    [SFinite μ] [SFinite ρ] {f : A → B} {g : A → C → D}
    (hf : MeasurePreserving f μ ν) (hg : Measurable (Function.uncurry g))
    (hlaw : ∀ᵐ a ∂μ, Measure.map (g a) ρ = σ) :
    Measure.map (fun z : A × C => (f z.1, g z.1 z.2)) (μ.prod ρ) = ν.prod σ :=
  (hf.skew_product hg hlaw).map_eq

/-- Split a finite independent family into its prefix and final coordinate. -/
theorem measurePreserving_finInitLast {n : ℕ} (μ : Fin (n + 1) → Measure X)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (fun x : Fin (n + 1) → X => (Fin.init x, x (Fin.last n)))
      (Measure.pi μ) ((Measure.pi fun i : Fin n => μ i.castSucc).prod (μ (Fin.last n))) := by
  have h := (measurePreserving_piFinSuccAbove μ (Fin.last n))
  have hs := (Measure.measurePreserving_swap :
    MeasurePreserving Prod.swap ((μ (Fin.last n)).prod (Measure.pi fun i : Fin n => μ ((Fin.last n).succAbove i)))
      ((Measure.pi fun i : Fin n => μ ((Fin.last n).succAbove i)).prod (μ (Fin.last n))))
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
    Fin.succAbove_last, Fin.init_def] using hs.comp h

/-- Append the last coordinate to recover the finite product measure. -/
theorem measurePreserving_finSnoc {n : ℕ} (μ : Fin (n + 1) → Measure X)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (fun z : (Fin n → X) × X => Fin.snoc z.1 z.2)
      ((Measure.pi fun i : Fin n => μ i.castSucc).prod (μ (Fin.last n))) (Measure.pi μ) := by
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using measurable_snd
    · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  · have h := (measurePreserving_finInitLast μ).map_eq
    rw [← h, Measure.map_map]
    · simpa only [Function.comp_def, Fin.snoc_init_self, id_eq] using (Measure.map_id' (μ := Measure.pi μ))
    · apply measurable_pi_iff.mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using measurable_snd
      · simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
    · exact (measurePreserving_finInitLast μ).measurable

/-- Sequential triangular transformation: step `n` sees exactly the preceding
input rows and the new row. -/
def sequentialMap (g : (n : ℕ) → (Fin n → X) → X → Y) :
    (n : ℕ) → (Fin n → X) → Fin n → Y
  | 0, _ => Fin.elim0
  | n + 1, x => Fin.snoc (sequentialMap g n (Fin.init x))
      (g n (Fin.init x) (x (Fin.last n)))

/-- Joint product law for a finite measurable sequential transform with
almost-everywhere constant fibre pushforwards. This proves independence rather
than assuming it, and tolerates exceptional degenerate prefixes of measure zero. -/
theorem measurePreserving_sequentialMap (μ : Measure X) [SigmaFinite μ]
    (ν : ℕ → Measure Y) [∀ n, SigmaFinite (ν n)]
    (g : (n : ℕ) → (Fin n → X) → X → Y)
    (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (hlaw : ∀ n, ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), Measure.map (g n x) μ = ν n)
    (n : ℕ) :
    MeasurePreserving (sequentialMap g n) (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun i : Fin n => ν i.val)) := by
  induction n with
  | zero =>
    refine ⟨measurable_pi_iff.mpr (fun i => Fin.elim0 i), ?_⟩
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [Measure.map_dirac]
    · congr 1
  | succ n ih =>
    have hsplit := measurePreserving_finInitLast (fun _ : Fin (n + 1) => μ)
    have hskew := ih.skew_product (hg n) (hlaw n)
    have hsnoc := measurePreserving_finSnoc (fun i : Fin (n + 1) => ν i.val)
    simpa [Function.comp_def, sequentialMap] using hsnoc.comp (hskew.comp hsplit)

/-- Equality of the actual finite pushforward law to the product of one-step laws. -/
theorem map_sequentialMap (μ : Measure X) [SigmaFinite μ]
    (ν : ℕ → Measure Y) [∀ n, SigmaFinite (ν n)]
    (g : (n : ℕ) → (Fin n → X) → X → Y)
    (hg : ∀ n, Measurable (Function.uncurry (g n)))
    (hlaw : ∀ n, ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), Measure.map (g n x) μ = ν n)
    (n : ℕ) :
    Measure.map (sequentialMap g n) (Measure.pi (fun _ : Fin n => μ)) =
      Measure.pi (fun i : Fin n => ν i.val) :=
  (measurePreserving_sequentialMap μ ν g hg hlaw n).map_eq

/-- Finite-horizon form: laws are required only for the steps actually executed. -/
theorem measurePreserving_sequentialMap_of_lt (μ : Measure X) [SigmaFinite μ]
    (ν : ℕ → Measure Y) [∀ n, SigmaFinite (ν n)]
    (g : (n : ℕ) → (Fin n → X) → X → Y) (n : ℕ)
    (hg : ∀ k < n, Measurable (Function.uncurry (g k)))
    (hlaw : ∀ k < n, ∀ᵐ x ∂Measure.pi (fun _ : Fin k => μ),
      Measure.map (g k x) μ = ν k) :
    MeasurePreserving (sequentialMap g n) (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun i : Fin n => ν i.val)) := by
  induction n with
  | zero =>
    refine ⟨measurable_pi_iff.mpr (fun i => Fin.elim0 i), ?_⟩
    rw [Measure.pi_of_empty, Measure.pi_of_empty, Measure.map_dirac]
    · congr 1
  | succ n ih =>
    have hp := ih (fun k hk => hg k (by omega)) (fun k hk => hlaw k (by omega))
    have hsplit := measurePreserving_finInitLast (fun _ : Fin (n + 1) => μ)
    have hskew := hp.skew_product (hg n (by omega)) (hlaw n (by omega))
    have hsnoc := measurePreserving_finSnoc (fun i : Fin (n + 1) => ν i.val)
    simpa [Function.comp_def, sequentialMap] using hsnoc.comp (hskew.comp hsplit)

end GaussianMixedNormHelpers
