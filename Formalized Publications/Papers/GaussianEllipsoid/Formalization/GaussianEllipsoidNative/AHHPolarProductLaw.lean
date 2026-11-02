import AHHRadialJensen
import AHHComplexRadialLaw

/-! Joint law of every radius and direction in an iid product-state sample. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set GaussianMixedNormHelpers
namespace AHHRadial

/-- Reordering independent product coordinates, proved with measure-preserving
associators and swaps. -/
theorem cross_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have hr : MeasurePreserving (fun p : B × (C × D) => (p.2.1,(p.1,p.2.2)))
      (μB.prod (μC.prod μD)) (μC.prod (μB.prod μD)) :=
    (measurePreserving_prodAssoc μC μB μD).comp
      ((Measure.measurePreserving_swap.prod (MeasurePreserving.id μD)).comp
        (measurePreserving_prodAssoc μB μC μD).symm)
  exact (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm.comp
    (((MeasurePreserving.id μA).prod hr).comp
      (measurePreserving_prodAssoc μA μB (μC.prod μD)))

abbrev UnitDirection (h : ℕ) := UnitSphere (CE h)
abbrev Directions (n h : ℕ) := Fin n → UnitDirection h × UnitDirection h

def directionPairLaw (h : ℕ) : Measure (UnitDirection h × UnitDirection h) :=
  (sphereLaw (volume : Measure (CE h))).prod (sphereLaw (volume : Measure (CE h)))

def directionsLaw (n h : ℕ) : Measure (Directions n h) :=
  Measure.pi (fun _ : Fin n => directionPairLaw h)

def gaussianPairLaw (h : ℕ) : Measure (CE h × CE h) :=
  (radialGaussianLaw (volume : Measure (CE h)) h).prod
    (radialGaussianLaw (volume : Measure (CE h)) h)

def gaussianPairsLaw (n h : ℕ) : Measure (Fin n → CE h × CE h) :=
  Measure.pi (fun _ : Fin n => gaussianPairLaw h)

def assemblePair (h : ℕ) (p : (Radius × Radius) × (UnitDirection h × UnitDirection h)) :
    CE h × CE h := ((p.1.1 : ℝ) • (p.2.1 : CE h), (p.1.2 : ℝ) • (p.2.2 : CE h))

def assembleSample (n h : ℕ)
    (p : (Fin n → Radius × Radius) × Directions n h) (i : Fin n) : CE h × CE h :=
  assemblePair h (p.1 i, p.2 i)

theorem directionPairLaw_probability (h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (directionPairLaw h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  unfold directionPairLaw
  infer_instance

theorem directionsLaw_probability (n h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (directionsLaw n h) := by
  letI := directionPairLaw_probability h hh
  unfold directionsLaw
  infer_instance

theorem gaussianPairLaw_probability (h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (gaussianPairLaw h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := radialGaussianLaw_isProbabilityMeasure (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  unfold gaussianPairLaw
  infer_instance

theorem assemblePair_preserving (h : ℕ) (hh : 0 < h) :
    MeasurePreserving (assemblePair h) ((radiusPairLaw h).prod (directionPairLaw h))
      (gaussianPairLaw h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  let μ : Measure (CE h) := volume
  have hp : MeasurePreserving (assemble (E := CE h))
      ((sphereLaw μ).prod (radiusLaw μ h)) (radialGaussianLaw μ h) :=
    ⟨measurable_assemble, (radialGaussianLaw_eq_map_polar μ h).symm⟩
  have hq := hp.comp (Measure.measurePreserving_swap
    (μ := radiusLaw μ h) (ν := sphereLaw μ))
  exact (hq.prod hq).comp (cross_preserving (radiusLaw μ h) (radiusLaw μ h)
    (sphereLaw μ) (sphereLaw μ))

/-- Actual iid radial Gaussian factors after reconstructing all independent
Haar directions and radii. -/
theorem assembleSample_preserving (n h : ℕ) (hh : 0 < h) :
    MeasurePreserving (assembleSample n h) ((radiiLaw n h).prod (directionsLaw n h))
      (gaussianPairsLaw n h) := by
  letI := radiusPairLaw_probability h hh
  letI := directionPairLaw_probability h hh
  letI := gaussianPairLaw_probability h hh
  exact (measurePreserving_pi (fun _ : Fin n => (radiusPairLaw h).prod (directionPairLaw h))
    (fun _ => gaussianPairLaw h) (fun _ => assemblePair_preserving h hh)).comp
      (measurePreserving_arrowProdEquivProdArrow (Radius × Radius)
        (UnitDirection h × UnitDirection h) (Fin n)
        (fun _ => radiusPairLaw h) (fun _ => directionPairLaw h)).symm

open AHHGaussian

/-- The literal normalized Gaussian pair, before forming its tensor product. -/
def actualNormalizedPairs (n h : ℕ) (s t : Bool) (x : FourEntries n h)
    (i : Fin n) : CE h × CE h :=
  (normalizedRow h s (fourRealRows n h x i).1,
    normalizedRow h t (fourRealRows n h x i).2)

theorem normalizedPairRow_preserving (h : ℕ) (hh : 0 < h) (s t : Bool) :
    MeasurePreserving (Prod.map (normalizedRow h s) (normalizedRow h t))
      (fourRealRowLaw h) (gaussianPairLaw h) := by
  have hs : MeasurePreserving (normalizedRow h s) (pairRealRowLaw h)
      (radialGaussianLaw (volume : Measure (CE h)) h) :=
    ⟨by unfold normalizedRow normalizedCoordinate; fun_prop, normalizedRow_law h hh s⟩
  have ht : MeasurePreserving (normalizedRow h t) (pairRealRowLaw h)
      (radialGaussianLaw (volume : Measure (CE h)) h) :=
    ⟨by unfold normalizedRow normalizedCoordinate; fun_prop, normalizedRow_law h hh t⟩
  exact hs.prod ht

/-- Actual four-independent-real Gaussian sample has precisely the radial law
used on the Gaussian side of the Jensen comparison. -/
theorem actualNormalizedPairs_preserving (n h : ℕ) (hh : 0 < h) (s t : Bool) :
    MeasurePreserving (actualNormalizedPairs n h s t) (fourGaussianLaw n h)
      (gaussianPairsLaw n h) := by
  letI := gaussianPairLaw_probability h hh
  exact (measurePreserving_pi (fun _ : Fin n => fourRealRowLaw h)
    (fun _ => gaussianPairLaw h) (fun _ => normalizedPairRow_preserving h hh s t)).comp
      (fourRealRows_preserving n h)

#print axioms assembleSample_preserving
#print axioms actualNormalizedPairs_preserving
end AHHRadial
