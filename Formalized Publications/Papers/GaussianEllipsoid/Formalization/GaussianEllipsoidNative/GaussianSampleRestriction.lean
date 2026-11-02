import GaussianDisjointSamples
import QuadraticSamplePadding

open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open GaussianEllipsoid.ProjectedClusters
open scoped Topology
namespace GaussianEllipsoidFinalPassage

/-- Literal sample restriction along a deterministic index injection. -/
def restrictRows {n N d : ℕ} (e : Fin n ↪ Fin N)
    (X : Fin N → Euclid d) : Fin n → Euclid d := fun i => X (e i)

/-- Any fixed injective sample restriction has the smaller actual iid law. -/
theorem restrictRows_preserving {n N d : ℕ} (e : Fin n ↪ Fin N) :
    MeasurePreserving (restrictRows (d:=d) e)
      (Measure.pi (fun _ : Fin N => euclideanGaussianLaw (Fin d)))
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))) := by
  have h := (entriesToRows_preserving n d).comp
    ((selectEntries_preserving (h:=d) e).comp (rowsToEntries_preserving N d))
  convert! h using 1

/-- Every witness that fits a full sample also fits a restricted sample. This
covers exact quadratic fitting with any fixed spectral constraint. -/
def witnessEvent {S : Type*} (C : Set S) {d : ℕ} (R : S → Euclid d → Prop)
    (n : ℕ) : Set (Fin n → Euclid d) := {X | ∃ s ∈ C, ∀ i, R s (X i)}

theorem witnessEvent_restriction {S : Type*} (C : Set S) {d n N : ℕ}
    (R : S → Euclid d → Prop) (e : Fin n ↪ Fin N)
    (X : Fin N → Euclid d) (hX : X ∈ witnessEvent C R N) :
    restrictRows e X ∈ witnessEvent C R n := by
  obtain ⟨s,hs,hfit⟩ := hX
  exact ⟨s,hs,fun i => hfit (e i)⟩

/-- Quantitative monotonicity for exact fitting under genuine Gaussian sample
extension. Measurability is the ordinary event requirement, not an assumed
probabilistic comparison. -/
theorem witnessEvent_failure_le {S : Type*} (C : Set S) {d n N : ℕ}
    (R : S → Euclid d → Prop) (e : Fin n ↪ Fin N)
    (hsmall : MeasurableSet (witnessEvent C R n)) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real (witnessEvent C R n)ᶜ ≤
      (Measure.pi (fun _ : Fin N => euclideanGaussianLaw (Fin d))).real (witnessEvent C R N)ᶜ := by
  have hp := restrictRows_preserving (d:=d) e
  rw [← hp.measureReal_preimage hsmall.compl.nullMeasurableSet]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro X hX hbig
  exact hX (witnessEvent_restriction C R e X hbig)

/-- First n samples, with all finite edge cases allowed. -/
def prefixEmbedding {n N : ℕ} (h : n ≤ N) : Fin n ↪ Fin N where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  inj' := by intro i j hij; exact Fin.ext (congrArg (fun z : Fin N => z.val) hij)

/-- Transfer a vanishing bad probability from any pointwise dominating sample
sequence. Together with quadratic padding this preserves the main theorem's
full strict-limsup quantifier, even at zero or oscillating aspect ratio. -/
theorem witnessEvent_failure_tendsto_of_dominating
    {S : ℕ → Type*} (C : ∀ d, Set (S d)) (R : ∀ d, S d → Euclid d → Prop)
    (n N : ℕ → ℕ) (hnN : ∀ d, n d ≤ N d)
    (hmeas : ∀ d, MeasurableSet (witnessEvent (C d) (R d) (n d)))
    (hlim : Tendsto (fun d =>
      (Measure.pi (fun _ : Fin (N d) => euclideanGaussianLaw (Fin d))).real
        (witnessEvent (C d) (R d) (N d))ᶜ) atTop (𝓝 0)) :
    Tendsto (fun d =>
      (Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d))).real
        (witnessEvent (C d) (R d) (n d))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro d
  exact witnessEvent_failure_le (C d) (R d) (prefixEmbedding (hnN d)) (hmeas d)

/-- Compact witness constraints and closed observation equations give a
closed fitting event. This supplies the ordinary measurability input above
for bounded spectral/convex constraint sets. -/
theorem isClosed_witnessEvent {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsCompact C) {d n : ℕ}
    (R : S → Euclid d → Prop) (hR : IsClosed {p : S × Euclid d | R p.1 p.2}) :
    IsClosed (witnessEvent C R n) := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let E : Set (C × (Fin n → Euclid d)) := {p | ∀ i, R p.1.val (p.2 i)}
  have hE : IsClosed E := by
    change IsClosed {p : C × (Fin n → Euclid d) | ∀ i, R p.1.val (p.2 i)}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    have hf : Continuous (fun p : C × (Fin n → Euclid d) => (p.1.val,p.2 i)) := by fun_prop
    exact hR.preimage hf
  have he : Prod.snd '' E = witnessEvent C R n := by
    ext X
    constructor
    · rintro ⟨⟨s,Y⟩,hY,rfl⟩
      exact ⟨s.val,s.property,hY⟩
    · rintro ⟨s,hs,hfit⟩
      exact ⟨(⟨s,hs⟩,X),hfit,rfl⟩
  rw [← he]
  exact isClosedMap_snd_of_compactSpace E hE

theorem measurableSet_witnessEvent {S : Type*} [TopologicalSpace S]
    (C : Set S) (hC : IsCompact C) {d n : ℕ}
    (R : S → Euclid d → Prop) (hR : IsClosed {p : S × Euclid d | R p.1 p.2}) :
    MeasurableSet (witnessEvent C R n) :=
  (isClosed_witnessEvent C hC R hR).measurableSet

/-- A closed constraint set in a proper normed space has a Borel witness
fitting event, even when the witnesses themselves have no uniform norm bound.
This includes the entire finite-dimensional PSD cone. -/
theorem measurableSet_witnessEvent_of_isClosed {S : Type*}
    [NormedAddCommGroup S] [ProperSpace S] (C : Set S) (hC : IsClosed C) {d n : ℕ}
    (R : S → Euclid d → Prop) (hR : IsClosed {p : S × Euclid d | R p.1 p.2}) :
    MeasurableSet (witnessEvent C R n) := by
  have he : witnessEvent C R n =
      ⋃ m : ℕ, witnessEvent (C ∩ Metric.closedBall 0 (m:ℝ)) R n := by
    ext X
    constructor
    · rintro ⟨s,hs,hfit⟩
      apply Set.mem_iUnion.mpr
      refine ⟨⌈‖s‖⌉₊,s,⟨hs,?_⟩,hfit⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using Nat.le_ceil ‖s‖
    · intro hX
      obtain ⟨m,s,hs,hfit⟩ := Set.mem_iUnion.mp hX
      exact ⟨s,hs.1,hfit⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro m
  exact measurableSet_witnessEvent _ ((isCompact_closedBall (0:S) (m:ℝ)).inter_left hC) R hR

/-- Success probability is monotone downwards with the number of iid samples.
This is the direction used by the above-threshold assembly. -/
theorem witnessEvent_success_le {S : Type*} (C : Set S) {d n N : ℕ}
    (R : S → Euclid d → Prop) (e : Fin n ↪ Fin N)
    (hsmall : MeasurableSet (witnessEvent C R n)) :
    (Measure.pi (fun _ : Fin N => euclideanGaussianLaw (Fin d))).real (witnessEvent C R N) ≤
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real (witnessEvent C R n) := by
  have hp := restrictRows_preserving (d:=d) e
  rw [← hp.measureReal_preimage hsmall.nullMeasurableSet]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro X hX
  exact witnessEvent_restriction C R e X hX

#print axioms measurableSet_witnessEvent_of_isClosed
#print axioms witnessEvent_success_le
#print axioms isClosed_witnessEvent
#print axioms measurableSet_witnessEvent
#print axioms restrictRows_preserving
#print axioms witnessEvent_restriction
#print axioms witnessEvent_failure_le
#print axioms witnessEvent_failure_tendsto_of_dominating
end GaussianEllipsoidFinalPassage
