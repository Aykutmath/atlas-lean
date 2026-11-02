import GaussianEllipsoid.PaperMain
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory Set
open scoped Matrix.Norms.Elementwise
namespace GaussianEllipsoid

private theorem compact_witness_fit_closed {d n : ℕ} (K : Set (Square d))
    (hK : IsCompact K) :
    IsClosed {x : Sample d n | ∃ S ∈ K, ∀ i, quadratic S (x i) = (d : ℝ)} := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h : IsClosed {p : Sample d n × K | ∀ i, quadratic p.2.val (p.1 i) = (d : ℝ)} := by
    simp only [setOf_forall]
    refine isClosed_iInter (fun i => ?_)
    have hx : Continuous (fun p : Sample d n × K => p.1 i) :=
      (continuous_apply i).comp continuous_fst
    have hS : Continuous (fun p : Sample d n × K => (p.2 : Square d)) :=
      continuous_subtype_val.comp continuous_snd
    exact isClosed_eq (hx.dotProduct (hS.matrix_mulVec hx)) continuous_const
  have hp := isClosedMap_fst_of_compactSpace _ h
  convert hp using 1
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    exact ⟨(x, ⟨S, hS⟩), hx, rfl⟩
  · rintro ⟨⟨y, S⟩, hx, hy⟩
    change y = x at hy
    subst y
    exact ⟨S.val, S.property, hx⟩

private def psdBounded (d m : ℕ) : Set (Square d) :=
  {S | S.PosSemidef} ∩ Metric.closedBall 0 (m : ℝ)

private theorem psdBounded_compact (d m : ℕ) : IsCompact (psdBounded d m) := by
  exact (isCompact_closedBall (0 : Square d) (m : ℝ)).inter_left Matrix.posSemidef_is_closed

/-- Exact positive-semidefinite fitting is a Borel event. -/
theorem measurableSet_fitEvent (d n : ℕ) : MeasurableSet (fitEvent d n) := by
  have heq : fitEvent d n = ⋃ m : ℕ,
      {x : Sample d n | ∃ S ∈ psdBounded d m, ∀ i, quadratic S (x i) = (d : ℝ)} := by
    ext x
    simp only [fitEvent, HasFit, Feasible, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨S, hS, hx⟩
      obtain ⟨m, hm⟩ := exists_nat_ge ‖S‖
      exact ⟨m, S, ⟨hS, by simpa using hm⟩, hx⟩
    · rintro ⟨m, S, hS, hx⟩
      exact ⟨S, hS.1, hx⟩
  rw [heq]
  exact MeasurableSet.iUnion fun m => (compact_witness_fit_closed _ (psdBounded_compact d m)).measurableSet

private def pdBounded (d m k : ℕ) : Set (Square d) :=
  psdBounded d m ∩ {S | (1 : ℝ) / (k + 1 : ℝ) ≤ |S.det|}

private theorem pdBounded_compact (d m k : ℕ) : IsCompact (pdBounded d m k) := by
  apply (psdBounded_compact d m).inter_right
  exact isClosed_le continuous_const (by fun_prop)

/-- Exact positive-definite fitting is a Borel event. -/
theorem measurableSet_strictFitEvent (d n : ℕ) : MeasurableSet (strictFitEvent d n) := by
  have heq : strictFitEvent d n = ⋃ m : ℕ, ⋃ k : ℕ,
      {x : Sample d n | ∃ S ∈ pdBounded d m k, ∀ i, quadratic S (x i) = (d : ℝ)} := by
    ext x
    simp only [strictFitEvent, HasStrictFit, StrictlyFeasible, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨S, hS, hx⟩
      obtain ⟨m, hm⟩ := exists_nat_ge ‖S‖
      have hd : 0 < |S.det| := abs_pos.mpr (hS.posSemidef.posDef_iff_det_ne_zero.mp hS)
      obtain ⟨k, hk⟩ := exists_nat_gt ((1 : ℝ) / |S.det|)
      refine ⟨m, k, S, ⟨⟨hS.posSemidef, by simpa using hm⟩, ?_⟩, hx⟩
      dsimp
      have hk' : (1 : ℝ) / |S.det| ≤ (k : ℝ) + 1 := by linarith
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr (by
        have := (div_le_iff₀ hd).mp hk'
        nlinarith)
    · rintro ⟨m, k, S, hS, hx⟩
      refine ⟨S, hS.1.1.posDef_iff_det_ne_zero.mpr ?_, hx⟩
      have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      have habs : 0 < |S.det| := hpos.trans_le hS.2
      exact abs_pos.mp habs
  rw [heq]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun k =>
    (compact_witness_fit_closed _ (pdBounded_compact d m k)).measurableSet

#print axioms measurableSet_fitEvent
#print axioms measurableSet_strictFitEvent
end GaussianEllipsoid
