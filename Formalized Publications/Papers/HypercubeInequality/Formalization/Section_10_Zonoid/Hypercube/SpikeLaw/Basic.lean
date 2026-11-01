import Section_10_Zonoid.Hypercube.FiniteAtomic
import Section_10_Zonoid.Hypercube.Statements
import Mathlib.Algebra.BigOperators.Fin

/- Source Section 7.3. The last support label denotes the origin and the
first d labels denote the standard basis vectors. This is only a labeling
choice: the atom masses are exactly those displayed in the paper. -/

noncomputable section

open MeasureTheory

namespace Hypercube.SpikeLaw

def basisPoint (d : Nat) (i : Fin d) : Paper.Point d :=
  fun j => if j = i then 1 else 0

def spikePoint (d : Nat) : Fin (d + 1) -> Paper.Point d :=
  Fin.lastCases 0 (basisPoint d)

def spikeWeight (d : Nat) (eps : Real) : Fin (d + 1) -> Real :=
  Fin.lastCases (1 - (d : Real) * eps) (fun _ => eps)

def spikeLaw (d : Nat) (eps : Real) : Measure (Paper.Point d) :=
  FiniteAtomic.atomicLaw (spikeWeight d eps) (spikePoint d)

theorem spikePoint_origin (d : Nat) : spikePoint d (Fin.last d) = 0 := by
  simp only [spikePoint, Fin.lastCases_last]

theorem spikePoint_basis (d : Nat) (i : Fin d) : spikePoint d i.castSucc = basisPoint d i := by
  simp only [spikePoint, Fin.lastCases_castSucc]

theorem spikeWeight_origin (d : Nat) (eps : Real) :
    spikeWeight d eps (Fin.last d) = 1 - (d : Real) * eps := by
  simp only [spikeWeight, Fin.lastCases_last]

theorem spikeWeight_basis (d : Nat) (eps : Real) (i : Fin d) :
    spikeWeight d eps i.castSucc = eps := by
  simp only [spikeWeight, Fin.lastCases_castSucc]

theorem spikeWeight_nonneg (d : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : (d : Real) * eps <= 1) : forall i, 0 <= spikeWeight d eps i := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  next => rw [spikeWeight_origin]; linarith
  next i => simpa only [spikeWeight_basis] using heps

theorem spikeWeight_sum (d : Nat) (eps : Real) :
    Finset.sum Finset.univ (spikeWeight d eps) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [spikeWeight_origin, spikeWeight_basis, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem spikeLaw_isProbability (d : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : (d : Real) * eps <= 1) : IsProbabilityMeasure (spikeLaw d eps) := by
  have : IsProbabilityMeasure (FiniteAtomic.labelMeasure (spikeWeight d eps)) :=
    FiniteAtomic.labelMeasure_isProbability _ (spikeWeight_nonneg d eps heps hd) (spikeWeight_sum d eps)
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable (spikePoint d)).aemeasurable).mpr inferInstance

theorem spikeLaw_firstMoments (d : Nat) (eps : Real) :
    Paper.finiteCoordinateFirstMoments (spikeLaw d eps) := by
  intro j
  unfold spikeLaw FiniteAtomic.atomicLaw
  have hc : Measurable (fun z : Paper.Point d => z j) := measurable_pi_apply j
  apply (integrable_map_measure (continuous_abs.measurable.comp hc).aestronglyMeasurable
    (measurable_of_countable (spikePoint d)).aemeasurable).mpr
  exact Integrable.of_finite

end Hypercube.SpikeLaw
