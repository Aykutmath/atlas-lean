import Section_10_Zonoid.Hypercube.SpikeLaw.Basic

noncomputable section

open MeasureTheory

namespace Hypercube.SpikeLaw

def spikeCube (d : Nat) : Fin (d + 1) -> Paper.Cube d :=
  Fin.lastCases (fun _ => false) (fun i j => decide (j = i))

def spikeCubeLaw (d : Nat) (eps : Real) : Measure (Paper.Cube d) :=
  FiniteAtomic.atomicLaw (spikeWeight d eps) (spikeCube d)

theorem cubePoint_spikeCube (d : Nat) (i : Fin (d + 1)) :
    Paper.cubePoint (spikeCube d i) = spikePoint d i := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  next =>
    funext j
    simp [Paper.cubePoint, spikeCube, spikePoint]
  next i =>
    funext j
    simp [Paper.cubePoint, spikeCube, spikePoint, basisPoint]

theorem spikeCubeLaw_pushforward (d : Nat) (eps : Real) :
    (spikeCubeLaw d eps).map Paper.cubePoint = spikeLaw d eps := by
  unfold spikeCubeLaw spikeLaw FiniteAtomic.atomicLaw
  rw [Measure.map_map (measurable_of_finite Paper.cubePoint) (measurable_of_countable (spikeCube d))]
  congr 1
  funext i
  exact cubePoint_spikeCube d i

theorem spikeCubeLaw_isProbability (d : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : (d : Real) * eps <= 1) : IsProbabilityMeasure (spikeCubeLaw d eps) := by
  have : IsProbabilityMeasure (FiniteAtomic.labelMeasure (spikeWeight d eps)) :=
    FiniteAtomic.labelMeasure_isProbability _ (spikeWeight_nonneg d eps heps hd) (spikeWeight_sum d eps)
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable (spikeCube d)).aemeasurable).mpr inferInstance

end Hypercube.SpikeLaw
