import Section_10_Zonoid.Hypercube.SpikeLaw.Basic
import Section_10_Zonoid.Hypercube.Moments
import Section_10_Zonoid.Hypercube.SpikeLaw.Volume

noncomputable section

open MeasureTheory

namespace Hypercube.SpikeLaw

/- An explicit representation bridge: the Lean labels place the origin last,
but the resulting probability law has exactly the paper's Dirac masses. -/
theorem spikeLaw_dirac (d : Nat) (eps : Real) :
    spikeLaw d eps =
      Finset.sum Finset.univ (fun i : Fin d =>
        HSMul.hSMul (Real.toNNReal eps) (Measure.dirac (basisPoint d i))) +
      HSMul.hSMul (Real.toNNReal (1 - (d : Real) * eps)) (Measure.dirac (0 : Paper.Point d)) := by
  unfold spikeLaw FiniteAtomic.atomicLaw FiniteAtomic.labelMeasure
  rw [Measure.map_finset_sum' (measurable_of_countable (spikePoint d)).aemeasurable]
  simp_rw [Measure.map_smul _ (measurable_of_countable (spikePoint d)).aemeasurable,
    Measure.map_dirac]
  rw [Fin.sum_univ_castSucc]
  simp only [spikeWeight_origin, spikePoint_origin, spikeWeight_basis, spikePoint_basis]

theorem project_basis_castSucc (m : Nat) (i : Fin m) :
    Paper.projectLast (basisPoint (m + 1) i.castSucc) = basisPoint m i := by
  funext j
  simp only [Paper.projectLast, basisPoint, Fin.castSucc_inj]

theorem project_basis_last (m : Nat) :
    Paper.projectLast (basisPoint (m + 1) (Fin.last m)) = 0 := by
  funext j
  simp [Paper.projectLast, basisPoint]

theorem project_zero (m : Nat) :
    Paper.projectLast (0 : Paper.Point (m + 1)) = (0 : Paper.Point m) := rfl

theorem spikeLaw_project (m : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : ((m + 1 : Nat) : Real) * eps <= 1) :
    (spikeLaw (m + 1) eps).map Paper.projectLast = spikeLaw m eps := by
  have hproj : Measurable (Paper.projectLast : Paper.Point (m + 1) -> Paper.Point m) :=
    Moments.projectLast_continuous.measurable
  rw [spikeLaw_dirac, Measure.map_add _ _ hproj,
    Measure.map_finset_sum' hproj.aemeasurable]
  simp_rw [Measure.map_smul _ hproj.aemeasurable, Measure.map_dirac' hproj]
  rw [Fin.sum_univ_castSucc]
  simp only [project_basis_castSucc, project_basis_last, project_zero]
  rw [spikeLaw_dirac]
  have horigin : 0 <= 1 - ((m + 1 : Nat) : Real) * eps := by linarith
  have hmerge : Real.toNNReal eps + Real.toNNReal (1 - ((m + 1 : Nat) : Real) * eps) =
      Real.toNNReal (1 - (m : Real) * eps) := by
    rw [<- Real.toNNReal_add heps horigin]
    congr 1
    push_cast
    ring
  rw [add_assoc, <- add_smul, hmerge]

theorem spike_projected_expectedSimplexVolume (m : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : ((m + 1 : Nat) : Real) * eps <= 1) :
    Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast) =
      ((m + 1 : Nat) : Real) * (1 - (m : Real) * eps) * eps ^ m := by
  have hm : (m : Real) * eps <= 1 := by push_cast at hd; nlinarith
  rw [spikeLaw_project m eps heps hd, spike_expectedSimplexVolume m eps heps hm]

end Hypercube.SpikeLaw
