import Section_10_Zonoid.Hypercube.SpikeLaw.Basic
import Section_10_Zonoid.Hypercube.SpikeCounting

noncomputable section

namespace Hypercube.SpikeLaw

theorem spikePoint_binary (d : Nat) (i : Fin (d + 1)) (j : Fin d) :
    Or (spikePoint d i j = 0) (spikePoint d i j = 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  next =>
    left
    simp [spikePoint_origin]
  next i =>
    rw [spikePoint_basis]
    unfold basisPoint
    split
    next => exact Or.inr rfl
    next => exact Or.inl rfl

theorem spike_coordinate_mean (d : Nat) (eps : Real) (j : Fin d) :
    Finset.sum Finset.univ (fun i => spikeWeight d eps i * spikePoint d i j) = eps := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [spikeWeight_origin, spikePoint_origin, Pi.zero_apply, mul_zero, add_zero,
    spikeWeight_basis, spikePoint_basis, basisPoint]
  simp [mul_ite]

theorem spike_coordinateGap (d : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : (d : Real) * eps <= 1) (j : Fin d) :
    Paper.coordinateGap (spikeLaw d eps) j = 2 * eps * (1 - eps) := by
  change Paper.coordinateGap
    (FiniteAtomicGeneric.atomicLaw (spikeWeight d eps) (spikePoint d)) j = _
  rw [SpikeCounting.atomic_coordinateGap _ (spikeWeight_nonneg d eps heps hd)
    (spikeWeight_sum d eps) (spikePoint d) j (fun i => spikePoint_binary d i j),
    spike_coordinate_mean]

theorem spike_coordinateGap_product (d : Nat) (eps : Real) (heps : 0 <= eps)
    (hd : (d : Real) * eps <= 1) :
    Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j) =
      (2 * eps * (1 - eps)) ^ d := by
  simp_rw [spike_coordinateGap d eps heps hd]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Hypercube.SpikeLaw
