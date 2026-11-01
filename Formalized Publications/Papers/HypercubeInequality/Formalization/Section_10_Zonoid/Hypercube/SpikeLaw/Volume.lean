import Section_10_Zonoid.Hypercube.SpikeLaw.Basic
import Section_10_Zonoid.Hypercube.EndpointAssembly

noncomputable section

namespace Hypercube.SpikeLaw

open MeasureTheory

theorem spike_affine_minor (d : Nat) :
    (Geometry.affineMatrix (spikePoint d)).submatrix
      (Fin.last d).succAbove (Fin.last d).succAbove = 1 := by
  funext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last,
    Geometry.affineMatrix, Fin.lastCases_castSucc, spikePoint_basis, basisPoint,
    Matrix.one_apply]
  simp only [eq_comm]

theorem spike_affineDet (d : Nat) : Geometry.affineDet (spikePoint d) = 1 := by
  unfold Geometry.affineDet
  rw [Matrix.det_succ_row _ (Fin.last d), Fin.sum_univ_castSucc]
  have hzero : Finset.sum Finset.univ
      (fun j : Fin d => (-1 : Real) ^ ((Fin.last d).val + j.castSucc.val) *
        Geometry.affineMatrix (spikePoint d) (Fin.last d) j.castSucc *
        ((Geometry.affineMatrix (spikePoint d)).submatrix
          (Fin.last d).succAbove j.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [Geometry.affineMatrix, Fin.lastCases_castSucc, spikePoint_origin,
      Pi.zero_apply, mul_zero, zero_mul]
  rw [hzero, zero_add, spike_affine_minor, Matrix.det_one]
  simp only [Geometry.affineMatrix, Fin.lastCases_last, Fin.val_last, mul_one]
  rw [show d + d = 2 * d from by omega, pow_mul]
  norm_num

theorem univ_orderEmbOfFin {n : Nat}
    (hcard : (Finset.univ : Finset (Fin n)).card = n) (i : Fin n) :
    (Finset.univ : Finset (Fin n)).orderEmbOfFin hcard i = i := by
  have h : (OrderIso.refl (Fin n)).toOrderEmbedding =
      (Finset.univ : Finset (Fin n)).orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique' hcard
    intro a
    exact Finset.mem_univ _
  exact (congrArg (fun e => e i) h).symm

theorem subsetAffineDet_spike_univ (d : Nat) :
    Bernoulli.subsetAffineDet (spikePoint d) Finset.univ = 1 := by
  have hcard : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 := by simp
  rw [Bernoulli.subsetAffineDet_of_card _ _ hcard]
  have hpoint : (fun i => spikePoint d (Finset.univ.orderEmbOfFin hcard i)) = spikePoint d := by
    funext i
    rw [univ_orderEmbOfFin hcard i]
  rw [hpoint, spike_affineDet]

theorem spikeWeight_prod (d : Nat) (eps : Real) :
    Finset.prod Finset.univ (spikeWeight d eps) =
      (1 - (d : Real) * eps) * eps ^ d := by
  rw [Fin.prod_univ_castSucc]
  simp only [spikeWeight_origin, spikeWeight_basis, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

theorem spike_finiteD (d : Nat) (eps : Real) :
    Bernoulli.finiteD (spikeWeight d eps)
      (Bernoulli.subsetAffineDet (spikePoint d)) d =
      (1 - (d : Real) * eps) * eps ^ d := by
  unfold Bernoulli.finiteD
  have hcard : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 := by simp
  have hpower : (Finset.univ : Finset (Fin (d + 1))).powersetCard (d + 1) =
      {Finset.univ} := by
    simpa only [hcard] using (Finset.powersetCard_self (Finset.univ : Finset (Fin (d + 1))))
  rw [hpower, Finset.sum_singleton,
    subsetAffineDet_spike_univ]
  simp only [abs_one, mul_one]
  exact spikeWeight_prod d eps

theorem spike_expectedSimplexVolume (d : Nat) (eps : Real)
    (heps : 0 <= eps) (hd : (d : Real) * eps <= 1) :
    Paper.expectedSimplexVolume (spikeLaw d eps) =
      ((d + 1 : Nat) : Real) * (1 - (d : Real) * eps) * eps ^ d := by
  have hnorm := EndpointAssembly.expected_volume_normalization (spikeLaw d eps)
  unfold spikeLaw at hnorm
  have hF : StronglyMeasurable
      (fun z : Fin (d + 1) -> Paper.Point d => |Geometry.affineDet z|) :=
    (continuous_abs.comp EndpointAssembly.affineDet_continuous).stronglyMeasurable
  rw [FiniteAtomic.iid_atomicLaw_integral (spikeWeight d eps)
    (spikeWeight_nonneg d eps heps hd) (spikePoint d) _
      hF,
    Sampling.finite_affineDet_normalization, spike_finiteD] at hnorm
  have hfac : ((d + 1).factorial : Real) =
      ((d + 1 : Nat) : Real) * (d.factorial : Real) := by
    exact_mod_cast Nat.factorial_succ d
  have hnonzero : Not ((d.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero d
  apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hnonzero
  rw [hfac] at hnorm
  calc
    _ = ((d + 1 : Nat) : Real) * (d.factorial : Real) *
        ((1 - (d : Real) * eps) * eps ^ d) := hnorm
    _ = _ := by ring

end Hypercube.SpikeLaw
