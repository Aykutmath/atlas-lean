import Section_10_Zonoid.Hypercube.FiniteAtomicGeneric
import Section_10_Zonoid.Hypercube.Statements

/- Exact binary-coordinate gap computation used by the spike extremizers.
These identities are valid for every finite atomic law, including zero masses. -/

noncomputable section

namespace Hypercube.SpikeCounting

open MeasureTheory

theorem binary_abs_difference (a b : Real)
    (ha : Or (a = 0) (a = 1)) (hb : Or (b = 0) (b = 1)) :
    |a - b| = a + b - 2 * a * b := by
  rcases ha with ha | ha
  all_goals rcases hb with hb | hb
  all_goals rw [ha, hb]
  all_goals norm_num

theorem weighted_binary_gap {Index : Type*} [Fintype Index]
    (q f : Index -> Real) (hqsum : Finset.sum Finset.univ q = 1)
    (hf : forall i, Or (f i = 0) (f i = 1)) :
    Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => q i * q j * |f i - f j|)) =
      2 * (Finset.sum Finset.univ (fun i => q i * f i)) *
        (1 - Finset.sum Finset.univ (fun i => q i * f i)) := by
  have hpoint (i j : Index) :
      q i * q j * |f i - f j| =
        (q i * f i) * q j + q i * (q j * f j) -
          2 * (q i * f i) * (q j * f j) := by
    rw [binary_abs_difference (f i) (f j) (hf i) (hf j)]
    ring
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]
  rw [<- Finset.sum_mul, <- Finset.sum_mul, <- Finset.sum_mul]
  rw [hqsum]
  ring_nf
  rw [<- Finset.sum_mul Finset.univ (fun i => q i * f i) (2 : Real)]
  ring

theorem atomic_coordinateGap {Index : Type*} [Fintype Index] [MeasurableSpace Index]
    [MeasurableSingletonClass Index] {d : Nat} (q : Index -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (points : Index -> Paper.Point d) (j : Fin d)
    (hbinary : forall i, Or (points i j = 0) (points i j = 1)) :
    Paper.coordinateGap (FiniteAtomicGeneric.atomicLaw q points) j =
      2 * (Finset.sum Finset.univ (fun i => q i * points i j)) *
        (1 - Finset.sum Finset.univ (fun i => q i * points i j)) := by
  unfold Paper.coordinateGap
  have hF : StronglyMeasurable
      (fun zz : Prod (Paper.Point d) (Paper.Point d) => |zz.1 j - zz.2 j|) := by
    apply Continuous.stronglyMeasurable
    exact (((continuous_apply j).comp continuous_fst).sub
      ((continuous_apply j).comp continuous_snd)).abs
  rw [FiniteAtomicGeneric.pair_atomicLaw_integral q hq points _ hF]
  exact weighted_binary_gap q (fun i => points i j) hqsum hbinary

end Hypercube.SpikeCounting
