import Section_10_Zonoid.Hypercube.FiniteAtomic
import Mathlib.MeasureTheory.Integral.Prod

/- The finite-atomic integral bridge, with an arbitrary finite label type.
This allows the cube vertices to retain their paper-facing indexing. -/

noncomputable section

namespace Hypercube.FiniteAtomicGeneric

open MeasureTheory

variable {Index : Type*} [Fintype Index] [MeasurableSpace Index]
  [MeasurableSingletonClass Index]

def labelMeasure (q : Index -> Real) : Measure Index :=
  Finset.sum Finset.univ
    (fun i => HSMul.hSMul (Real.toNNReal (q i)) (Measure.dirac i))

instance labelMeasure_isFinite (q : Index -> Real) : IsFiniteMeasure (labelMeasure q) := by
  unfold labelMeasure
  infer_instance

theorem labelMeasure_singleton (q : Index -> Real) (i : Index) :
    labelMeasure q {i} = ENNReal.ofReal (q i) := by
  classical
  unfold labelMeasure
  rw [Measure.finsetSum_apply]
  have hpoint (j : Index) :
      (HSMul.hSMul (Real.toNNReal (q j)) (Measure.dirac j) : Measure Index) {i} =
        if j = i then ENNReal.ofReal (q j) else 0 := by
    change ((Real.toNNReal (q j) : NNReal) : ENNReal) * (Measure.dirac j) {i} = _
    by_cases hj : j = i
    all_goals simp [hj, ENNReal.ofReal]
  simp_rw [hpoint]
  simp

theorem labelMeasure_real_singleton (q : Index -> Real)
    (hq : forall i, 0 <= q i) (i : Index) : (labelMeasure q).real {i} = q i := by
  rw [measureReal_def, labelMeasure_singleton, ENNReal.toReal_ofReal (hq i)]

theorem label_integral (q : Index -> Real) (hq : forall i, 0 <= q i) (F : Index -> Real) :
    integral (labelMeasure q) F = Finset.sum Finset.univ (fun i => q i * F i) := by
  rw [integral_fintype Integrable.of_finite]
  simp only [labelMeasure_real_singleton q hq, smul_eq_mul]

theorem labelMeasure_isProbability (q : Index -> Real) (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum Finset.univ q = 1) : IsProbabilityMeasure (labelMeasure q) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := label_integral q hq (fun _ => (1 : Real))
  have hmass : (labelMeasure q).real Set.univ = Finset.sum Finset.univ q := by
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  exact hmass.trans hqsum

theorem iid_real_singleton {n : Nat} (q : Index -> Real) (hq : forall i, 0 <= q i)
    (f : Fin n -> Index) :
    (Measure.pi (fun _ : Fin n => labelMeasure q)).real {f} =
      Finset.prod Finset.univ (fun i => q (f i)) := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [labelMeasure_singleton, ENNReal.toReal_ofReal (hq (f i))]

theorem iid_integral {n : Nat} (q : Index -> Real) (hq : forall i, 0 <= q i)
    (F : (Fin n -> Index) -> Real) :
    integral (Measure.pi (fun _ : Fin n => labelMeasure q)) F =
      Finset.sum Finset.univ
        (fun f : Fin n -> Index => Finset.prod Finset.univ (fun i => q (f i)) * F f) := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro f _
  rw [iid_real_singleton q hq f]
  rfl

theorem pair_integral (q : Index -> Real) (hq : forall i, 0 <= q i)
    (F : Prod Index Index -> Real) :
    integral ((labelMeasure q).prod (labelMeasure q)) F =
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => q i * q j * F (i, j))) := by
  rw [integral_prod F Integrable.of_finite, label_integral q hq]
  simp_rw [label_integral q hq, Finset.mul_sum, mul_assoc]

theorem finite_probability_binary_gate {m : Nat} (mu : Measure Index)
    [IsProbabilityMeasure mu] (X : Index -> Real) (w : Index -> Geometry.Point m)
    (hbinary : forall i, Or (X i = 0) (X i = 1)) :
    let p := integral mu X
    integral (Measure.pi (fun _ : Fin (m + 2) => mu))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => mu))
          (fun f => Geometry.radonMass (fun j => w (f j))) := by
  let e := Fintype.equivFin Index
  let nu := Measure.map e mu
  have : IsProbabilityMeasure nu := by
    dsimp only [nu]
    infer_instance
  have h := FiniteAtomic.finite_probability_binary_gate nu
    (fun i => X (e.symm i)) (fun i => w (e.symm i)) (fun i => hbinary (e.symm i))
  have hpi : Measure.pi (fun _ : Fin (m + 2) => nu) =
      Measure.map (fun f : Fin (m + 2) -> Index => fun i => e (f i))
        (Measure.pi (fun _ : Fin (m + 2) => mu)) := by
    exact (Measure.pi_map_pi (fun _ => (measurable_of_countable e).aemeasurable)).symm
  dsimp only at h
  rw [hpi] at h
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable] at h
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable] at h
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable] at h
  simpa only [Equiv.symm_apply_apply] using h

section Pushforward

variable {Space : Type*} [MeasurableSpace Space]

def atomicLaw (q : Index -> Real) (points : Index -> Space) : Measure Space :=
  Measure.map points (labelMeasure q)

instance atomicLaw_isFinite (q : Index -> Real) (points : Index -> Space) :
    IsFiniteMeasure (atomicLaw q points) := by
  unfold atomicLaw
  infer_instance

theorem iid_atomicLaw_map {n : Nat} (q : Index -> Real) (points : Index -> Space) :
    Measure.map (fun f : Fin n -> Index => fun i => points (f i))
      (Measure.pi (fun _ : Fin n => labelMeasure q)) =
      Measure.pi (fun _ : Fin n => atomicLaw q points) := by
  exact Measure.pi_map_pi (fun _ => (measurable_of_countable points).aemeasurable)

theorem iid_atomicLaw_integral {n : Nat} (q : Index -> Real)
    (hq : forall i, 0 <= q i) (points : Index -> Space)
    (F : (Fin n -> Space) -> Real) (hF : StronglyMeasurable F) :
    integral (Measure.pi (fun _ : Fin n => atomicLaw q points)) F =
      Finset.sum Finset.univ (fun f : Fin n -> Index =>
        Finset.prod Finset.univ (fun i => q (f i)) * F (fun i => points (f i))) := by
  rw [<- iid_atomicLaw_map q points]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) hF]
  exact iid_integral q hq _

theorem pair_atomicLaw_integral (q : Index -> Real) (hq : forall i, 0 <= q i)
    (points : Index -> Space) (F : Prod Space Space -> Real)
    (hF : StronglyMeasurable F) :
    integral ((atomicLaw q points).prod (atomicLaw q points)) F =
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => q i * q j * F (points i, points j))) := by
  unfold atomicLaw
  rw [Measure.map_prod_map (labelMeasure q) (labelMeasure q)
    (measurable_of_countable points) (measurable_of_countable points)]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) hF]
  exact pair_integral q hq _

end Pushforward

end Hypercube.FiniteAtomicGeneric
