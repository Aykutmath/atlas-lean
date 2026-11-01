import Section_10_Zonoid.Hypercube.Sampling
import Section_10_Zonoid.Hypercube.BernoulliGeometry
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/- The index law is the exact finite atomic probability law. Different labels
may map to the same projected or lifted point. Zero masses are permitted. -/

noncomputable section

namespace Hypercube.FiniteAtomic

open MeasureTheory

def labelMeasure {N : Nat} (q : Fin N -> Real) : Measure (Fin N) :=
  Finset.sum Finset.univ
    (fun i => HSMul.hSMul (Real.toNNReal (q i)) (Measure.dirac i))

instance labelMeasure_isFinite {N : Nat} (q : Fin N -> Real) :
    IsFiniteMeasure (labelMeasure q) := by
  unfold labelMeasure
  infer_instance

theorem labelMeasure_singleton {N : Nat} (q : Fin N -> Real) (i : Fin N) :
    labelMeasure q {i} = ENNReal.ofReal (q i) := by
  unfold labelMeasure
  rw [Measure.finsetSum_apply]
  have hpoint (j : Fin N) :
      (HSMul.hSMul (Real.toNNReal (q j)) (Measure.dirac j) : Measure (Fin N)) {i} =
        if j = i then ENNReal.ofReal (q j) else 0 := by
    change ((Real.toNNReal (q j) : NNReal) : ENNReal) * (Measure.dirac j) {i} = _
    by_cases hj : j = i
    all_goals simp [hj, ENNReal.ofReal]
  simp_rw [hpoint]
  simp

theorem labelMeasure_real_singleton {N : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (i : Fin N) : (labelMeasure q).real {i} = q i := by
  rw [measureReal_def, labelMeasure_singleton, ENNReal.toReal_ofReal (hq i)]

theorem iid_real_singleton {N n : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (f : Fin n -> Fin N) :
    (Measure.pi (fun _ : Fin n => labelMeasure q)).real {f} =
      Finset.prod Finset.univ (fun i => q (f i)) := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [labelMeasure_singleton, ENNReal.toReal_ofReal (hq (f i))]

theorem iid_integral_eq_finiteExpectation {N n : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (F : (Fin n -> Fin N) -> Real) :
    integral (Measure.pi (fun _ : Fin n => labelMeasure q)) F =
      Sampling.finiteExpectation q F := by
  rw [integral_fintype Integrable.of_finite]
  unfold Sampling.finiteExpectation
  apply Finset.sum_congr rfl
  intro f _
  rw [iid_real_singleton q hq f]
  rfl

theorem labelMeasure_isProbability {N : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1) :
    IsProbabilityMeasure (labelMeasure q) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h : integral (labelMeasure q) (fun _ : Fin N => (1 : Real)) =
      Finset.sum Finset.univ q := by
    rw [integral_fintype Integrable.of_finite]
    simp only [labelMeasure_real_singleton q hq, smul_eq_mul, mul_one]
  have hmass : (labelMeasure q).real Set.univ = Finset.sum Finset.univ q := by
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  exact hmass.trans hqsum

theorem label_integral {N : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (F : Fin N -> Real) :
    integral (labelMeasure q) F =
      Finset.sum Finset.univ (fun i => q i * F i) := by
  rw [integral_fintype Integrable.of_finite]
  simp only [labelMeasure_real_singleton q hq, smul_eq_mul]

theorem finite_measure_atomic_decomposition {N : Nat} (mu : Measure (Fin N))
    [IsFiniteMeasure mu] : labelMeasure (fun i => mu.real {i}) = mu := by
  apply Measure.ext_of_measureReal_singleton
  intro i
  exact labelMeasure_real_singleton _ (fun j => measureReal_nonneg) i

theorem finite_probability_masses_sum {N : Nat} (mu : Measure (Fin N))
    [IsProbabilityMeasure mu] : Finset.sum Finset.univ (fun i => mu.real {i}) = 1 := by
  have h : integral mu (fun _ : Fin N => (1 : Real)) =
      Finset.sum Finset.univ (fun i => mu.real {i} * 1) := by
    simpa only [smul_eq_mul] using
      (integral_fintype (show Integrable (fun _ : Fin N => (1 : Real)) mu
        from Integrable.of_finite))
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h.symm

theorem iid_finite_measure_integral {N n : Nat} (mu : Measure (Fin N))
    [IsFiniteMeasure mu] (F : (Fin n -> Fin N) -> Real) :
    integral (Measure.pi (fun _ : Fin n => mu)) F =
      Sampling.finiteExpectation (fun i => mu.real {i}) F := by
  calc
    _ = integral (Measure.pi (fun _ : Fin n => labelMeasure (fun i => mu.real {i}))) F := by
      rw [finite_measure_atomic_decomposition mu]
    _ = _ := iid_integral_eq_finiteExpectation _ (fun i => measureReal_nonneg) _

theorem iid_affineDet_normalization {N m : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (w : Fin N -> Geometry.Point m) :
    integral (Measure.pi (fun _ : Fin (m + 1) => labelMeasure q))
      (fun f => |Geometry.affineDet (fun i => w (f i))|) =
      ((m + 1).factorial : Real) * Bernoulli.finiteD q (Bernoulli.subsetAffineDet w) m := by
  rw [iid_integral_eq_finiteExpectation q hq, Sampling.finite_affineDet_normalization]

theorem iid_radonMass_normalization {N m : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (w : Fin N -> Geometry.Point m) :
    integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
      (fun f => Geometry.radonMass (fun j => w (f j))) =
      ((m + 2).factorial : Real) / 2 * Bernoulli.finiteD q (Bernoulli.subsetAffineDet w) m := by
  rw [iid_integral_eq_finiteExpectation q hq, Sampling.finite_radonMass_normalization q hqsum]

theorem iid_height_normalization {N m : Nat} (q X : Fin N -> Real)
    (hq : forall i, 0 <= q i) (w : Fin N -> Geometry.Point m) :
    integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) =
      ((m + 2).factorial : Real) * Bernoulli.finiteL q X (Bernoulli.subsetAffineDet w) m := by
  rw [iid_integral_eq_finiteExpectation q hq, Sampling.finite_height_normalization]

/- The geometric premises are deliberately visible. This theorem discharges
the sampling and probability interface, but is not a proof of those premises. -/
theorem iid_binary_gate_of_finiteL_bound {N m : Nat} (q X : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (w : Fin N -> Geometry.Point m)
    (hbound : Bernoulli.finiteL q X (Bernoulli.subsetAffineDet w) m <=
      (Finset.sum Finset.univ (fun i => q i * X i)) *
        (1 - Finset.sum Finset.univ (fun i => q i * X i)) *
          Bernoulli.finiteD q (Bernoulli.subsetAffineDet w) m) :
    let p := integral (labelMeasure q) X
    integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
          (fun f => Geometry.radonMass (fun j => w (f j))) := by
  dsimp only
  rw [label_integral q hq, iid_height_normalization q X hq w,
    iid_radonMass_normalization q hq hqsum w]
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (show 0 <= ((m + 2).factorial : Real) from Nat.cast_nonneg _)
  convert hscaled using 1
  ring

theorem iid_binary_gate_of_cocycle_and_volume {N m : Nat}
    (q X : Fin N -> Real) (hq : forall i, 0 <= q i)
    (hqsum : Finset.sum Finset.univ q = 1) (w : Fin N -> Geometry.Point m)
    (hbinary : forall i, Or (X i = 0) (X i = 1))
    (hrep : forall I, I.card = m + 1 ->
      Bernoulli.subsetAffineDet w I = (m.factorial : Real) *
        integral volume (Bernoulli.subsetSignedSimplex w I))
    (habsrep : forall I, I.card = m + 1 ->
      |Bernoulli.subsetAffineDet w I| = (m.factorial : Real) *
        integral volume (fun x => |Bernoulli.subsetSignedSimplex w I x|))
    (hcycle : Filter.Eventually
      (fun x => forall J, J.card = m + 2 ->
        BinaryCocycle.increasingAlternatingSum (fun _ => 1)
          (fun I => Bernoulli.subsetSignedSimplex w I x) J = 0) (ae volume)) :
    let p := integral (labelMeasure q) X
    integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
          (fun f => Geometry.radonMass (fun j => w (f j))) := by
  apply iid_binary_gate_of_finiteL_bound q X hq hqsum w
  exact Bernoulli.finite_support_geometric_bound_of_cocycle_and_volume
    w q X hq hqsum hbinary hrep habsrep hcycle

theorem iid_binary_gate {N m : Nat} (q X : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (w : Fin N -> Geometry.Point m)
    (hbinary : forall i, Or (X i = 0) (X i = 1)) :
    let p := integral (labelMeasure q) X
    integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => labelMeasure q))
          (fun f => Geometry.radonMass (fun j => w (f j))) := by
  apply iid_binary_gate_of_finiteL_bound q X hq hqsum w
  exact Bernoulli.finite_support_geometric_bound w q X hq hqsum hbinary

theorem finite_probability_binary_gate {N m : Nat} (mu : Measure (Fin N))
    [IsProbabilityMeasure mu] (X : Fin N -> Real) (w : Fin N -> Geometry.Point m)
    (hbinary : forall i, Or (X i = 0) (X i = 1)) :
    let p := integral mu X
    integral (Measure.pi (fun _ : Fin (m + 2) => mu))
      (fun f => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (f j)) i * X (f i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => mu))
          (fun f => Geometry.radonMass (fun j => w (f j))) := by
  have h := iid_binary_gate (fun i => mu.real {i}) X
    (fun i => measureReal_nonneg) (finite_probability_masses_sum mu) w hbinary
  simpa only [finite_measure_atomic_decomposition mu] using h

section Pushforward

variable {Space : Type*} [MeasurableSpace Space]

def atomicLaw {N : Nat} (q : Fin N -> Real) (points : Fin N -> Space) : Measure Space :=
  Measure.map points (labelMeasure q)

instance atomicLaw_isFinite {N : Nat} (q : Fin N -> Real) (points : Fin N -> Space) :
    IsFiniteMeasure (atomicLaw q points) := by
  unfold atomicLaw
  infer_instance

theorem iid_atomicLaw_map {N n : Nat} (q : Fin N -> Real) (points : Fin N -> Space) :
    Measure.map (fun f : Fin n -> Fin N => fun i => points (f i))
      (Measure.pi (fun _ : Fin n => labelMeasure q)) =
      Measure.pi (fun _ : Fin n => atomicLaw q points) := by
  exact Measure.pi_map_pi (fun _ => (measurable_of_countable points).aemeasurable)

theorem iid_atomicLaw_integral {N n : Nat} (q : Fin N -> Real)
    (hq : forall i, 0 <= q i) (points : Fin N -> Space)
    (F : (Fin n -> Space) -> Real) (hF : StronglyMeasurable F) :
    integral (Measure.pi (fun _ : Fin n => atomicLaw q points)) F =
      Sampling.finiteExpectation q (fun f => F (fun i => points (f i))) := by
  rw [<- iid_atomicLaw_map q points]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) hF]
  exact iid_integral_eq_finiteExpectation q hq _

end Pushforward

end Hypercube.FiniteAtomic
