import Section_10_Zonoid.Hypercube.FiniteAtomicGeneric

/- Source: the split-label reduction for arbitrary conditional Bernoulli
parameters. Both bits may have the same projected point, including endpoints. -/

noncomputable section

namespace Hypercube.BinaryLift

open MeasureTheory

abbrev Label (N : Nat) := Prod (Fin N) (Fin 2)

def splitMass {N : Nat} (q r : Fin N -> Real) (a : Label N) : Real :=
  q a.1 * if a.2 = 0 then 1 - r a.1 else r a.1

def bit {N : Nat} (a : Label N) : Real := (a.2.val : Real)

def splitLaw {N : Nat} (q r : Fin N -> Real) : Measure (Label N) :=
  FiniteAtomicGeneric.labelMeasure (splitMass q r)

instance splitLaw_isFinite {N : Nat} (q r : Fin N -> Real) :
    IsFiniteMeasure (splitLaw q r) := by
  unfold splitLaw
  infer_instance

theorem splitMass_nonneg {N : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) (a : Label N) : 0 <= splitMass q r a := by
  unfold splitMass
  split
  case isTrue h => exact mul_nonneg (hq a.1) (sub_nonneg.mpr (hr1 a.1))
  case isFalse h => exact mul_nonneg (hq a.1) (hr0 a.1)

theorem splitMass_sum {N : Nat} (q r : Fin N -> Real) :
    Finset.sum Finset.univ (splitMass q r) = Finset.sum Finset.univ q := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [splitMass, Fin.reduceEq, ite_true, ite_false]
  ring

theorem splitLaw_isProbability {N : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hr0 : forall i, 0 <= r i) (hr1 : forall i, r i <= 1) :
    IsProbabilityMeasure (splitLaw q r) := by
  apply FiniteAtomicGeneric.labelMeasure_isProbability
  next => exact splitMass_nonneg q r hq hr0 hr1
  next => rw [splitMass_sum, hqsum]

theorem bit_binary {N : Nat} (a : Label N) : Or (bit a = 0) (bit a = 1) := by
  by_cases h : a.2 = 0
  case pos =>
    left
    simp [bit, h]
  case neg =>
    right
    simp [bit, Fin.eq_one_of_ne_zero a.2 h]

theorem split_bit_mean {N : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) :
    integral (splitLaw q r) bit =
      Finset.sum Finset.univ (fun i => q i * r i) := by
  unfold splitLaw
  rw [FiniteAtomicGeneric.label_integral _ (splitMass_nonneg q r hq hr0 hr1)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [splitMass, bit]

theorem split_projection_integral {N : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) (F : Fin N -> Real) :
    integral (splitLaw q r) (fun a => F a.1) =
      Finset.sum Finset.univ (fun i => q i * F i) := by
  unfold splitLaw
  rw [FiniteAtomicGeneric.label_integral _ (splitMass_nonneg q r hq hr0 hr1)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [splitMass, Fin.reduceEq, ite_true, ite_false]
  ring

theorem split_projection_law {N : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) :
    Measure.map (fun a : Label N => a.1) (splitLaw q r) = FiniteAtomic.labelMeasure q := by
  classical
  apply Measure.ext_of_measureReal_singleton
  intro i
  let F : Fin N -> Real := ({i} : Set (Fin N)).indicator (fun _ => 1)
  have hF : StronglyMeasurable F := (measurable_of_countable F).stronglyMeasurable
  calc
    _ = integral (Measure.map (fun a : Label N => a.1) (splitLaw q r)) F := by
      rw [integral_indicator_const 1 (measurableSet_singleton i)]
      simp only [smul_eq_mul, mul_one]
    _ = integral (splitLaw q r) (fun a => F a.1) :=
      integral_map_of_stronglyMeasurable (measurable_of_countable _) hF
    _ = Finset.sum Finset.univ (fun j => q j * F j) :=
      split_projection_integral q r hq hr0 hr1 F
    _ = q i := by simp [F, Pi.single_apply]
    _ = _ := (FiniteAtomic.labelMeasure_real_singleton q hq i).symm

theorem split_projection_iid_law {N n : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) :
    Measure.map (fun a : Fin n -> Label N => fun i => (a i).1)
      (Measure.pi (fun _ : Fin n => splitLaw q r)) =
      Measure.pi (fun _ : Fin n => FiniteAtomic.labelMeasure q) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  simp_rw [split_projection_law q r hq hr0 hr1]

theorem split_iid_projection_integral {N n : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hr0 : forall i, 0 <= r i)
    (hr1 : forall i, r i <= 1) (F : (Fin n -> Fin N) -> Real) :
    integral (Measure.pi (fun _ : Fin n => splitLaw q r))
      (fun a => F (fun i => (a i).1)) =
      integral (Measure.pi (fun _ : Fin n => FiniteAtomic.labelMeasure q)) F := by
  calc
    _ = integral (Measure.map (fun a : Fin n -> Label N => fun i => (a i).1)
        (Measure.pi (fun _ : Fin n => splitLaw q r))) F := by
      exact (integral_map_of_stronglyMeasurable (measurable_of_countable _)
        (measurable_of_countable F).stronglyMeasurable).symm
    _ = _ := by rw [split_projection_iid_law q r hq hr0 hr1]

theorem conditional_bernoulli_gate {N m : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hr0 : forall i, 0 <= r i) (hr1 : forall i, r i <= 1)
    (w : Fin N -> Geometry.Point m) :
    let p := Finset.sum Finset.univ (fun i => q i * r i)
    integral (Measure.pi (fun _ : Fin (m + 2) => splitLaw q r))
      (fun a => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (a j).1) i * bit (a i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => splitLaw q r))
          (fun a => Geometry.radonMass (fun j => w (a j).1)) := by
  have : IsProbabilityMeasure (splitLaw q r) := splitLaw_isProbability q r hq hqsum hr0 hr1
  have h := FiniteAtomicGeneric.finite_probability_binary_gate
    (splitLaw q r) bit (fun a => w a.1) bit_binary
  simpa only [split_bit_mean q r hq hr0 hr1] using h

theorem conditional_bernoulli_gate_projected {N m : Nat} (q r : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hr0 : forall i, 0 <= r i) (hr1 : forall i, r i <= 1)
    (w : Fin N -> Geometry.Point m) :
    let p := Finset.sum Finset.univ (fun i => q i * r i)
    integral (Measure.pi (fun _ : Fin (m + 2) => splitLaw q r))
      (fun a => |Finset.sum Finset.univ
        (fun i => Geometry.cofactor (fun j => w (a j).1) i * bit (a i))|) <=
      2 * p * (1 - p) *
        integral (Measure.pi (fun _ : Fin (m + 2) => FiniteAtomic.labelMeasure q))
          (fun a => Geometry.radonMass (fun j => w (a j))) := by
  have h := conditional_bernoulli_gate q r hq hqsum hr0 hr1 w
  rw [split_iid_projection_integral q r hq hr0 hr1
    (fun a : Fin (m + 2) -> Fin N => Geometry.radonMass (fun j => w (a j)))] at h
  exact h

end Hypercube.BinaryLift
