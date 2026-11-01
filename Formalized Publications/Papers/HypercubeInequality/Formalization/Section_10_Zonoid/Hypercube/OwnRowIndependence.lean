import Section_10_Zonoid.Hypercube.EndpointAssembly
import Section_10_Zonoid.Hypercube.FiniteProjectedHeight

/- Source preliminary factor-two loss. The omitted rows and the own sample
are explicitly transported to a product law before taking expectations. -/

noncomputable section

namespace Hypercube.OwnRowIndependence

open MeasureTheory

theorem iid_own_row_factorization {Space : Type*} [MeasurableSpace Space]
    (nu : Measure Space) [IsProbabilityMeasure nu] (n : Nat) (i : Fin (n + 1))
    (F : (Fin n -> Space) -> Real) (G : Space -> Real) :
    integral (Measure.pi (fun _ : Fin (n + 1) => nu))
      (fun z => F (fun j => z (i.succAbove j)) * G (z i)) =
      integral (Measure.pi (fun _ : Fin n => nu)) F * integral nu G := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => nu) i).integral_comp'
    (fun z : Prod Space (Fin n -> Space) => G z.1 * F z.2)
  calc
    integral (Measure.pi (fun _ : Fin (n + 1) => nu))
      (fun z => F (fun j => z (i.succAbove j)) * G (z i)) =
      integral (nu.prod (Measure.pi (fun _ : Fin n => nu)))
        (fun z => G z.1 * F z.2) := by
          convert h using 1
          congr 1
          funext z
          exact mul_comm _ _
    _ = integral nu G * integral (Measure.pi (fun _ : Fin n => nu)) F := integral_prod_mul G F
    _ = _ := mul_comm _ _

theorem binary_integrable {Space : Type*} [MeasurableSpace Space]
    (P : Measure Space) [IsProbabilityMeasure P] (X : Space -> Real) (hX : Measurable X)
    (hbinary : Filter.Eventually (fun z => Or (X z = 0) (X z = 1)) (ae P)) :
    Integrable X P := by
  apply (integrable_const (1 : Real)).mono' hX.aestronglyMeasurable
  exact hbinary.mono (fun z hz => by rcases hz with hz | hz <;> simp [hz])

theorem binary_mean_bounds {Space : Type*} [MeasurableSpace Space]
    (P : Measure Space) [IsProbabilityMeasure P] (X : Space -> Real) (hX : Measurable X)
    (hbinary : Filter.Eventually (fun z => Or (X z = 0) (X z = 1)) (ae P)) :
    And (0 <= integral P X) (integral P X <= 1) := by
  have hint := binary_integrable P X hX hbinary
  constructor
  next =>
    apply integral_nonneg_of_ae
    exact hbinary.mono (fun z hz => by rcases hz with hz | hz <;> simp [hz])
  next =>
    have hle : Filter.Eventually (fun z => X z <= (1 : Real)) (ae P) :=
      hbinary.mono (fun z hz => by rcases hz with hz | hz <;> simp [hz])
    simpa using integral_mono_ae hint (integrable_const (1 : Real)) hle

theorem binary_mean_eq_success_probability {Space : Type*} [MeasurableSpace Space]
    (P : Measure Space) [IsProbabilityMeasure P] (X : Space -> Real) (hX : Measurable X)
    (hbinary : Filter.Eventually (fun z => Or (X z = 0) (X z = 1)) (ae P)) :
    integral P X = P.real {z | X z = 1} := by
  classical
  have heq : Filter.Eventually
      (fun z => X z = ({z | X z = 1} : Set Space).indicator (fun _ => (1 : Real)) z) (ae P) := by
    exact hbinary.mono (fun z hz => by rcases hz with hz | hz <;> simp [hz, Set.indicator])
  rw [integral_congr_ae heq, integral_indicator_const _ (measurableSet_eq_fun hX measurable_const)]
  simp

theorem binary_centered_abs_mean {Space : Type*} [MeasurableSpace Space]
    (P : Measure Space) [IsProbabilityMeasure P] (X : Space -> Real) (hX : Measurable X)
    (hbinary : Filter.Eventually (fun z => Or (X z = 0) (X z = 1)) (ae P)) :
    integral P (fun z => |X z - integral P X|) =
      2 * integral P X * (1 - integral P X) := by
  let p := integral P X
  have hp := binary_mean_bounds P X hX hbinary
  have hp0 : 0 <= p := hp.1
  have heq : Filter.Eventually (fun z => |X z - p| = p + (1 - 2 * p) * X z) (ae P) := by
    apply hbinary.mono
    intro z hz
    rcases hz with hz | hz
    next => simp [hz, abs_of_nonneg hp0]
    next => rw [hz, abs_of_nonneg (sub_nonneg.mpr hp.2)]; ring
  rw [integral_congr_ae heq,
    integral_add (integrable_const p) ((binary_integrable P X hX hbinary).const_mul (1 - 2 * p)),
    integral_const, integral_const_mul, probReal_univ]
  change 1 * p + (1 - 2 * p) * p = 2 * p * (1 - p)
  ring

/-- Exact own-row expectation factorization, even when each height depends on its own projection. -/
theorem cofactor_own_height_factorization {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (i : Fin (m + 2)) (G : Paper.Point (m + 1) -> Real) :
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * G (z i)) =
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|) * integral nu G := by
  let F := fun z : Fin (m + 1) -> Paper.Point (m + 1) =>
    |Geometry.affineDet (fun j => Paper.projectLast (z j))|
  have hmain := iid_own_row_factorization nu (m + 1) i F G
  have hone := iid_own_row_factorization nu (m + 1) i F (fun _ => 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hone
  simp only [Moments.cofactor_abs]
  exact hmain.trans (congrArg (fun a => a * integral nu G) hone.symm)

theorem centered_cofactor_height_integrable {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (i : Fin (m + 2)) (p : Real) :
    Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m) - p|)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
  have hc := (Moments.sampled_cofactor_continuous i).measurable
  have ht := (Moments.sampled_height_continuous i).measurable
  have hci : Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      Geometry.cofactor (fun j => Paper.projectLast (z j)) i)
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
    apply (integrable_norm_iff hc.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using Moments.sampled_cofactor_abs_integrable nu hfirst i
  have hcit : Integrable (fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
      Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m))
      (Measure.pi (fun _ : Fin (m + 2) => nu)) := by
    apply (integrable_norm_iff (hc.mul ht).aestronglyMeasurable).mp
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
      Moments.cofactor_height_product_integrable nu hfirst i
  have h := (hcit.sub (hci.mul_const p)).abs
  convert h using 1
  funext z
  rw [<- abs_mul]
  congr 1
  simp only [Pi.sub_apply]
  ring

/-- The source direct-triangle estimate loses exactly a factor of two. -/
theorem crude_binary_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu)
    (hbinary : Filter.Eventually
      (fun z => Or (z (Fin.last m) = 0) (z (Fin.last m) = 1)) (ae nu)) :
    let p := integral nu (fun z => z (Fin.last m))
    EndpointAssembly.sampledHeightObjective nu <=
      4 * p * (1 - p) * EndpointAssembly.expectedRadonMass nu := by
  let p := integral nu (fun z => z (Fin.last m))
  let P := Measure.pi (fun _ : Fin (m + 2) => nu)
  let term := fun i : Fin (m + 2) => fun z : Fin (m + 2) -> Paper.Point (m + 1) =>
    |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| * |z i (Fin.last m) - p|
  have hterm (i : Fin (m + 2)) : Integrable (term i) P :=
    centered_cofactor_height_integrable nu hfirst i p
  have hpoint (z : Fin (m + 2) -> Paper.Point (m + 1)) :
      |Finset.sum Finset.univ (fun i => Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
        z i (Fin.last m))| <= Finset.sum Finset.univ (fun i => term i z) := by
    have hcenter : Finset.sum Finset.univ (fun i =>
        Geometry.cofactor (fun j => Paper.projectLast (z j)) i * (z i (Fin.last m) - p)) =
        Finset.sum Finset.univ (fun i =>
          Geometry.cofactor (fun j => Paper.projectLast (z j)) i * z i (Fin.last m)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, <- Finset.sum_mul,
        Geometry.cofactor_sum_zero, zero_mul, sub_zero]
    rw [<- hcenter]
    simpa only [term, abs_mul] using Finset.abs_sum_le_sum_abs
      (fun i : Fin (m + 2) => Geometry.cofactor (fun j => Paper.projectLast (z j)) i *
        (z i (Fin.last m) - p)) Finset.univ
  have hmean : integral nu (fun z => |z (Fin.last m) - p|) = 2 * p * (1 - p) :=
    binary_centered_abs_mean nu (fun z => z (Fin.last m)) (measurable_pi_apply _) hbinary
  have hfactor (i : Fin (m + 2)) : integral P (term i) =
      integral P (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|) *
        (2 * p * (1 - p)) := by
    have hh := cofactor_own_height_factorization nu i (fun z => |z (Fin.last m) - p|)
    rw [hmean] at hh
    exact hh
  have hmass : Finset.sum Finset.univ (fun i : Fin (m + 2) =>
      integral P (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|)) =
      2 * EndpointAssembly.expectedRadonMass nu := by
    unfold EndpointAssembly.expectedRadonMass Geometry.radonMass
    rw [integral_const_mul, integral_finsetSum Finset.univ
      (fun i _ => Moments.sampled_cofactor_abs_integrable nu hfirst i)]
    change _ = 2 * ((1 / 2 : Real) * _)
    ring
  calc
    EndpointAssembly.sampledHeightObjective nu <= integral P (fun z =>
      Finset.sum Finset.univ (fun i => term i z)) :=
        integral_mono (Moments.sampled_determinant_integrable nu hfirst)
          (integrable_finsetSum Finset.univ (fun i _ => hterm i)) hpoint
    _ = Finset.sum Finset.univ (fun i => integral P (term i)) :=
      integral_finsetSum Finset.univ (fun i _ => hterm i)
    _ = Finset.sum Finset.univ (fun i : Fin (m + 2) => integral P
        (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|)) *
          (2 * p * (1 - p)) := by simp_rw [hfactor]; rw [Finset.sum_mul]
    _ = 4 * p * (1 - p) * EndpointAssembly.expectedRadonMass nu := by rw [hmass]; ring

theorem cofactor_own_centered_height_mean {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (i : Fin (m + 2))
    (hbinary : Filter.Eventually
      (fun z => Or (z (Fin.last m) = 0) (z (Fin.last m) = 1)) (ae nu)) :
    let p := nu.real {z | z (Fin.last m) = 1}
    integral (Measure.pi (fun _ : Fin (m + 2) => nu))
      (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i| *
        |z i (Fin.last m) - p|) =
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => |Geometry.cofactor (fun j => Paper.projectLast (z j)) i|) *
          (2 * p * (1 - p)) := by
  have hp := binary_mean_eq_success_probability nu (fun z => z (Fin.last m))
    (measurable_pi_apply _) hbinary
  have hm := binary_centered_abs_mean nu (fun z => z (Fin.last m))
    (measurable_pi_apply _) hbinary
  rw [hp] at hm
  have hh := cofactor_own_height_factorization nu i
    (fun z => |z (Fin.last m) - nu.real {z | z (Fin.last m) = 1}|)
  rw [hm] at hh
  exact hh

/-- Literal preliminary estimate for a finite projected law and binary heights. -/
theorem finite_projected_crude_binary_gate {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (s : Set (Paper.Point m)) (hfinite : Set.Finite s)
    (hsupport : (nu.map Paper.projectLast) s = 1)
    (hbinary : Filter.Eventually
      (fun z => Or (z (Fin.last m) = 0) (z (Fin.last m) = 1)) (ae nu)) :
    let p := nu.real {z | z (Fin.last m) = 1}
    EndpointAssembly.sampledHeightObjective nu <=
      4 * p * (1 - p) * EndpointAssembly.expectedRadonMass nu := by
  have hheight := binary_integrable nu (fun z => z (Fin.last m)) (measurable_pi_apply _) hbinary
  have hfirst := FiniteProjectedHeight.firstMoments_of_finite_projected_law
    nu s hfinite hsupport hheight
  have h := crude_binary_gate nu hfirst hbinary
  simpa only [binary_mean_eq_success_probability nu (fun z => z (Fin.last m))
    (measurable_pi_apply _) hbinary] using h

end Hypercube.OwnRowIndependence
