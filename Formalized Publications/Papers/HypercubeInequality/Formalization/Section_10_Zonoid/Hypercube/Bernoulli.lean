import Section_10_Zonoid.Hypercube.Algebra.BinaryCocycle
import Section_10_Zonoid.Hypercube.Geometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
Source: hypercube_readable.tex, Section 5, equations eq:DL and eq:finite.
The actual point determinants and signed simplices are defined below.
The integration theorem exposes every geometric premise explicitly.
It is a checked implication, not a proof of the unclosed geometric premises.
-/

noncomputable section

namespace Hypercube.Bernoulli

open MeasureTheory
open Hypercube.BinaryCocycle

def finiteD {N : Nat} (q : Fin N -> Real)
    (a : Finset (Fin N) -> Real) (m : Nat) : Real :=
  Finset.sum ((Finset.univ : Finset (Fin N)).powersetCard (m + 1))
    (fun I => (Finset.prod I q) * |a I|)

def finiteL {N : Nat} (q f : Fin N -> Real)
    (a : Finset (Fin N) -> Real) (m : Nat) : Real :=
  Finset.sum ((Finset.univ : Finset (Fin N)).powersetCard (m + 2))
    (fun J => (Finset.prod J q) * |increasingAlternatingSum f a J|)

/-- The source a_I uses the increasing order on I; other degrees are zero. -/
def subsetAffineDet {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) : Real :=
  if hI : I.card = m + 1 then
    Geometry.affineDet (fun r => w (I.orderEmbOfFin hI r)) else 0

/-- The source h_I uses the same increasing order and the actual convex hull. -/
def subsetSignedSimplex {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) : Geometry.Point m -> Real :=
  if hI : I.card = m + 1 then
    Geometry.signedSimplex (fun r => w (I.orderEmbOfFin hI r)) else fun _ => 0

theorem subsetAffineDet_of_card {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) (hI : I.card = m + 1) :
    subsetAffineDet w I = Geometry.affineDet (fun r => w (I.orderEmbOfFin hI r)) := by
  simp [subsetAffineDet, hI]

theorem subsetSignedSimplex_of_card {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) (hI : I.card = m + 1) :
    subsetSignedSimplex w I =
      Geometry.signedSimplex (fun r => w (I.orderEmbOfFin hI r)) := by
  simp [subsetSignedSimplex, hI]

theorem subsetSignedSimplex_integrable {N m : Nat}
    (w : Fin N -> Geometry.Point m) (I : Finset (Fin N)) :
    Integrable (subsetSignedSimplex w I) volume := by
  unfold subsetSignedSimplex
  split_ifs
  next => exact Geometry.signedSimplex_integrable _
  next => exact integrable_zero (Geometry.Point m) Real volume

theorem subsetSignedSimplex_values {N m : Nat}
    (w : Fin N -> Geometry.Point m) (I : Finset (Fin N)) (x : Geometry.Point m) :
    Or (subsetSignedSimplex w I x = -1)
      (Or (subsetSignedSimplex w I x = 0) (subsetSignedSimplex w I x = 1)) := by
  unfold subsetSignedSimplex
  split_ifs
  next => exact Geometry.signedSimplex_values _ _
  next => simp

section Integration

variable {N m : Nat} {Space : Type*} [MeasurableSpace Space]

theorem increasing_sum_integrable (measure : Measure Space)
    (f : Fin N -> Real) (h : Finset (Fin N) -> Space -> Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) :
    Integrable (fun x => increasingAlternatingSum f (fun I => h I x) J) measure := by
  have heq : (fun x => increasingAlternatingSum f (fun I => h I x) J) =
      fun x => boundary f (fun I => h I x) J := by
    funext x
    rw [boundary_eq_alternatingSum, alternatingSum_eq_increasingAlternatingSum]
  rw [heq]
  unfold boundary
  apply integrable_finsetSum
  intro i hi
  have hcard : (J.erase i).card = m + 1 := by
    have he := Finset.card_erase_add_one hi
    omega
  exact (hints _ hcard).const_mul _

theorem increasing_sum_integral (measure : Measure Space)
    (f : Fin N -> Real) (h : Finset (Fin N) -> Space -> Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) :
    integral measure (fun x => increasingAlternatingSum f (fun I => h I x) J) =
      increasingAlternatingSum f (fun I => integral measure (h I)) J := by
  have heq : (fun x => increasingAlternatingSum f (fun I => h I x) J) =
      fun x => boundary f (fun I => h I x) J := by
    funext x
    rw [boundary_eq_alternatingSum, alternatingSum_eq_increasingAlternatingSum]
  rw [heq, <- alternatingSum_eq_increasingAlternatingSum,
    <- boundary_eq_alternatingSum]
  unfold boundary
  rw [integral_finsetSum]
  next =>
    simp only [integral_const_mul]
  next =>
    intro i hi
    have hcard : (J.erase i).card = m + 1 := by
      have he := Finset.card_erase_add_one hi
      omega
    exact (hints _ hcard).const_mul _

theorem increasing_sum_integral_representation (measure : Measure Space)
    (f : Fin N -> Real) (a : Finset (Fin N) -> Real)
    (h : Finset (Fin N) -> Space -> Real) (scale : Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (hrep : forall I, I.card = m + 1 -> a I = scale * integral measure (h I))
    (J : Finset (Fin N)) (hJ : J.card = m + 2) :
    increasingAlternatingSum f a J =
      scale * integral measure (fun x => increasingAlternatingSum f (fun I => h I x) J) := by
  rw [increasing_sum_integral measure f h hints J hJ]
  rw [<- alternatingSum_eq_increasingAlternatingSum,
    <- alternatingSum_eq_increasingAlternatingSum,
    <- boundary_eq_alternatingSum, <- boundary_eq_alternatingSum]
  unfold boundary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : (J.erase i).card = m + 1 := by
    have he := Finset.card_erase_add_one hi
    omega
  rw [hrep _ hcard]
  ring

theorem localD_integrable (measure : Measure Space)
    (q : Fin N -> Real) (h : Finset (Fin N) -> Space -> Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure) :
    Integrable (fun x => finiteD q (fun I => h I x) m) measure := by
  unfold finiteD
  apply integrable_finsetSum
  intro I hI
  exact ((hints I (Finset.mem_powersetCard.mp hI).2).abs).const_mul _

theorem localL_integrable (measure : Measure Space)
    (q f : Fin N -> Real) (h : Finset (Fin N) -> Space -> Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure) :
    Integrable (fun x => finiteL q f (fun I => h I x) m) measure := by
  unfold finiteL
  apply integrable_finsetSum
  intro J hJ
  exact ((increasing_sum_integrable measure f h hints J
    (Finset.mem_powersetCard.mp hJ).2).abs).const_mul _

theorem finiteD_integral_representation (measure : Measure Space)
    (q : Fin N -> Real) (a : Finset (Fin N) -> Real)
    (h : Finset (Fin N) -> Space -> Real) (scale : Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (habsrep : forall I, I.card = m + 1 ->
      |a I| = scale * integral measure (fun x => |h I x|)) :
    finiteD q a m = scale * integral measure (fun x => finiteD q (fun I => h I x) m) := by
  unfold finiteD
  rw [integral_finsetSum]
  next =>
    simp only [integral_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    rw [habsrep I (Finset.mem_powersetCard.mp hI).2]
    ring
  next =>
    intro I hI
    exact ((hints I (Finset.mem_powersetCard.mp hI).2).abs).const_mul _

/-- The sole spatial triangle inequality, with its direction explicit. -/
theorem finiteL_triangle_bound (measure : Measure Space)
    (q f : Fin N -> Real) (hq : forall i, 0 <= q i)
    (a : Finset (Fin N) -> Real) (h : Finset (Fin N) -> Space -> Real)
    (scale : Real) (hscale : 0 <= scale)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (hrep : forall I, I.card = m + 1 -> a I = scale * integral measure (h I)) :
    finiteL q f a m <=
      scale * integral measure (fun x => finiteL q f (fun I => h I x) m) := by
  unfold finiteL
  rw [integral_finsetSum]
  next =>
    simp only [integral_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro J hJ
    have hcard := (Finset.mem_powersetCard.mp hJ).2
    rw [increasing_sum_integral_representation measure f a h scale hints hrep J hcard,
      abs_mul, abs_of_nonneg hscale]
    have hw : 0 <= Finset.prod J q := Finset.prod_nonneg (fun i _ => hq i)
    have ht :
        |integral measure (fun x => increasingAlternatingSum f (fun I => h I x) J)| <=
        integral measure (fun x => |increasingAlternatingSum f (fun I => h I x) J|) :=
      abs_integral_le_integral_abs
    nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg hscale hw)]
  next =>
    intro J hJ
    exact ((increasing_sum_integrable measure f h hints J
      (Finset.mem_powersetCard.mp hJ).2).abs).const_mul _

/-- The paper's integration step. All not-yet-proved geometric premises are visible. -/
theorem finite_support_bound_of_signed_data (measure : Measure Space)
    (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (a : Finset (Fin N) -> Real) (h : Finset (Fin N) -> Space -> Real)
    (hints : forall I, I.card = m + 1 -> Integrable (h I) measure)
    (hrep : forall I, I.card = m + 1 ->
      a I = (m.factorial : Real) * integral measure (h I))
    (habsrep : forall I, I.card = m + 1 ->
      |a I| = (m.factorial : Real) * integral measure (fun x => |h I x|))
    (hunit : Filter.Eventually
      (fun x => forall I, I.card = m + 1 ->
        Or (h I x = -1) (Or (h I x = 0) (h I x = 1))) (ae measure))
    (hcycle : Filter.Eventually
      (fun x => forall J, J.card = m + 2 ->
        increasingAlternatingSum (fun _ => 1) (fun I => h I x) J = 0) (ae measure)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    finiteL q f a m <= p * (1 - p) * finiteD q a m := by
  dsimp only
  let p := Finset.sum Finset.univ (fun i => q i * f i)
  by_cases hN : m + 1 <= N
  next =>
    have hpoint : Filter.Eventually
        (fun x => finiteL q f (fun I => h I x) m <=
          p * (1 - p) * finiteD q (fun I => h I x) m) (ae measure) := by
      filter_upwards [hunit, hcycle] with x hxunit hxcycle
      have hc : forall J, J.card = (m + 1) + 1 ->
          increasingAlternatingSum (fun _ => 1) (fun I => h I x) J = 0 := by
        intro J hJ
        exact hxcycle J (by omega)
      have hb := weighted_binary_cocycle_increasing (by omega : 1 <= m + 1) hN
        q f hq hqsum hbinary (fun I => h I x) hxunit hc
      simpa [finiteL, finiteD, p, Nat.add_assoc] using hb
    have hleft := localL_integrable measure q f h hints
    have hright := (localD_integrable measure q h hints).const_mul (p * (1 - p))
    have hint := integral_mono_ae hleft hright hpoint
    have hscale : 0 <= (m.factorial : Real) := by
      exact_mod_cast Nat.zero_le m.factorial
    calc
      finiteL q f a m <= (m.factorial : Real) *
          integral measure (fun x => finiteL q f (fun I => h I x) m) :=
        finiteL_triangle_bound measure q f hq a h _ hscale hints hrep
      _ <= (m.factorial : Real) *
          integral measure (fun x => p * (1 - p) * finiteD q (fun I => h I x) m) :=
        mul_le_mul_of_nonneg_left hint hscale
      _ = p * (1 - p) * finiteD q a m := by
        rw [integral_const_mul, finiteD_integral_representation measure q a h _ hints habsrep]
        ring
  next =>
    have hemptyD : (Finset.univ : Finset (Fin N)).powersetCard (m + 1) = Finset.empty := by
      apply Finset.powersetCard_eq_empty.mpr
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hemptyL : (Finset.univ : Finset (Fin N)).powersetCard (m + 2) = Finset.empty := by
      apply Finset.powersetCard_eq_empty.mpr
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    simp [finiteL, finiteD, hemptyL, hemptyD, Finset.empty, Finset.sum_empty]

end Integration

/-- The actual determinant form, conditional only on its geometric cocycle and volume bridges. -/
theorem finite_support_geometric_bound_of_cocycle_and_volume {N m : Nat}
    (w : Fin N -> Geometry.Point m) (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (hrep : forall I, I.card = m + 1 ->
      subsetAffineDet w I = (m.factorial : Real) * integral volume (subsetSignedSimplex w I))
    (habsrep : forall I, I.card = m + 1 ->
      |subsetAffineDet w I| = (m.factorial : Real) *
        integral volume (fun x => |subsetSignedSimplex w I x|))
    (hcycle : Filter.Eventually
      (fun x => forall J, J.card = m + 2 ->
        increasingAlternatingSum (fun _ => 1) (fun I => subsetSignedSimplex w I x) J = 0)
      (ae volume)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    finiteL q f (subsetAffineDet w) m <= p * (1 - p) * finiteD q (subsetAffineDet w) m := by
  apply finite_support_bound_of_signed_data volume q f hq hqsum hbinary
    (subsetAffineDet w) (subsetSignedSimplex w)
  next =>
    intro I _
    exact subsetSignedSimplex_integrable w I
  next => exact hrep
  next => exact habsrep
  next =>
    exact Filter.Eventually.of_forall (fun x I _ => subsetSignedSimplex_values w I x)
  next => exact hcycle

end Hypercube.Bernoulli
