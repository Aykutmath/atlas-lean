/-
Kernel-checked real finite-dimensional quotient duality with primal/dual attainment.

Paper: Lemma "Finite-dimensional quotient duality", source lines 3119-3138.
The scalar field is explicitly Real, as in the ellipsoid application.
The proof uses a norm-minimizing point of a closed affine fiber and a
Hahn-Banach norming functional on the genuine quotient seminormed space.
No desired duality conclusion is assumed as an input.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

section QuotientDuality

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace Real X]
variable [NormedAddCommGroup Y] [NormedSpace Real Y]

/-- The real values over which the primal fiber infimum is taken. -/
def fiberNormValues (T : ContinuousLinearMap (RingHom.id Real) X Y) (e : Y) :
    Set Real :=
  {r | exists x : X, T x = e /\ norm x = r}

/-- The dual support values. Composition with T is the transpose action on
continuous linear functionals, so its operator norm is the paper's dual norm. -/
def dualFiberValues (T : ContinuousLinearMap (RingHom.id Real) X Y) (e : Y) :
    Set Real :=
  {r | exists phi : StrongDual Real Y,
    norm (phi.comp T) <= 1 /\ abs (phi e) = r}

/-- A primal norm is nonnegative; this gives the boundedness needed by sInf. -/
theorem fiberNormValues_bddBelow
    (T : ContinuousLinearMap (RingHom.id Real) X Y) (e : Y) :
    BddBelow (fiberNormValues T e) := by
  refine Exists.intro 0 ?_
  rintro r hr
  let x : X := hr.choose
  have hnorm : norm x = r := hr.choose_spec.2
  rw [<- hnorm]
  exact norm_nonneg x

/-- Surjectivity makes every affine fiber nonempty. -/
theorem fiberNormValues_nonempty
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    (fiberNormValues T e).Nonempty := by
  let x : X := (hT e).choose
  have hx : T x = e := (hT e).choose_spec
  exact Exists.intro (norm x) (Exists.intro x (And.intro hx rfl))

/-- The zero dual functional is admissible, including in zero dimension. -/
theorem dualFiberValues_nonempty
    (T : ContinuousLinearMap (RingHom.id Real) X Y) (e : Y) :
    (dualFiberValues T e).Nonempty := by
  refine Exists.intro 0 (Exists.intro (0 : StrongDual Real Y) ?_)
  simp

/-- Weak duality for each actual vector in the affine fiber. This statement
does not need finite dimension or surjectivity. -/
theorem abs_dual_apply_le_fiber_norm
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (phi : StrongDual Real Y) (hphi : norm (phi.comp T) <= 1)
    {e : Y} {x : X} (hx : T x = e) :
    abs (phi e) <= norm x := by
  have hbound := (phi.comp T).le_opNorm x
  have hscalar : norm (phi.comp T) * norm x <= norm x := by
    calc
      norm (phi.comp T) * norm x <= 1 * norm x :=
        mul_le_mul_of_nonneg_right hphi (norm_nonneg x)
      _ = norm x := one_mul _
  have heval : norm ((phi.comp T) x) = abs (phi e) := by
    simp only [ContinuousLinearMap.comp_apply, hx, Real.norm_eq_abs]
  rw [heval] at hbound
  exact hbound.trans hscalar

/-- The admissible dual values are bounded above by any feasible primal norm. -/
theorem dualFiberValues_bddAbove
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    BddAbove (dualFiberValues T e) := by
  let x : X := (hT e).choose
  have hx : T x = e := (hT e).choose_spec
  refine Exists.intro (norm x) ?_
  rintro r hr
  let phi : StrongDual Real Y := hr.choose
  have hphi : norm (phi.comp T) <= 1 := hr.choose_spec.1
  have hvalue : abs (phi e) = r := hr.choose_spec.2
  rw [<- hvalue]
  exact abs_dual_apply_le_fiber_norm T phi hphi hx

/-- Weak duality in infimum form, without a finite-dimensional hypothesis. -/
theorem abs_dual_apply_le_fiber_infimum
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y)
    (phi : StrongDual Real Y) (hphi : norm (phi.comp T) <= 1) :
    abs (phi e) <= sInf (fiberNormValues T e) := by
  apply le_csInf (fiberNormValues_nonempty T hT e)
  rintro r hr
  let x : X := hr.choose
  have hx : T x = e := hr.choose_spec.1
  have hnorm : norm x = r := hr.choose_spec.2
  rw [<- hnorm]
  exact abs_dual_apply_le_fiber_norm T phi hphi hx

/-- In a proper source space, a nonempty affine fiber of a continuous linear
map contains a vector of minimum norm. The proof uses nearest-point attainment
for a nonempty closed set, rather than assuming a quotient norm minimizer. -/
theorem exists_fiber_norm_minimizer [ProperSpace X]
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    exists x : X, T x = e /\
      forall z : X, T z = e -> norm x <= norm z := by
  let F : Set X := {x | T x = e}
  have hclosed : IsClosed F := isClosed_eq T.continuous continuous_const
  have hnonempty : F.Nonempty := by
    exact hT e
  have hattain := hclosed.exists_infDist_eq_dist hnonempty (0 : X)
  let x : X := hattain.choose
  have hx : T x = e := hattain.choose_spec.1
  have hdist : Metric.infDist (0 : X) F = dist (0 : X) x := hattain.choose_spec.2
  refine Exists.intro x (And.intro hx ?_)
  intro z hz
  have hle : Metric.infDist (0 : X) F <= dist (0 : X) z :=
    Metric.infDist_le_dist_of_mem (s := F) hz
  rw [hdist] at hle
  simpa only [dist_zero_left] using hle

/-- The norm of the quotient class of an actual fiber minimizer equals its
ambient norm. The reverse inequality uses arbitrarily accurate quotient
representatives, not a pre-assumed norm-attaining quotient section. -/
theorem quotient_norm_eq_minimizer
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) (x : X)
    (hx : T x = e) (hmin : forall z : X, T z = e -> norm x <= norm z) :
    norm (Submodule.Quotient.mk x :
      HasQuotient.Quotient X T.toLinearMap.ker) = norm x := by
  let E := T.toLinearMap.quotKerEquivOfSurjective hT
  let q : HasQuotient.Quotient X T.toLinearMap.ker := Submodule.Quotient.mk x
  refine le_antisymm ?lower ?upper
  case lower =>
    exact Submodule.Quotient.norm_mk_le T.toLinearMap.ker x
  case upper =>
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have hrep := Submodule.Quotient.norm_mk_lt q hepsilon
    let z : X := hrep.choose
    have hz : Submodule.Quotient.mk z = q := hrep.choose_spec.1
    have hznorm : norm z < norm q + epsilon := hrep.choose_spec.2
    have hze := congrArg E hz
    change T z = T x at hze
    have hzfiber : T z = e := hze.trans hx
    exact (hmin z hzfiber).trans hznorm.le

/-- The norm of a functional on the quotient equals the norm of its
pullback to X. The bridge hypothesis is the pointwise representation identity;
no norm identity or duality inequality is assumed. -/
theorem norm_pullback_eq_quotient_dual
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (g : StrongDual Real (HasQuotient.Quotient X T.toLinearMap.ker))
    (phi : StrongDual Real Y)
    (hbridge : forall z : X,
      phi (T z) = g (Submodule.Quotient.mk z)) :
    norm (phi.comp T) = norm g := by
  refine le_antisymm ?pullback ?quotient
  case pullback =>
    apply (phi.comp T).opNorm_le_bound (norm_nonneg g)
    intro z
    calc
      norm ((phi.comp T) z) = norm (g (Submodule.Quotient.mk z)) := by
        rw [ContinuousLinearMap.comp_apply, hbridge]
      _ <= norm g * norm (Submodule.Quotient.mk z :
          HasQuotient.Quotient X T.toLinearMap.ker) := g.le_opNorm _
      _ <= norm g * norm z := mul_le_mul_of_nonneg_left
        (Submodule.Quotient.norm_mk_le T.toLinearMap.ker z) (norm_nonneg g)
  case quotient =>
    apply g.opNorm_le_bound (norm_nonneg (phi.comp T))
    intro q
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let C : Real := norm (phi.comp T)
    have hC : 0 <= C := norm_nonneg _
    have hCplus : 0 < C + 1 := by linarith
    let eta : Real := epsilon / (C + 1)
    have heta : 0 < eta := div_pos hepsilon hCplus
    have heta_eq : eta * (C + 1) = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hCplus]
    have hsmall : C * eta <= epsilon := by nlinarith
    have hrep := Submodule.Quotient.norm_mk_lt q heta
    let z : X := hrep.choose
    have hz : Submodule.Quotient.mk z = q := hrep.choose_spec.1
    have hznorm : norm z < norm q + eta := hrep.choose_spec.2
    have hvalue : g q = (phi.comp T) z := by
      calc
        g q = g (Submodule.Quotient.mk z) := congrArg g hz.symm
        _ = phi (T z) := (hbridge z).symm
        _ = (phi.comp T) z := rfl
    calc
      norm (g q) = norm ((phi.comp T) z) := congrArg norm hvalue
      _ <= C * norm z := (phi.comp T).le_opNorm z
      _ <= C * (norm q + eta) := mul_le_mul_of_nonneg_left hznorm.le hC
      _ = C * norm q + C * eta := mul_add C (norm q) eta
      _ <= C * norm q + epsilon := add_le_add_right hsmall _

/-- A norming functional on the quotient yields an admissible dual functional
on Y attaining the minimum fiber norm. Finite dimension is used for primal
attainment and for automatic continuity of the transported linear functional. -/
theorem exists_fiber_norming_dual
    [FiniteDimensional Real X] [FiniteDimensional Real Y]
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    exists x : X, exists phi : StrongDual Real Y,
      T x = e /\
      (forall z : X, T z = e -> norm x <= norm z) /\
      norm (phi.comp T) <= 1 /\ phi e = norm x := by
  have hprimal := exists_fiber_norm_minimizer T hT e
  let x : X := hprimal.choose
  have hx : T x = e := hprimal.choose_spec.1
  have hmin : forall z : X, T z = e -> norm x <= norm z := hprimal.choose_spec.2
  let Q := HasQuotient.Quotient X T.toLinearMap.ker
  let E := T.toLinearMap.quotKerEquivOfSurjective hT
  let q : Q := Submodule.Quotient.mk x
  have hq : norm q = norm x := quotient_norm_eq_minimizer T hT e x hx hmin
  have hdual := exists_dual_vector'' Real q
  let g : StrongDual Real Q := hdual.choose
  have hgnorm : norm g <= 1 := hdual.choose_spec.1
  have hgvalue : g q = norm q := hdual.choose_spec.2
  let phiL : LinearMap (RingHom.id Real) Y Real :=
    g.toLinearMap.comp E.symm.toLinearMap
  let phi : StrongDual Real Y := phiL.toContinuousLinearMap
  have hphi_apply (z : X) :
      phi (T z) = g (Submodule.Quotient.mk z : Q) := by
    change g (E.symm (T z)) = g (Submodule.Quotient.mk z : Q)
    have hquot : E.symm (T z) = (Submodule.Quotient.mk z : Q) :=
      LinearMap.quotKerEquivOfSurjective_symm_apply T.toLinearMap hT z
    rw [hquot]
  have hnorm_exact : norm (phi.comp T) = norm g :=
    norm_pullback_eq_quotient_dual T g phi hphi_apply
  have hbound : norm (phi.comp T) <= 1 := hnorm_exact.le.trans hgnorm
  have hvalue : phi e = norm x := by
    rw [<- hx, hphi_apply]
    exact hgvalue.trans hq
  exact Exists.intro x (Exists.intro phi
    (And.intro hx (And.intro hmin (And.intro hbound hvalue))))

/-- Both extrema in finite-dimensional real quotient duality are attained.
This is stronger than the paper's separate assertion of primal attainment. -/
theorem finite_dimensional_quotient_duality_extrema
    [FiniteDimensional Real X] [FiniteDimensional Real Y]
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    exists r : Real,
      IsLeast (fiberNormValues T e) r /\ IsGreatest (dualFiberValues T e) r := by
  have hcertificate := exists_fiber_norming_dual T hT e
  let x : X := hcertificate.choose
  let phi : StrongDual Real Y := hcertificate.choose_spec.choose
  have hx : T x = e := hcertificate.choose_spec.choose_spec.1
  have hmin : forall z : X, T z = e -> norm x <= norm z :=
    hcertificate.choose_spec.choose_spec.2.1
  have hbound : norm (phi.comp T) <= 1 := hcertificate.choose_spec.choose_spec.2.2.1
  have hvalue : phi e = norm x := hcertificate.choose_spec.choose_spec.2.2.2
  refine Exists.intro (norm x) (And.intro ?primal ?dual)
  case primal =>
    refine And.intro (Exists.intro x (And.intro hx rfl)) ?_
    rintro r hr
    let z : X := hr.choose
    have hz : T z = e := hr.choose_spec.1
    have hnorm : norm z = r := hr.choose_spec.2
    rw [<- hnorm]
    exact hmin z hz
  case dual =>
    have habs : abs (phi e) = norm x := by
      rw [hvalue, abs_of_nonneg (norm_nonneg x)]
    refine And.intro (Exists.intro phi (And.intro hbound habs)) ?_
    rintro r hr
    let psi : StrongDual Real Y := hr.choose
    have hpsi : norm (psi.comp T) <= 1 := hr.choose_spec.1
    have hnorm : abs (psi e) = r := hr.choose_spec.2
    rw [<- hnorm]
    exact abs_dual_apply_le_fiber_norm T psi hpsi hx

/-- The paper's finite-dimensional quotient duality equality, with the primal
minimum attained. The two sets explicitly encode all constraints on both sides. -/
theorem finite_dimensional_quotient_duality
    [FiniteDimensional Real X] [FiniteDimensional Real Y]
    (T : ContinuousLinearMap (RingHom.id Real) X Y)
    (hT : Function.Surjective T) (e : Y) :
    sInf (fiberNormValues T e) = sSup (dualFiberValues T e) /\
      exists x : X, T x = e /\ norm x = sInf (fiberNormValues T e) := by
  have hextrema := finite_dimensional_quotient_duality_extrema T hT e
  let r : Real := hextrema.choose
  have hleast : IsLeast (fiberNormValues T e) r := hextrema.choose_spec.1
  have hgreatest : IsGreatest (dualFiberValues T e) r := hextrema.choose_spec.2
  have hinf : sInf (fiberNormValues T e) = r := hleast.csInf_eq
  have hsup : sSup (dualFiberValues T e) = r := hgreatest.csSup_eq
  refine And.intro (hinf.trans hsup.symm) ?_
  let x : X := hleast.1.choose
  have hx : T x = e := hleast.1.choose_spec.1
  have hnorm : norm x = r := hleast.1.choose_spec.2
  exact Exists.intro x (And.intro hx (hnorm.trans hinf.symm))

/-- Literal linear-map version of the real finite-dimensional paper lemma.
Automatic continuity is supplied by mathlib, so continuity is not an additional
hypothesis. Composition with the dual functional is the pullback T-star. -/
theorem finite_dimensional_quotient_duality_linear
    [FiniteDimensional Real X] [FiniteDimensional Real Y]
    (T : LinearMap (RingHom.id Real) X Y) (hT : Function.Surjective T) (e : Y) :
    sInf {r : Real | exists x : X, T x = e /\ norm x = r} =
      sSup {r : Real | exists phi : StrongDual Real Y,
        norm (phi.comp T.toContinuousLinearMap) <= 1 /\ abs (phi e) = r} /\
      exists x : X, T x = e /\
        norm x = sInf {r : Real | exists z : X, T z = e /\ norm z = r} := by
  exact finite_dimensional_quotient_duality T.toContinuousLinearMap hT e

end QuotientDuality

end GaussianEllipsoid
