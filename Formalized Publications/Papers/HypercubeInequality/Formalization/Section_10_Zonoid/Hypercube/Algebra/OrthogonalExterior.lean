import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Real.Sqrt

/- The actual functorial action on Mathlib exterior powers preserves the
determinant-Gram form induced by any preserved base bilinear form. The norm
bridge below uses the canonical increasing exterior basis, with no factorial. -/

noncomputable section

namespace Hypercube.OrthogonalExterior

abbrev Degree (M : Type*) [AddCommGroup M] [Module Real M] (k : Nat) :=
  {x : ExteriorAlgebra Real M // Membership.mem (ExteriorAlgebra.exteriorPower Real k M) x}

def pullbackForm {M : Type*} [AddCommGroup M] [Module Real M]
    (B : LinearMap.BilinForm Real M) (U : Module.End Real M) :
    LinearMap.BilinForm Real M where
  toFun x := (B (U x)).comp U
  map_add' x y := by ext z; simp
  map_smul' r x := by ext z; simp

theorem induced_form_invariant {M : Type*} [AddCommGroup M] [Module Real M]
    (B : LinearMap.BilinForm Real M) (U : Module.End Real M)
    (hU : forall x y, B (U x) (U y) = B x y) (k : Nat)
    (x y : Degree M k) :
    B.exteriorPower k (exteriorPower.map k U x) (exteriorPower.map k U y) =
      B.exteriorPower k x y := by
  have heq : pullbackForm (B.exteriorPower k) (exteriorPower.map k U) =
      B.exteriorPower k := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp [pullbackForm, hU]
  exact congrArg (fun F : LinearMap.BilinForm Real (Degree M k) => F x y) heq

section Coordinates

variable {Index : Type*} [Fintype Index] [LinearOrder Index]

def dotForm : LinearMap.BilinForm Real (Index -> Real) :=
  Matrix.toBilin' (1 : Matrix Index Index Real)

def powerBasis (k : Nat) := (Pi.basisFun Real Index).exteriorPower k

def powerEnergy (k : Nat) (x : Degree (Index -> Real) k) : Real :=
  Finset.sum Finset.univ (fun s => ((powerBasis k).repr x s) ^ 2)

def powerNorm (k : Nat) (x : Degree (Index -> Real) k) : Real :=
  Real.sqrt (powerEnergy k x)

def fullBasis := (Pi.basisFun Real Index).ExteriorAlgebra

def fullNorm (x : ExteriorAlgebra Real (Index -> Real)) : Real :=
  Real.sqrt (Finset.sum Finset.univ (fun S => (fullBasis.repr x S) ^ 2))

theorem fullCoordinate_coe_basis (k : Nat) (s : Set.powersetCard Index k)
    (S : Finset Index) :
    fullBasis.repr (powerBasis k s).val S = if s.val = S then 1 else 0 := by
  classical
  have heq : (powerBasis k s).val = fullBasis s.val := by
    exact (ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun Real Index) s).symm
  rw [heq]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

theorem fullCoordinate_coe_expansion (k : Nat) (x : Degree (Index -> Real) k)
    (S : Finset Index) :
    fullBasis.repr x.val S = Finset.sum Finset.univ
      (fun s => (powerBasis k).repr x s * if s.val = S then 1 else 0) := by
  classical
  have hr := congrArg (fun y : Degree (Index -> Real) k => y.val) ((powerBasis k).sum_repr x)
  rw [<- hr]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, fullCoordinate_coe_basis]

theorem fullCoordinate_coe_of_card (k : Nat) (x : Degree (Index -> Real) k)
    (S : Finset Index) (hS : S.card = k) :
    fullBasis.repr x.val S = (powerBasis k).repr x (Set.powersetCard.ofCard hS) := by
  classical
  rw [fullCoordinate_coe_expansion]
  have hsum := Finset.sum_eq_single (Set.powersetCard.ofCard hS)
    (s := Finset.univ)
    (f := fun s : Set.powersetCard Index k =>
      (powerBasis k).repr x s * if s.val = S then 1 else 0)
    (by
      intro s _ hs
      have hv : Not (s.val = S) := by
        intro h
        exact hs (Subtype.ext h)
      simp only [ite_eq_right hv, mul_zero])
    (by simp)
  simpa using hsum

theorem fullCoordinate_coe_of_wrong_card (k : Nat) (x : Degree (Index -> Real) k)
    (S : Finset Index) (hS : Not (S.card = k)) : fullBasis.repr x.val S = 0 := by
  classical
  rw [fullCoordinate_coe_expansion]
  apply Finset.sum_eq_zero
  intro s _
  have hv : Not (s.val = S) := by
    intro h
    exact hS (h.symm.trans rfl |> congrArg Finset.card |>.trans s.prop)
  simp only [ite_eq_right hv, mul_zero]

theorem fullNorm_coe_power (k : Nat) (x : Degree (Index -> Real) k) :
    fullNorm x.val = powerNorm k x := by
  classical
  unfold fullNorm powerNorm
  apply congrArg Real.sqrt
  have hfilter : Finset.sum Finset.univ (fun S : Finset Index => (fullBasis.repr x.val S)^2) =
      Finset.sum (Finset.univ.filter (fun S : Finset Index => S.card = k))
        (fun S => (fullBasis.repr x.val S)^2) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hcard : Not (S.card = k) := by
      intro h
      exact hS (Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) h))
    rw [fullCoordinate_coe_of_wrong_card k x S hcard]
    norm_num
  rw [hfilter]
  unfold powerEnergy
  symm
  apply Finset.sum_bij (fun s _ => s.val)
  next =>
    intro s _
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) s.prop)
  next =>
    intro s _ t _ h
    exact Subtype.ext h
  next =>
    intro S hS
    exact Exists.intro (Set.powersetCard.ofCard (Finset.mem_filter.mp hS).2)
      (Exists.intro (Finset.mem_univ _) rfl)
  next =>
    intro s _
    rw [fullCoordinate_coe_of_card k x s.val s.prop]
    rfl

theorem dotForm_apply (x y : Index -> Real) :
    dotForm x y = Finset.sum Finset.univ (fun i => x i * y i) := by
  rw [dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec]
  rfl

theorem dotForm_basis_dual (i : Index) :
    dotForm ((Pi.basisFun Real Index) i) = (Pi.basisFun Real Index).dualBasis i := by
  apply LinearMap.ext
  intro x
  rw [dotForm_apply]
  simp [Pi.basisFun_apply, Pi.single_apply]

theorem dotForm_exterior_basis (k : Nat) (s t : Set.powersetCard Index k) :
    dotForm.exteriorPower k (powerBasis k s) (powerBasis k t) = if s = t then 1 else 0 := by
  classical
  have hsingle : (fun i : Index => dotForm (Pi.single i 1)) =
      (Pi.basisFun Real Index).coord := by
    funext i
    apply LinearMap.ext
    intro x
    have h := congrArg (fun F : Module.Dual Real (Index -> Real) => F x) (dotForm_basis_dual i)
    simpa only [Pi.basisFun_apply, Module.Basis.dualBasis_apply, Module.Basis.coord_apply] using h
  have hmap : exteriorPower.map k dotForm (powerBasis k s) =
      ((Pi.basisFun Real Index).dualBasis.exteriorPower k) s := by
    simp only [powerBasis, exteriorPower.basis_apply]
    simp [Function.comp_def, hsingle]
  unfold LinearMap.BilinForm.exteriorPower
  rw [LinearMap.comp_apply, hmap,
    exteriorPower.pairingDual_apply_dualBasis_exteriorPower]
  change ((Pi.basisFun Real Index).exteriorPower k).dualBasis s
    (((Pi.basisFun Real Index).exteriorPower k) t) = _
  simp only [Module.Basis.dualBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply, eq_comm]

theorem exterior_energy_eq_induced_form (k : Nat) (x : Degree (Index -> Real) k) :
    powerEnergy k x = dotForm.exteriorPower k x x := by
  classical
  have hmatrix : LinearMap.BilinForm.toMatrix (powerBasis (Index := Index) k)
      ((dotForm (Index := Index)).exteriorPower k) =
      (1 : Matrix (Set.powersetCard Index k) (Set.powersetCard Index k) Real) := by
    funext s t
    rw [LinearMap.BilinForm.toMatrix_apply, dotForm_exterior_basis, Matrix.one_apply]
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec (powerBasis k),
    hmatrix, Matrix.one_mulVec]
  simp only [powerEnergy, dotProduct, pow_two]

theorem orthogonal_induced_exterior_norm (U : Module.End Real (Index -> Real))
    (hU : forall x y, Finset.sum Finset.univ (fun i => U x i * U y i) =
      Finset.sum Finset.univ (fun i => x i * y i))
    (k : Nat) (x : Degree (Index -> Real) k) :
    powerNorm k (exteriorPower.map k U x) = powerNorm k x := by
  unfold powerNorm
  rw [exterior_energy_eq_induced_form, exterior_energy_eq_induced_form]
  rw [induced_form_invariant dotForm U (fun x y => by
    simpa only [dotForm_apply] using hU x y)]

theorem orthogonal_full_exterior_norm_of_degree (U : Module.End Real (Index -> Real))
    (hU : forall x y, Finset.sum Finset.univ (fun i => U x i * U y i) =
      Finset.sum Finset.univ (fun i => x i * y i))
    (k : Nat) (x : Degree (Index -> Real) k) :
    fullNorm (ExteriorAlgebra.map U x.val) = fullNorm x.val := by
  rw [<- exteriorPower.coe_map U x, fullNorm_coe_power, fullNorm_coe_power]
  exact orthogonal_induced_exterior_norm U hU k x

end Coordinates

end Hypercube.OrthogonalExterior
