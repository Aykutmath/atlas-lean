import Section_10_Zonoid.Hypercube.Statements
import Mathlib.Tactic.NormNum

/-!
The source cube is the set of real points whose coordinates are zero or one.
The computational index type in Statements is `Fin d -> Bool`. This module
proves that the two domains are equivalent, including dimension zero, rather
than treating the change of vertex representation as an assumption.
-/

noncomputable section

namespace Hypercube.CubeRepresentation

def SourceCube (d : Nat) :=
  {z : Paper.Point d // forall j, Or (z j = 0) (z j = 1)}

theorem cubePoint_binary {d : Nat} (v : Paper.Cube d) (j : Fin d) :
    Or (Paper.cubePoint v j = 0) (Paper.cubePoint v j = 1) := by
  cases hv : v j
  next => exact Or.inl (by simp [Paper.cubePoint, hv])
  next => exact Or.inr (by simp [Paper.cubePoint, hv])

theorem cubePoint_injective {d : Nat} :
    Function.Injective (Paper.cubePoint : Paper.Cube d -> Paper.Point d) := by
  intro v w h
  funext j
  have hj := congrFun h j
  cases hv : v j <;> cases hw : w j
  all_goals first | rfl | (simp [Paper.cubePoint, hv, hw] at hj)

def boolCubeEquiv (d : Nat) : Equiv (Paper.Cube d) (SourceCube d) := by
  classical
  exact {
    toFun := fun v => Subtype.mk (Paper.cubePoint v) (cubePoint_binary v)
    invFun := fun z j => if z.val j = 1 then true else false
    left_inv := by
      intro v
      funext j
      cases hv : v j
      all_goals simp [Paper.cubePoint, hv]
    right_inv := by
      intro z
      apply Subtype.ext
      funext j
      rcases z.property j with hzero | hone
      next => simp [Paper.cubePoint, hzero]
      next => simp [Paper.cubePoint, hone]
  }

theorem boolCubeEquiv_point (d : Nat) (v : Paper.Cube d) :
    (boolCubeEquiv d v).val = Paper.cubePoint v := rfl

theorem range_cubePoint {d : Nat} :
    Set.range (Paper.cubePoint : Paper.Cube d -> Paper.Point d) =
      {z | forall j, Or (z j = 0) (z j = 1)} := by
  ext z
  constructor
  next =>
    intro hz
    cases hz with
    | intro v hval =>
        rw [<- hval]
        exact cubePoint_binary v
  next =>
    intro hz
    let p : SourceCube d := Subtype.mk z hz
    refine Exists.intro ((boolCubeEquiv d).symm p) ?_
    have h := congrArg Subtype.val ((boolCubeEquiv d).apply_symm_apply p)
    exact h

end Hypercube.CubeRepresentation
