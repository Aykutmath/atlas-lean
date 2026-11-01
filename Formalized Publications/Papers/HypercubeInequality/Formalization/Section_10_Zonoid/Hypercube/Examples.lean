import Section_10_Zonoid.Hypercube.CubeEndpoint
import Mathlib.Tactic.NormNum

/- Exact source example: the uniform probability law on the four unit-square vertices.
The finite calculations below use kernel-checked rewrites and rational arithmetic. -/

noncomputable section

namespace Hypercube.Examples

open MeasureTheory

private theorem sum_fin_function_succ {Index : Type*} [Fintype Index] (n : Nat)
    (F : (Fin (n + 1) -> Index) -> Real) :
    Finset.sum Finset.univ F = Finset.sum Finset.univ (fun a =>
      Finset.sum Finset.univ (fun f : Fin n -> Index => F (Fin.cons a f))) := by
  rw [<- (Fin.consEquiv (fun _ : Fin (n + 1) => Index)).sum_comp F,
    Fintype.sum_prod_type]
  rfl

def uniformSquareLaw : Measure (Paper.Point 2) :=
  CubeEndpoint.cubeLaw (fun _ : Paper.Cube 2 => (1 / 4 : Real))

private theorem cons_two {Index : Type*} (a : Index) (f : Fin 2 -> Index) :
    (Fin.cons a f : Fin 3 -> Index) 2 = f 1 := rfl

private theorem affineDet_two (z : Fin 3 -> Paper.Point 2) :
    Geometry.affineDet z = z 0 0 * z 1 1 - z 0 0 * z 2 1 -
      z 0 1 * z 1 0 + z 0 1 * z 2 0 + z 1 0 * z 2 1 - z 1 1 * z 2 0 := by
  unfold Geometry.affineDet
  rw [Matrix.det_fin_three]
  change z 0 0 * z 1 1 * 1 - z 0 0 * 1 * z 2 1 -
    z 0 1 * z 1 0 * 1 + z 0 1 * 1 * z 2 0 +
    1 * z 1 0 * z 2 1 - 1 * z 1 1 * z 2 0 = _
  ring

private def squareDet (f : Fin 3 -> Paper.Cube 2) : Int :=
  let b : Fin 3 -> Fin 2 -> Int := fun i j => if f i j then 1 else 0
  b 0 0 * b 1 1 - b 0 0 * b 2 1 - b 0 1 * b 1 0 +
    b 0 1 * b 2 0 + b 1 0 * b 2 1 - b 1 1 * b 2 0

private theorem squareDet_of_injective :
    forall f : Fin 3 -> Paper.Cube 2, Function.Injective f -> |squareDet f| = 1 := by
  decide

private theorem squareDet_cast (f : Fin 3 -> Paper.Cube 2) :
    (squareDet f : Real) = Geometry.affineDet (fun i => Paper.cubePoint (f i)) := by
  rw [affineDet_two]
  simp [squareDet, Paper.cubePoint]

/-- Every triangle formed by three distinct unit-square vertices has Euclidean area 1/2. -/
theorem square_triangle_area (f : Fin 3 -> Paper.Cube 2) (hf : Function.Injective f) :
    Paper.simplexVolume (fun i => Paper.cubePoint (f i)) = 1 / 2 := by
  have hd : |Geometry.affineDet (fun i => Paper.cubePoint (f i))| = 1 := by
    rw [<- squareDet_cast, <- Int.cast_abs, squareDet_of_injective f hf]
    norm_num
  have h := Geometry.simplex_volume_factorial (fun i => Paper.cubePoint (f i))
  rw [hd] at h
  norm_num at h
  change Geometry.simplexVolume (fun i => Paper.cubePoint (f i)) = 1 / 2
  linarith

private theorem square_determinant_sum :
    Finset.sum Finset.univ (fun f : Fin 3 -> Paper.Cube 2 =>
      Finset.prod Finset.univ (fun _ : Fin 3 => (1 / 4 : Real)) *
        |Geometry.affineDet (fun i => Paper.cubePoint (f i))|) = 3 / 8 := by
  simp_rw [sum_fin_function_succ]
  norm_num [Fintype.sum_bool, Fin.sum_univ_succ, Fin.prod_univ_succ,
    affineDet_two, Paper.cubePoint, cons_two]

private theorem square_distinct_count :
    (Finset.univ.filter (fun f : Fin 3 -> Paper.Cube 2 => Function.Injective f)).card = 24 := by
  decide

private theorem square_distinct_indicator_sum :
    Finset.sum Finset.univ (fun f : Fin 3 -> Paper.Cube 2 =>
      Finset.prod Finset.univ (fun _ : Fin 3 => (1 / 4 : Real)) *
        (if Function.Injective f then 1 else 0)) = 3 / 8 := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_ite,
    mul_one, mul_zero]
  rw [<- Finset.sum_filter]
  simp only [Finset.sum_const, square_distinct_count, nsmul_eq_mul]
  norm_num

private theorem cubePoint_injective :
    Function.Injective (Paper.cubePoint : Paper.Cube 2 -> Paper.Point 2) := by
  intro v w hvw
  funext j
  have h := congrFun hvw j
  cases hv : v j <;> cases hw : w j <;> simp_all [Paper.cubePoint]

private theorem measurableSet_injective_squareTuple :
    MeasurableSet {z : Fin 3 -> Paper.Point 2 | Function.Injective z} := by
  have heq : {z : Fin 3 -> Paper.Point 2 | Function.Injective z} =
      Set.iInter (fun i : Fin 3 => Set.iInter (fun j : Fin 3 =>
        {z : Fin 3 -> Paper.Point 2 | z i = z j -> i = j})) := by
    ext z
    simp [Function.Injective]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  next => simp [hij]
  next =>
    have hh : MeasurableSet {z : Fin 3 -> Paper.Point 2 | Not (z i = z j)} :=
      (isClosed_eq
        (continuous_apply i : Continuous (fun z : Fin 3 -> Paper.Point 2 => z i))
        (continuous_apply j : Continuous (fun z : Fin 3 -> Paper.Point 2 => z j))).measurableSet.compl
    have heq : {z : Fin 3 -> Paper.Point 2 | z i = z j -> i = j} =
        {z : Fin 3 -> Paper.Point 2 | Not (z i = z j)} := by
      ext z
      simp [hij]
    rw [heq]
    exact hh

/-- The defined four-vertex law is genuinely a probability measure. -/
theorem uniformSquare_probability : IsProbabilityMeasure uniformSquareLaw := by
  apply CubeEndpoint.cubeLaw_probability (fun _ : Paper.Cube 2 => (1 / 4 : Real))
  next => intro v; norm_num
  next => norm_num [Paper.totalWeight]

/-- The three actual iid square vertices are distinct with probability 3/8. -/
theorem uniformSquare_distinct_probability :
    (Measure.pi (fun _ : Fin 3 => uniformSquareLaw)).real
      {z | Function.Injective z} = 3 / 8 := by
  have hset := measurableSet_injective_squareTuple
  rw [<- integral_indicator_one hset]
  unfold uniformSquareLaw CubeEndpoint.cubeLaw
  rw [FiniteAtomicGeneric.iid_atomicLaw_integral
    (fun _ : Paper.Cube 2 => (1 / 4 : Real)) (by intro v; norm_num) Paper.cubePoint
    (Set.indicator {z : Fin 3 -> Paper.Point 2 | Function.Injective z} 1)
    ((measurable_const : Measurable (fun _ : Fin 3 -> Paper.Point 2 => (1 : Real))).indicator
      hset).stronglyMeasurable]
  have hinj (f : Fin 3 -> Paper.Cube 2) :
      Function.Injective (fun i => Paper.cubePoint (f i)) <-> Function.Injective f :=
    cubePoint_injective.of_comp_iff f
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hinj]
  exact square_distinct_indicator_sum

/-- Source introduction: exact expected area of three iid uniform square vertices. -/
theorem uniformSquare_expectedSimplexVolume :
    Paper.expectedSimplexVolume uniformSquareLaw = 3 / 16 := by
  have hdet : integral (Measure.pi (fun _ : Fin 3 => uniformSquareLaw))
      (fun z => |Geometry.affineDet z|) = 3 / 8 := by
    unfold uniformSquareLaw CubeEndpoint.cubeLaw
    rw [FiniteAtomicGeneric.iid_atomicLaw_integral
      (fun _ : Paper.Cube 2 => (1 / 4 : Real)) (by intro v; norm_num)
      Paper.cubePoint (fun z => |Geometry.affineDet z|)
      (continuous_abs.comp EndpointAssembly.affineDet_continuous).stronglyMeasurable]
    exact square_determinant_sum
  have h := EndpointAssembly.expected_volume_normalization uniformSquareLaw
  rw [hdet] at h
  norm_num at h
  linarith

/-- Both actual independent-copy coordinate gaps are exactly one half. -/
theorem uniformSquare_coordinateGap (j : Fin 2) :
    Paper.coordinateGap uniformSquareLaw j = 1 / 2 := by
  unfold Paper.coordinateGap uniformSquareLaw CubeEndpoint.cubeLaw
  rw [FiniteAtomicGeneric.pair_atomicLaw_integral
    (fun _ : Paper.Cube 2 => (1 / 4 : Real)) (by intro v; norm_num)
    Paper.cubePoint (fun zz => |zz.1 j - zz.2 j|)
    (continuous_abs.comp
      (((continuous_apply j).comp continuous_fst).sub
        ((continuous_apply j).comp continuous_snd))).stronglyMeasurable]
  simp_rw [sum_fin_function_succ]
  fin_cases j
  all_goals norm_num [Fintype.sum_bool, Paper.cubePoint]

/-- The literal source main inequality is an equality for the uniform square. -/
theorem uniformSquare_main_equality :
    Paper.expectedSimplexVolume uniformSquareLaw =
      ((2 + 1 : Nat) : Real) / (2 : Real) ^ 2 *
        Finset.prod Finset.univ (fun j => Paper.coordinateGap uniformSquareLaw j) := by
  simp_rw [uniformSquare_coordinateGap]
  rw [uniformSquare_expectedSimplexVolume]
  norm_num

/-- The same square also attains the source one-step inequality in dimension two. -/
theorem uniformSquare_oneStep_equality :
    Paper.expectedSimplexVolume uniformSquareLaw =
      (3 / 4 : Real) * Paper.coordinateGap uniformSquareLaw (Fin.last 1) *
        Paper.expectedSimplexVolume (uniformSquareLaw.map Paper.projectLast) := by
  have : IsProbabilityMeasure uniformSquareLaw := uniformSquare_probability
  have : IsProbabilityMeasure (uniformSquareLaw.map Paper.projectLast) :=
    EndpointAssembly.projection_probability uniformSquareLaw
  rw [EndpointAssembly.base_one, EndpointAssembly.coordinateGap_projection,
    uniformSquare_expectedSimplexVolume]
  simp_rw [uniformSquare_coordinateGap]
  norm_num

end Hypercube.Examples
