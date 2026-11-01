import Section_10_Zonoid.Hypercube.PaperIntegrability
import Mathlib.Probability.Independence.Basic

/-!
Explicit meaning of the paper's moment and iid conventions. The canonical
coordinate functions are measurable, so finite nonnegative expectations of
absolute coordinates are exactly the governed integrability hypotheses.
Independent random vectors with the same law have the product law used in
the paper-facing simplex expectation definition.
-/

noncomputable section

namespace Hypercube.PaperLawBridge

open MeasureTheory ProbabilityTheory

theorem finiteCoordinateFirstMoments_iff_lintegral {d : Nat}
    (nu : Measure (Paper.Point d)) :
    Paper.finiteCoordinateFirstMoments nu <->
      forall j : Fin d, lintegral nu (fun z => ENNReal.ofReal |z j|) < Top.top := by
  unfold Paper.finiteCoordinateFirstMoments
  apply forall_congr'
  intro j
  have hm : AEStronglyMeasurable (fun z : Paper.Point d => |z j|) nu :=
    ((continuous_apply j).abs).measurable.aestronglyMeasurable
  have hn : Filter.Eventually (fun z : Paper.Point d => 0 <= |z j|) (ae nu) :=
    Filter.Eventually.of_forall (fun z => abs_nonneg (z j))
  rw [Integrable, hasFiniteIntegral_iff_ofReal hn]
  simp only [hm, true_and]

theorem iid_joint_law {Index Space Omega : Type*} [Fintype Index]
    [MeasurableSpace Space] [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure Space) (X : Index -> Omega -> Space)
    (hX : forall i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : forall i, P.map (X i) = nu) :
    P.map (fun w i => X i w) = Measure.pi (fun _ : Index => nu) := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hX i).aemeasurable) hind]
  simp only [hlaw]

theorem iid_integral {Index Space Omega : Type*} [Fintype Index]
    [MeasurableSpace Space] [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure Space) (X : Index -> Omega -> Space)
    (hX : forall i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : forall i, P.map (X i) = nu)
    (F : (Index -> Space) -> Real)
    (hF : AEStronglyMeasurable F (Measure.pi (fun _ : Index => nu))) :
    integral (Measure.pi (fun _ : Index => nu)) F =
      integral P (fun w => F (fun i => X i w)) := by
  have hj := iid_joint_law P nu X hX hind hlaw
  have hz : Measurable (fun w i => X i w) := Measurable.of_eval hX
  rw [<- hj] at hF
  rw [<- hj]
  exact integral_map hz.aemeasurable hF

theorem expectedSimplexVolume_eq_iid_expectation {d : Nat}
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (X : Fin (d + 1) -> Omega -> Paper.Point d)
    (hX : forall i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : forall i, P.map (X i) = nu)
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.expectedSimplexVolume nu =
      integral P (fun w => Paper.simplexVolume (fun i => X i w)) := by
  exact iid_integral P nu X hX hind hlaw Paper.simplexVolume
    (PaperIntegrability.simplexVolume_integrable nu hfirst).aestronglyMeasurable

theorem coordinateGap_eq_independent_expectation {d : Nat}
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (X Y : Omega -> Paper.Point d) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (hlawX : P.map X = nu) (hlawY : P.map Y = nu)
    (hfirst : Paper.finiteCoordinateFirstMoments nu) (j : Fin d) :
    Paper.coordinateGap nu j = integral P (fun w => |X w j - Y w j|) := by
  have hj : P.map (fun w => (X w, Y w)) = nu.prod nu := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind
    simpa only [hlawX, hlawY] using h
  have hi := PaperIntegrability.coordinateGap_integrable nu hfirst j
  rw [<- hj] at hi
  unfold Paper.coordinateGap
  rw [<- hj]
  exact integral_map (hX.prodMk hY).aemeasurable hi.aestronglyMeasurable

end Hypercube.PaperLawBridge
