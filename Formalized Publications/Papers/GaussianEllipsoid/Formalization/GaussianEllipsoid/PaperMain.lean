/-
Kernel-checked main-theorem statements, recorded as propositions, not proofs.
There is no theorem declaration asserting either strict-threshold conclusion.
The product Gaussian model is imported with kernel-checked independence and
restriction bridges. The asymptotic threshold proof remains open.
Mathematical source: paper.tex, Theorem 1.1 and Section 2.
-/
import GaussianEllipsoid.Main
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

namespace GaussianEllipsoid

/-- The PSD feasibility event, with no measurability assumption inserted.
Its measurability is an explicit remaining proof obligation. -/
def fitEvent (d n : Nat) : Set (Sample d n) :=
  {x | HasFit x}

/-- The PD feasibility event, with measurability still to be established. -/
def strictFitEvent (d n : Nat) : Set (Sample d n) :=
  {x | HasStrictFit x}

/-- Real-valued probability expression for positive semidefinite feasibility. -/
def fitProbability (d n : Nat) : Real :=
  (gaussianSampleLaw d n (fitEvent d n)).toReal

/-- Real-valued probability expression for positive definite feasibility. -/
def strictFitProbability (d n : Nat) : Real :=
  (gaussianSampleLaw d n (strictFitEvent d n)).toReal

/-- UNPROVED statement target for Theorem 1.1(i).
This is a definition of a proposition, not a theorem or an assumption. -/
def BelowThresholdStatement : Prop :=
  forall n : Nat -> Nat,
    (forall d : Nat, 0 < n d) ->
    Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal) ->
    Filter.Tendsto (fun d => strictFitProbability d (n d))
      Filter.atTop (nhds (1 : Real))

/-- UNPROVED statement target for Theorem 1.1(ii).
This is a definition of a proposition, not a theorem or an assumption. -/
def AboveThresholdStatement : Prop :=
  forall n : Nat -> Nat,
    (forall d : Nat, 0 < n d) ->
    (1 / 4 : ENNReal) < Filter.liminf (dimensionRatio n) Filter.atTop ->
    Filter.Tendsto (fun d => fitProbability d (n d))
      Filter.atTop (nhds (0 : Real))

/-- UNPROVED conjunction corresponding to both strict-threshold directions.
No endpoint assertion is included. No proof is supplied or claimed. -/
def StrictThresholdStatement : Prop :=
  BelowThresholdStatement /\ AboveThresholdStatement

end GaussianEllipsoid
