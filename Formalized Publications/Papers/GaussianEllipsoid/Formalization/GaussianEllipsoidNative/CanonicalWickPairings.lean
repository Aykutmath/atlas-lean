import GaussianWickRecurrence
import Mathlib.Data.List.InsertIdx
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-! A concrete finite pairing enumeration and the actual Gaussian Wick sum.
The enumeration is canonical recursive pairing, so no theorem counting global
fixed-point-free involutions is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace GaussianTensorMoments

/-- Enumerate pair-edge lists by choosing the partner of the leading endpoint.
List indices distinguish every recursive choice; no quotient or pairing-count
theorem is needed. Odd endpoint lists produce an empty enumeration. -/
def canonicalPairings {E : Type*} : List E → List (List (E × E))
  | [] => [[]]
  | a::l => (List.ofFn (fun j : Fin l.length =>
      (canonicalPairings (l.eraseIdx j)).map (fun p => (a,l.get j)::p))).flatten
termination_by l => l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

/-- Product of all Kronecker-delta constraints associated to one edge list. -/
def pairingWeight {E ι : Type*} [DecidableEq ι] (label : E → ι)
    (p : List (E × E)) : ℕ :=
  (p.map (fun e => if label e.1=label e.2 then 1 else 0)).prod

@[simp] theorem pairingWeight_nil {E ι : Type*} [DecidableEq ι] (label : E → ι) :
    pairingWeight label [] = 1 := rfl

@[simp] theorem pairingWeight_cons {E ι : Type*} [DecidableEq ι] (label : E → ι)
    (a b : E) (p : List (E × E)) :
    pairingWeight label ((a,b)::p) =
      (if label a=label b then 1 else 0)*pairingWeight label p := rfl

/-- Weighted enumeration obeys exactly the same recurrence as Wick moments. -/
theorem canonicalPairings_weight_cons {E ι : Type*} [DecidableEq ι]
    (label : E → ι) (a : E) (l : List E) :
    ((canonicalPairings (a::l)).map (pairingWeight label)).sum =
      ∑ j : Fin l.length, if label a=label (l.get j) then
        ((canonicalPairings (l.eraseIdx j)).map (pairingWeight label)).sum else 0 := by
  rw [canonicalPairings]
  simp only [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
    List.map_map, Function.comp_def, pairingWeight_cons]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

/-- Canonical pair-edge enumeration realizes the recursive Wick count. -/
theorem canonicalPairings_weight_eq_wickCount {E ι : Type*} [DecidableEq ι]
    (label : E → ι) (l : List E) :
    ((canonicalPairings l).map (pairingWeight label)).sum = wickCount (l.map label) := by
  cases l with
  | nil => simp [canonicalPairings, wickCount]
  | cons a l =>
    rw [canonicalPairings_weight_cons]
    simp only [List.map_cons, wickCount, List.length_map, List.get_eq_getElem, List.getElem_map]
    refine Fintype.sum_equiv
      (finCongr (List.length_map label : (l.map label).length = l.length).symm) _ _ ?_
    intro j
    simp only [finCongr_apply, Fin.coe_cast]
    split_ifs
    · rw [List.eraseIdx_map]
      exact canonicalPairings_weight_eq_wickCount label (l.eraseIdx j)
    · rfl
termination_by l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

/-- Actual finite Gaussian Wick expansion as a sum over concrete pairings. -/
theorem gaussianProductLaw_wick_pairings {E ι : Type*} [Fintype ι] [DecidableEq ι]
    (label : E → ι) (l : List E) :
    (∫ x, ((l.map label).map x).prod ∂gaussianProductLaw ι) =
      (((canonicalPairings l).map (pairingWeight label)).sum : ℝ) := by
  rw [gaussianProductLaw_wickCount, canonicalPairings_weight_eq_wickCount]

#print axioms gaussianProductLaw_wick_pairings

end GaussianTensorMoments
