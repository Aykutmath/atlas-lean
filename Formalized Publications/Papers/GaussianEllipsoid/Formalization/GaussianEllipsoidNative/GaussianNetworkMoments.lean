import WickPairingAssignments
import Mathlib.Tactic

/-! Actual Gaussian moments of finite endpoint networks and the elementary
one-factor / two-factor tensor comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace GaussianTensorMoments

abbrev NetworkPairingIndex (E : Type*) [Fintype E] :=
  Fin ((canonicalPairings (Finset.univ.toList : List E)).length)

def networkPairEdges (E : Type*) [Fintype E] (p : NetworkPairingIndex E) : List (E × E) :=
  (canonicalPairings (Finset.univ.toList : List E)).get p

/-- Finite-product version of the actual Gaussian Wick expansion. -/
theorem gaussianProductLaw_network_wick {E I : Type*}
    [Fintype E] [Fintype I] [DecidableEq I] (label : E → I) :
    (∫ x, ∏ e, x (label e) ∂gaussianProductLaw I) =
      ∑ p : NetworkPairingIndex E, (pairingWeight label (networkPairEdges E p) : ℝ) := by
  let P := canonicalPairings (Finset.univ.toList : List E)
  have hlist : List.ofFn (fun p : Fin P.length => pairingWeight label (P.get p)) =
      P.map (pairingWeight label) := by
    change List.ofFn ((pairingWeight label) ∘ P.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  have hsum := congrArg List.sum hlist
  simp only [List.sum_ofFn] at hsum
  have hw := gaussianProductLaw_wick_pairings label (Finset.univ.toList : List E)
  rw [← hsum] at hw
  push_cast at hw
  simpa only [List.map_map, Function.comp_apply, Finset.prod_map_toList,
    networkPairEdges] using hw

variable {E C R : Type*} [Fintype E] [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R]

/-- One real Gaussian endpoint-network moment, summed over sample and row labels. -/
def oneNetworkMoment (c : E → C) (r : E → R) (n h : ℕ) : ℝ :=
  ∑ f : C → Fin n, ∑ g : R → Fin h,
    ∫ x, ∏ e, x (f (c e),g (r e)) ∂gaussianProductLaw (Fin n × Fin h)

/-- Two independent real Gaussian factors sharing their sample assignment. -/
def twoNetworkMoment (c : E → C) (r : E → R) (n h : ℕ) : ℝ :=
  ∑ f : C → Fin n, ∑ g : R → Fin h, ∑ k : R → Fin h,
    (∫ x, ∏ e, x (f (c e),g (r e)) ∂gaussianProductLaw (Fin n × Fin h)) *
    (∫ y, ∏ e, y (f (c e),k (r e)) ∂gaussianProductLaw (Fin n × Fin h))

/-- Exact Wick / quotient expansion of the one-factor network moment. -/
theorem oneNetworkMoment_eq_wick (c : E → C) (r : E → R) (n h : ℕ) :
    oneNetworkMoment c r n h =
      ∑ p : NetworkPairingIndex E,
        ((n ^ classCount (edgeRelation (networkPairEdges E p) c) *
          h ^ classCount (edgeRelation (networkPairEdges E p) r) : ℕ) : ℝ) := by
  unfold oneNetworkMoment
  simp_rw [gaussianProductLaw_network_wick]
  calc
    _ = ∑ f : C → Fin n, ∑ p : NetworkPairingIndex E, ∑ g : R → Fin h,
        (pairingWeight (fun e => (f (c e),g (r e))) (networkPairEdges E p) : ℝ) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact Finset.sum_comm
    _ = ∑ p : NetworkPairingIndex E, ∑ f : C → Fin n, ∑ g : R → Fin h,
        (pairingWeight (fun e => (f (c e),g (r e))) (networkPairEdges E p) : ℝ) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact_mod_cast sum_pairingWeight_entry_assignments (networkPairEdges E p) c r n h

/-- Generic reordering used to move both pairing indices outside assignments. -/
theorem sum_five_swap {A B C D F : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype F] (v : A → B → C → D → F → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ f, v a b c d f) =
      ∑ d, ∑ f, ∑ a, ∑ b, ∑ c, v a b c d f := by
  classical
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ f, ∑ c, v a b c d f := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ f, ∑ b, ∑ c, v a b c d f := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm

/-- Exact joined-partition expansion of the actual two-factor network moment. -/
theorem twoNetworkMoment_eq_wick (c : E → C) (r : E → R) (n h : ℕ) :
    twoNetworkMoment c r n h =
      ∑ p : NetworkPairingIndex E, ∑ q : NetworkPairingIndex E,
        ((n ^ classCount (edgeRelation (networkPairEdges E p) c ⊔
                          edgeRelation (networkPairEdges E q) c) *
          h ^ (classCount (edgeRelation (networkPairEdges E p) r) +
                classCount (edgeRelation (networkPairEdges E q) r)) : ℕ) : ℝ) := by
  unfold twoNetworkMoment
  simp_rw [gaussianProductLaw_network_wick, Finset.sum_mul_sum]
  rw [sum_five_swap]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact_mod_cast sum_two_pairingWeight_entry_assignments
    (networkPairEdges E p) (networkPairEdges E q) c r n h

/-- Direct actual Gaussian tensor-moment comparison. This is not conditional
on any Wick, integration-by-parts, independence, or MGF premise. -/
theorem twoNetworkMoment_le_oneNetworkMoment_sq
    (c : E → C) (r : E → R) {n q h : ℕ} (hq : 1 ≤ q) (hn : n ≤ q^2) :
    twoNetworkMoment c r n h ≤ (oneNetworkMoment c r q h)^2 := by
  rw [twoNetworkMoment_eq_wick, oneNetworkMoment_eq_wick]
  exact_mod_cast tensor_wick_sum_le_square
    (fun p : NetworkPairingIndex E => edgeRelation (networkPairEdges E p) c)
    (fun p => classCount (edgeRelation (networkPairEdges E p) r)) hq hn

#print axioms gaussianProductLaw_network_wick
#print axioms oneNetworkMoment_eq_wick
#print axioms twoNetworkMoment_eq_wick
#print axioms twoNetworkMoment_le_oneNetworkMoment_sq

end GaussianTensorMoments
