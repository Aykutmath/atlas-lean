import AHHMomentRecurrence
import AHHCanonicalLoop

/-! All finite combinatorics and scalar inequalities are assembled behind the
literal one-subsystem position-loop identity. The fresh-letter case is derived
from that identity rather than added as a separate assumption. -/
noncomputable section
open scoped BigOperators
namespace AHH
attribute [local instance] Classical.propDecidable
variable {α : Type*}

/-- An absent letter makes every derivative term in the position loop vanish. -/
theorem fresh_letter_of_position_loop (f : List α → ℝ) (g : List α → List α → ℝ) (H : ℝ)
    (hloop : ∀ s w, f (s :: w) =
      (f w + ∑ k : Fin w.length, if s = w.get k then
        g (s :: w.take k.val) (w.drop (k.val + 1)) else 0) / H)
    (s : α) (w : List α) (hs : s ∉ w) : f (s :: w) = f w / H := by
  have hneq : ∀ k : Fin w.length, s ≠ w.get k := by
    intro k heq
    exact hs (heq.symm ▸ List.get_mem w k)
  have hh := hloop s w
  have hz : (∑ k : Fin w.length, if s = w.get k then
      g (s :: w.take k.val) (w.drop (k.val + 1)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (hneq k)
  rw [hz, add_zero] at hh
  exact hh

/-- End of the combinatorial proof: exact local Gaussian identities imply the
finite sharp upper moment bound with the explicit conservative constants. -/
theorem moment_bound_of_position_loop [Fintype α]
    (f : List α → ℝ) (g : List α → List α → ℝ)
    {H : ℝ} (hH : 1 ≤ H) (hzero : f [] = H) (m : ℕ)
    (hcyclic : ∀ U V, f (U ++ V) = f (V ++ U))
    (hglue : ∀ (a : α) U V X Y,
      g (U ++ [a] ++ V) (X ++ [a] ++ Y) = f (U ++ [a] ++ Y ++ X ++ [a] ++ V))
    (hdisjoint : ∀ d : WordSplit α, ¬ d.shared → g d.L d.R = f d.L * f d.R)
    (hloop : ∀ s w, f (s :: w) =
      (f w + ∑ k : Fin w.length, if s = w.get k then
        g (s :: w.take k.val) (w.drop (k.val + 1)) else 0) / H) :
    wordSum (fun w => f w ^ 2) m ≤ H ^ 2 * edgeR (1 + 1 / Real.sqrt H)
      ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) *
      edgeL (1 + 1 / Real.sqrt H)
        ((Fintype.card α : ℝ) / H ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt H) ^ m := by
  apply moment_bound_of_one_subsystem_laws f g hH hzero m
  · intro n _ s w _ hs
    exact fresh_letter_of_position_loop f g H hloop s w hs
  · exact hdisjoint
  · intro c
    exact hglue c.a c.U c.V c.X c.Y
  · intro n _ d _
    exact WordSplit.canonical_loop_of_position_loop f g hcyclic hglue H hloop d

end AHH
