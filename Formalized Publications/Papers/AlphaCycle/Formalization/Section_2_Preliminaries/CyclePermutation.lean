import Section_2_Preliminaries.Relaxation

/-! Permuting no-private triples and aligning supported alpha-cycles with their
three distinct parent edges. -/
namespace AlphaCycle
open Classical

lemma three_perm_cases (σ : Equiv.Perm (Fin 3)) :
    (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨
    (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨
    (σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2) ∨
    (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
    (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨
    (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by
  have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have h12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  generalize h0 : σ 0 = a at *
  generalize h1 : σ 1 = b at *
  generalize h2 : σ 2 = c at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem noPrivate_permute (f : Fin 3 → Finset V) (σ : Equiv.Perm (Fin 3))
    (h : Triangle.NoPrivate (f 0) (f 1) (f 2)) :
    Triangle.NoPrivate (f (σ 0)) (f (σ 1)) (f (σ 2)) := by
  rcases three_perm_cases σ with hσ | hσ | hσ | hσ | hσ | hσ
  all_goals
    rcases hσ with ⟨h0, h1, h2⟩
    simp only [h0, h1, h2, Triangle.NoPrivate] at *
    aesop (add simp [Finset.union_comm])

/-- The four inequalities are unchanged by any permutation of the three edges. -/
 theorem generalizedTriangle_permute (e : Fin 3 → Finset V)
    (f : Fin 3 → Finset V) (hf : ∀ i, f i ∈ completedSupport e)
    (z : MomentVector (completedSupport e)) (σ : Equiv.Perm (Fin 3)) :
    generalizedTriangle e (fun i => f (σ i)) (fun i => hf (σ i)) z ↔
      generalizedTriangle e f hf z := by
  rcases three_perm_cases σ with hσ | hσ | hσ | hσ | hσ | hσ
  all_goals
    rcases hσ with ⟨h0, h1, h2⟩
    simp only [generalizedTriangle, h0, h1, h2, Triangle.GT,
      Finset.inter_comm, Finset.inter_left_comm, Finset.inter_assoc] <;>
      constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

 theorem intersections_subset_two (f : Fin 3 → Finset V) (i j : Fin 3) (hij : i ≠ j) :
    (f 0 ∩ f 1) ∪ (f 1 ∩ f 2) ∪ (f 0 ∩ f 2) ⊆ f i ∪ f j := by
  intro v hv
  fin_cases i <;> fin_cases j <;>
    simp_all only [Finset.mem_union, Finset.mem_inter] <;> tauto

/-- Every choice of containing parents for an alpha-cycle is injective. -/
 theorem SupportedCycle.parents_injective {e : Fin 3 → Finset V} (f : SupportedCycle e)
    (p : Fin 3 → Fin 3) (hp : ∀ i, f.edge i ⊆ e (p i)) : Function.Injective p := by
  intro i j he
  by_contra hij
  apply f.alpha (p i)
  apply (intersections_subset_two f.edge i j hij).trans
  apply Finset.union_subset (hp i)
  simpa only [he] using hp j

/-- Any supported alpha-cycle admits an ordering aligned with the generating edges. -/
 theorem SupportedCycle.exists_alignment {e : Fin 3 → Finset V} (f : SupportedCycle e) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, f.edge (σ i) ⊆ e i := by
  have hex : ∀ i, ∃ j, f.edge i ⊆ e j := fun i =>
    (mem_completedSupport e (f.edge i)).mp (f.supported i)
  choose p hp using hex
  have hi := f.parents_injective p hp
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective p ((Finite.injective_iff_bijective).mp hi)
  refine ⟨τ.symm, ?_⟩
  intro i
  have he : p (τ.symm i) = i := τ.apply_symm_apply i
  simpa only [he] using hp (τ.symm i)

/-- Checking all aligned triples is sufficient for every alpha-cycle in the
completed support. The complete-edge condition is passed through unchanged. -/
 theorem allCycleRelaxation_of_aligned (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) (hz : z ∈ completeEdgeRelaxation e)
    (halign : ∀ (f : Fin 3 → Finset V) (hf : ∀ i, f i ⊆ e i),
      Triangle.NoPrivate (f 0) (f 1) (f 2) → ∀ U : Finset V,
      generalizedTriangle e f (fun i => mem_completedSupport_of_subset e i (f i) (hf i))
        (switchVector e U z)) :
    z ∈ allCycleRelaxation e := by
  refine ⟨hz, ?_⟩
  intro f U
  obtain ⟨σ, hσ⟩ := f.exists_alignment
  have h := halign (fun i => f.edge (σ i)) hσ (noPrivate_permute f.edge σ f.noPrivate) U
  exact (generalizedTriangle_permute e f.edge f.supported (switchVector e U z) σ).mp h

end AlphaCycle
