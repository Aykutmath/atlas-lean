import Section_2_Preliminaries.Relaxation
import Section_1_Introduction.Geometry

/-! Relabelling the three parent edges leaves both polyhedral sets unchanged. -/
noncomputable section

namespace AlphaCycle.Reindex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Completion is independent of the order of the generating edges. -/
theorem completedSupport_eq (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3)) :
    completedSupport (e ∘ π) = completedSupport e := by
  ext s
  simp only [mem_completedSupport, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨π i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := π.surjective i
    exact ⟨j, hi⟩

/-- Transport a moment vector by keeping each underlying finite vertex set. -/
def vector (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π))) : MomentVector (completedSupport e) :=
  fun s => z ⟨s.val, (completedSupport_eq e π).symm ▸ s.property⟩

@[simp] theorem vector_apply (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π))) (s : Finset V)
    (hs : s ∈ completedSupport e) (hs' : s ∈ completedSupport (e ∘ π)) :
    vector e π z ⟨s, hs⟩ = z ⟨s, hs'⟩ := rfl

/-- Relabelling the parents commutes with every switching expansion. -/
theorem vector_switch (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π))) (u : Finset V) :
    vector e π (switchVector (e ∘ π) u z) = switchVector e u (vector e π z) := by
  funext s
  rfl

/-- Moment vectors of a fixed global law are independent of parent order. -/
theorem vector_moment (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (μ : BooleanLaw V) :
    vector e π (momentVector (completedSupport (e ∘ π)) μ) =
      momentVector (completedSupport e) μ := rfl

/-- The actual convex hull transports exactly, via its finite-law representation. -/
theorem mem_multilinearPolytope_iff (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π))) :
    z ∈ multilinearPolytope (completedSupport (e ∘ π)) ↔
      vector e π z ∈ multilinearPolytope (completedSupport e) := by
  constructor
  · intro hz
    obtain ⟨μ, rfl⟩ := (AlphaCycle.mem_multilinearPolytope_iff _ _).1 hz
    rw [vector_moment]
    exact (AlphaCycle.mem_multilinearPolytope_iff _ _).2 ⟨μ, rfl⟩
  · intro hz
    obtain ⟨μ, hμ⟩ := (AlphaCycle.mem_multilinearPolytope_iff _ _).1 hz
    apply (AlphaCycle.mem_multilinearPolytope_iff _ _).2
    refine ⟨μ, ?_⟩
    funext s
    exact congrFun hμ ⟨s.val, (completedSupport_eq e π) ▸ s.property⟩

/-- A supported alpha-cycle remains one after reordering its parent edges. -/
def cycle (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (f : SupportedCycle e) : SupportedCycle (e ∘ π) where
  edge := f.edge
  supported i := (completedSupport_eq e π).symm ▸ f.supported i
  noPrivate := f.noPrivate
  incomparable := f.incomparable
  alpha i := f.alpha (π i)

/-- The numerical generalized triangle expression is unchanged by transport. -/
theorem generalizedTriangle_iff (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (f : SupportedCycle e) (z : MomentVector (completedSupport (e ∘ π))) :
    generalizedTriangle (e ∘ π) (cycle e π f).edge (cycle e π f).supported z ↔
      generalizedTriangle e f.edge f.supported (vector e π z) := Iff.rfl

/-- Every complete-edge witness transports to the relabelled coordinate support. -/
theorem mem_completeEdgeRelaxation (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π)))
    (hz : z ∈ completeEdgeRelaxation (e ∘ π)) :
    vector e π z ∈ completeEdgeRelaxation e := by
  intro i
  obtain ⟨μ, hμ⟩ := hz (π.symm i)
  refine ⟨μ, ?_⟩
  intro s hs
  have hs' : s ⊆ (e ∘ π) (π.symm i) := by simpa using hs
  exact hμ s hs'

/-- Every switched inequality of every no-private subcycle is preserved. -/
theorem mem_allCycleRelaxation (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (z : MomentVector (completedSupport (e ∘ π)))
    (hz : z ∈ allCycleRelaxation (e ∘ π)) :
    vector e π z ∈ allCycleRelaxation e := by
  refine ⟨mem_completeEdgeRelaxation e π z hz.1, ?_⟩
  intro f u
  rw [← vector_switch]
  exact (generalizedTriangle_iff e π f _).1 (hz.2 (cycle e π f) u)

/-- In particular a counterexample after parent reindexing gives a counterexample
for the original ordered triple, including all relevant switched inequalities. -/
theorem counterexample (e : Fin 3 → Finset V) (π : Equiv.Perm (Fin 3))
    (h : ∃ z : MomentVector (completedSupport (e ∘ π)),
      z ∈ allCycleRelaxation (e ∘ π) ∧
      z ∉ multilinearPolytope (completedSupport (e ∘ π))) :
    ∃ z : MomentVector (completedSupport e),
      z ∈ allCycleRelaxation e ∧ z ∉ multilinearPolytope (completedSupport e) := by
  obtain ⟨z, hz, hn⟩ := h
  exact ⟨vector e π z, mem_allCycleRelaxation e π z hz,
    fun hm => hn ((mem_multilinearPolytope_iff e π z).2 hm)⟩

/-- Swapping the first and third parents moves block `B` into the `A` position. -/
theorem blockA_swap02 (e : Fin 3 → Finset V) :
    Geometry.blockA (e ∘ Equiv.swap 0 2) = Geometry.blockB e := by
  simp only [Geometry.blockA, Geometry.blockB, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2),
    Finset.inter_comm]

/-- Swapping the second and third parents moves block `C` into the `A` position. -/
theorem blockA_swap12 (e : Fin 3 → Finset V) :
    Geometry.blockA (e ∘ Equiv.swap 1 2) = Geometry.blockC e := by
  simp only [Geometry.blockA, Geometry.blockC, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]

theorem cycle_swap02 (e : Fin 3 → Finset V) (h : Geometry.IsCycle e) :
    Geometry.IsCycle (e ∘ Equiv.swap 0 2) := by
  rcases h with ⟨ha, hb, hc⟩
  simpa only [Geometry.IsCycle, Geometry.blockA, Geometry.blockB, Geometry.blockC,
    Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2),
    Finset.inter_comm] using And.intro hb (And.intro ha hc)

theorem cycle_swap12 (e : Fin 3 → Finset V) (h : Geometry.IsCycle e) :
    Geometry.IsCycle (e ∘ Equiv.swap 1 2) := by
  rcases h with ⟨ha, hb, hc⟩
  simpa only [Geometry.IsCycle, Geometry.blockA, Geometry.blockB, Geometry.blockC,
    Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2),
    Finset.inter_comm] using And.intro hc (And.intro hb ha)

end AlphaCycle.Reindex
