import Section_2_Preliminaries.Polytope
import Section_2_Preliminaries.Triangle
import Mathlib.Data.Finset.SymmDiff

/-! Actual switched moment inequalities on the completed coordinate space. -/
namespace AlphaCycle
open Classical
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem completedSupport_downward (e : Fin 3 → Finset V)
    {s t : Finset V} (ht : t ∈ completedSupport e) (hst : s ⊆ t) :
    s ∈ completedSupport e := by
  obtain ⟨i, hi⟩ := (mem_completedSupport e t).mp ht
  exact (mem_completedSupport e s).mpr ⟨i, hst.trans hi⟩

/-- A monomial occurring in the signed switching expansion remains supported. -/
 theorem switch_term_supported (e : Fin 3 → Finset V) (u : Finset V)
    (s : {s // s ∈ completedSupport e})
    (w : {w // w ∈ (s.val ∩ u).powerset}) :
    (s.val \ u) ∪ w.val ∈ completedSupport e := by
  apply completedSupport_downward e s.property
  apply Finset.union_subset
  · exact Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp w.property).trans Finset.inter_subset_left

/-- The paper's signed subset formula for switching moment coordinates. -/
noncomputable def switchVector (e : Fin 3 → Finset V) (u : Finset V)
    (z : MomentVector (completedSupport e)) : MomentVector (completedSupport e) :=
  fun s => ∑ w : {w // w ∈ (s.val ∩ u).powerset},
    (-1 : ℝ) ^ w.val.card * z ⟨(s.val \ u) ∪ w.val, switch_term_supported e u s w⟩

/-- Switching a moment coordinate evaluates its positive/negative literal event. -/
 theorem switchVector_moment_probability (e : Fin 3 → Finset V)
    (u : Finset V) (μ : BooleanLaw V) (s : {s // s ∈ completedSupport e}) :
    switchVector e u (momentVector (completedSupport e) μ) s =
      μ.prob (fun x => s.val \ u ⊆ x ∧ Disjoint (s.val ∩ u) x) := by
  unfold switchVector momentVector
  rw [← signed_moments_eq_probability]
  exact Finset.sum_coe_sort (s.val ∩ u).powerset
    (fun w => (-1 : ℝ) ^ w.card * moment μ ((s.val \ u) ∪ w))

/-- The switching/event identity only needs the moments on one containing edge,
so it applies to complete-edge local witnesses without any global realization. -/
 theorem switchVector_local_probability (e : Fin 3 → Finset V)
    (u : Finset V) (z : MomentVector (completedSupport e)) (μ : BooleanLaw V)
    (i : Fin 3)
    (hμ : ∀ t (ht : t ⊆ e i),
      moment μ t = z ⟨t, mem_completedSupport_of_subset e i t ht⟩)
    (s : {s // s ∈ completedSupport e}) (hs : s.val ⊆ e i) :
    switchVector e u z s =
      μ.prob (fun x => s.val \ u ⊆ x ∧ Disjoint (s.val ∩ u) x) := by
  rw [← switchVector_moment_probability e u μ s]
  unfold switchVector momentVector
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  symm
  apply hμ
  apply Finset.union_subset
  · exact Finset.sdiff_subset.trans hs
  · exact ((Finset.mem_powerset.mp w.property).trans Finset.inter_subset_left).trans hs

/-- The literal event is the conjunction event after Boolean complementation. -/
 theorem switched_subset_iff (s x u : Finset V) :
    s ⊆ x ∆ u ↔ s \ u ⊆ x ∧ Disjoint (s ∩ u) x := by
  constructor
  · intro h
    constructor
    · intro v hv
      obtain ⟨hvs, hvu⟩ := Finset.mem_sdiff.mp hv
      rcases Finset.mem_symmDiff.mp (h hvs) with hx | hu
      · exact hx.1
      · exact (hvu hu.1).elim
    · rw [Finset.disjoint_left]
      intro v hv hvx
      obtain ⟨hvs, hvu⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_symmDiff.mp (h hvs) with hx | hu
      · exact hx.2 hvu
      · exact hu.2 hvx
  · rintro ⟨hpos, hneg⟩ v hv
    apply Finset.mem_symmDiff.mpr
    by_cases hu : v ∈ u
    · right
      exact ⟨hu, fun hx => Finset.disjoint_left.mp hneg (Finset.mem_inter.mpr ⟨hv, hu⟩) hx⟩
    · left
      exact ⟨hpos (Finset.mem_sdiff.mpr ⟨hv, hu⟩), hu⟩

/-- The signed switching map preserves the probabilistic moment representation. -/
 theorem switchVector_momentVector (e : Fin 3 → Finset V)
    (u : Finset V) (μ : BooleanLaw V) :
    switchVector e u (momentVector (completedSupport e) μ) =
      momentVector (completedSupport e) (μ.map (fun x => x ∆ u)) := by
  funext s
  rw [switchVector_moment_probability]
  unfold momentVector moment
  rw [Law.prob_map]
  apply Law.prob_congr
  intro x
  exact (switched_subset_iff s.val x u).symm

/-- In particular switching preserves membership in the actual convex hull. -/
 theorem switchVector_mem_multilinearPolytope (e : Fin 3 → Finset V)
    (u : Finset V) {z : MomentVector (completedSupport e)}
    (hz : z ∈ multilinearPolytope (completedSupport e)) :
    switchVector e u z ∈ multilinearPolytope (completedSupport e) := by
  obtain ⟨μ, rfl⟩ := (mem_multilinearPolytope_iff _ _).mp hz
  rw [switchVector_momentVector]
  exact (mem_multilinearPolytope_iff _ _).mpr ⟨_, rfl⟩

/-- Supported no-private triples, with the paper's global alpha-cycle condition. -/
structure SupportedCycle (e : Fin 3 → Finset V) where
  edge : Fin 3 → Finset V
  supported : ∀ i, edge i ∈ completedSupport e
  noPrivate : Triangle.NoPrivate (edge 0) (edge 1) (edge 2)
  incomparable : ∀ i j, i ≠ j → ¬ edge i ⊆ edge j
  alpha : ∀ i, ¬ ((edge 0 ∩ edge 1) ∪ (edge 1 ∩ edge 2) ∪
    (edge 0 ∩ edge 2) ⊆ e i)

/-- The generalized triangle inequalities for a supported triple. -/
def generalizedTriangle (e : Fin 3 → Finset V)
    (f : Fin 3 → Finset V) (hf : ∀ i, f i ∈ completedSupport e)
    (z : MomentVector (completedSupport e)) : Prop :=
  Triangle.GT
    (z ⟨f 0 ∩ f 1 ∩ f 2, completedSupport_downward e (hf 0)
      (Finset.inter_subset_left.trans Finset.inter_subset_left)⟩)
    (z ⟨f 0 ∩ f 1, completedSupport_downward e (hf 0) Finset.inter_subset_left⟩)
    (z ⟨f 1 ∩ f 2, completedSupport_downward e (hf 1) Finset.inter_subset_left⟩)
    (z ⟨f 0 ∩ f 2, completedSupport_downward e (hf 0) Finset.inter_subset_left⟩)
    (z ⟨f 1, hf 1⟩) (z ⟨f 0, hf 0⟩) (z ⟨f 2, hf 2⟩)

/-- The all-cycle relaxation, including every switching of every relevant
supported no-private alpha-cycle inequality. -/
def allCycleRelaxation (e : Fin 3 → Finset V) :
    Set (MomentVector (completedSupport e)) :=
  {z | z ∈ completeEdgeRelaxation e ∧ ∀ f : SupportedCycle e, ∀ u : Finset V,
    generalizedTriangle e f.edge f.supported (switchVector e u z)}

/-- The relaxation for one distinguished reduced cycle. -/
def distinguishedRelaxation (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    Set (MomentVector (completedSupport e)) :=
  {z | z ∈ completeEdgeRelaxation e ∧ ∀ u : Finset V,
    generalizedTriangle e f.edge f.supported (switchVector e u z)}

 theorem allCycleRelaxation_subset_distinguishedRelaxation
    (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    allCycleRelaxation e ⊆ distinguishedRelaxation e f := by
  intro z hz
  exact ⟨hz.1, hz.2 f⟩

/-- Every finite Boolean law satisfies every supported no-private triangle. -/
 theorem generalizedTriangle_momentVector (e : Fin 3 → Finset V)
    (f : Fin 3 → Finset V) (hf : ∀ i, f i ∈ completedSupport e)
    (hn : Triangle.NoPrivate (f 0) (f 1) (f 2)) (μ : BooleanLaw V) :
    generalizedTriangle e f hf (momentVector (completedSupport e) μ) := by
  have hm (s : Finset V) : moment μ s =
      ∑ x : Finset V, μ.mass x * Triangle.event (fun v => decide (v ∈ x)) s := by
    unfold moment Law.prob
    apply Finset.sum_congr rfl
    intro x _
    have hp : Triangle.AllTrue (fun v => decide (v ∈ x)) s ↔ s ⊆ x := by
      simp [Triangle.AllTrue, Finset.subset_iff]
    by_cases hs : s ⊆ x <;> simp [Triangle.event, hp, hs]
  unfold generalizedTriangle momentVector
  simp_rw [hm]
  exact Triangle.weighted_sum _ _ _ _ _ _ _ _ μ.nonneg
    (fun x => Triangle.deterministic (fun v => decide (v ∈ x)) hn)

/-- Every multilinear-polytope point survives every switched no-private
alpha-cycle inequality in the completed support. -/
 theorem multilinearPolytope_subset_allCycleRelaxation (e : Fin 3 → Finset V) :
    multilinearPolytope (completedSupport e) ⊆ allCycleRelaxation e := by
  intro z hz
  refine ⟨multilinearPolytope_subset_completeEdgeRelaxation e hz, ?_⟩
  intro f u
  obtain ⟨μ, rfl⟩ := (mem_multilinearPolytope_iff _ _).mp hz
  rw [switchVector_momentVector]
  exact generalizedTriangle_momentVector e f.edge f.supported f.noPrivate _

end AlphaCycle
