import Section_2_Preliminaries.Polytope
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The constructive converse of Boolean moment inversion.  The inverse cell
formula is defined for arbitrary real moment coordinates, before any law exists.
Nonnegative inverse cells with empty moment one then construct that law. -/
namespace AlphaCycle
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The upper-set sum sends arbitrary signed cell masses to their moments. -/
noncomputable def upperMomentMap : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun p s := ∑ x, if s ⊆ x then p x else 0
  map_add' p q := by
    funext s
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  map_smul' c p := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp

/-- Alternating moment sum giving the mass of one exact Boolean cell. -/
noncomputable def inverseCell (e : Finset V) (z : Finset V → ℝ) (O : Finset V) : ℝ :=
  ∑ W ∈ (e \ O).powerset, (-1 : ℝ) ^ W.card * z (O ∪ W)

/-- The full Boolean-lattice inversion, as a linear map. -/
noncomputable def inverseMomentMap : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun z O := inverseCell Finset.univ z O
  map_add' p q := by
    funext s
    simp [inverseCell, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    funext s
    simp [inverseCell, Finset.mul_sum, mul_left_comm]

/-- Inclusion-exclusion recovers arbitrary signed cell masses, with no positivity
or normalization assumption. -/
theorem inverseMomentMap_upperMomentMap (p : Finset V → ℝ) :
    inverseMomentMap (upperMomentMap p) = p := by
  funext O
  change (∑ W ∈ (Finset.univ \ O).powerset, (-1 : ℝ) ^ W.card *
    ∑ x, if O ∪ W ⊆ x then p x else 0) = p O
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcell (x : Finset V) :
      (O ⊆ x ∧ Disjoint (Finset.univ \ O) x) ↔ x = O := by
    constructor
    · rintro ⟨ho, hd⟩
      apply Finset.Subset.antisymm _ ho
      intro v hv
      by_contra hn
      exact Finset.disjoint_left.mp hd (by simp [hn]) hv
    · rintro rfl
      exact ⟨Finset.Subset.refl _, Finset.sdiff_disjoint⟩
  calc
    _ = ∑ x, p x * ∑ W ∈ (Finset.univ \ O).powerset,
        (-1 : ℝ) ^ W.card * (if O ∪ W ⊆ x then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W _
      by_cases h : O ∪ W ⊆ x <;> simp [h, mul_comm]
    _ = ∑ x, if x = O then p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [signed_monomial_identity]
      simp only [hcell]
      split_ifs <;> simp
    _ = p O := by simp

/-- Conversely, summing the explicitly inverted cells gives back every prescribed
moment. This is the finite-dimensional converse of the same inversion identity. -/
theorem upperMomentMap_inverseMomentMap (z : Finset V → ℝ) :
    upperMomentMap (inverseMomentMap z) = z := by
  have h : (inverseMomentMap (V := V)).comp upperMomentMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact inverseMomentMap_upperMomentMap p
  have h' := (LinearMap.comp_eq_id_comm ℝ (Finset V → ℝ)).mp h
  exact congrArg (fun f : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) => f z) h'

/-- Extend an edge's moment coordinates by zero outside that edge. -/
noncomputable def edgeMomentExtension (e : Finset V) (z : Finset V → ℝ)
    (s : Finset V) : ℝ := if s ⊆ e then z s else 0

/-- Inverting the zero extension produces exactly the edge's prescribed inverse
cells, and puts zero mass on assignments outside the edge. -/
theorem inverseMomentMap_edgeMomentExtension (e : Finset V) (z : Finset V → ℝ)
    (O : Finset V) :
    inverseMomentMap (edgeMomentExtension e z) O =
      if O ⊆ e then inverseCell e z O else 0 := by
  change inverseCell Finset.univ (edgeMomentExtension e z) O = _
  unfold inverseCell
  by_cases hO : O ⊆ e
  · simp only [hO, ↓reduceIte]
    have hsub : (e \ O).powerset ⊆ (Finset.univ \ O).powerset := by
      intro W hW
      apply Finset.mem_powerset.mpr
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hW hv)).2⟩
    calc
      _ = ∑ W ∈ (e \ O).powerset,
          (-1 : ℝ) ^ W.card * edgeMomentExtension e z (O ∪ W) := by
        symm
        apply Finset.sum_subset hsub
        intro W hW hnW
        have hWe : ¬ W ⊆ e := by
          intro h
          apply hnW
          apply Finset.mem_powerset.mpr
          intro v hv
          exact Finset.mem_sdiff.mpr ⟨h hv,
            (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hW hv)).2⟩
        simp [edgeMomentExtension, Finset.union_subset_iff, hWe]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro W hW
        have hWe : W ⊆ e := (Finset.mem_powerset.mp hW).trans Finset.sdiff_subset
        simp [edgeMomentExtension, Finset.union_subset_iff, hO, hWe]
  · simp [hO, edgeMomentExtension, Finset.union_subset_iff]

/-- The constructive moment identity on an arbitrary finite edge: summing its
inverse cells over assignments containing `s` recovers the given moment. -/
theorem sum_inverseCell_eq (e : Finset V) (z : Finset V → ℝ)
    (s : Finset V) (hs : s ⊆ e) :
    (∑ O ∈ e.powerset, if s ⊆ O then inverseCell e z O else 0) = z s := by
  have h := congrFun (upperMomentMap_inverseMomentMap (edgeMomentExtension e z)) s
  change (∑ O, if s ⊆ O then
    inverseMomentMap (edgeMomentExtension e z) O else 0) = _ at h
  simp_rw [inverseMomentMap_edgeMomentExtension] at h
  simp only [edgeMomentExtension, hs, ↓reduceIte] at h
  rw [← h]
  calc
    _ = ∑ O ∈ e.powerset, if s ⊆ O then
          (if O ⊆ e then inverseCell e z O else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro O hO
      simp [Finset.mem_powerset.mp hO]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro O _ hO
      simp only [Finset.mem_powerset] at hO
      simp [hO]

/-- In particular, the inverse cells sum to the empty moment. -/
theorem sum_inverseCell (e : Finset V) (z : Finset V → ℝ) :
    (∑ O ∈ e.powerset, inverseCell e z O) = z ∅ := by
  simpa using sum_inverseCell_eq e z ∅ (Finset.empty_subset e)

/-- Construct a Boolean law from the inverse cells. The cells outside `e` have
zero mass. This directly implements the constructive converse in the paper. -/
noncomputable def lawOfInverseCells (e : Finset V) (z : Finset V → ℝ)
    (hzero : z ∅ = 1) (hpos : ∀ O, O ⊆ e → 0 ≤ inverseCell e z O) : BooleanLaw V where
  mass O := if O ⊆ e then inverseCell e z O else 0
  nonneg O := by split_ifs with hO; exact hpos O hO; exact le_rfl
  total := by
    have h := congrFun (upperMomentMap_inverseMomentMap (edgeMomentExtension e z)) ∅
    change (∑ O : Finset V, if (∅ : Finset V) ⊆ O then
      inverseMomentMap (edgeMomentExtension e z) O else 0) = _ at h
    simpa only [Finset.empty_subset, ↓reduceIte, inverseMomentMap_edgeMomentExtension,
      edgeMomentExtension, hzero] using h

/-- Every subset moment of the explicitly constructed law equals the input. -/
theorem moment_lawOfInverseCells (e : Finset V) (z : Finset V → ℝ)
    (hzero : z ∅ = 1) (hpos : ∀ O, O ⊆ e → 0 ≤ inverseCell e z O)
    (s : Finset V) (hs : s ⊆ e) :
    moment (lawOfInverseCells e z hzero hpos) s = z s := by
  classical
  have h := congrFun (upperMomentMap_inverseMomentMap (edgeMomentExtension e z)) s
  change (∑ O, if s ⊆ O then
    inverseMomentMap (edgeMomentExtension e z) O else 0) = _ at h
  simp only [inverseMomentMap_edgeMomentExtension, edgeMomentExtension, hs, ↓reduceIte] at h
  rw [← h]
  unfold moment Law.prob
  apply Finset.sum_congr rfl
  intro O _
  by_cases hO : s ⊆ O <;> simp [lawOfInverseCells, hO]

/-- The alternating sum used in the proof cancels unless the interval has a
single element. -/
theorem alternating_interval_sum (A F : Finset V) (hAF : A ⊆ F) :
    (∑ W ∈ (F \ A).powerset, (-1 : ℝ) ^ W.card) = if A = F then 1 else 0 := by
  classical
  have h := signed_monomial_identity (∅ : Finset V) (F \ A) Finset.univ
  have hcond : Disjoint (F \ A) Finset.univ ↔ A = F := by
    constructor
    · intro hd
      apply Finset.Subset.antisymm hAF
      intro v hv
      by_contra hn
      exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨hv, hn⟩) (Finset.mem_univ v)
    · rintro rfl
      simp
  simpa [hcond] using h

/-- An edge inverse cell equals the corresponding atom of the restricted law. -/
theorem inverseCell_eq_restrictLaw_mass (e : Finset V) (μ : BooleanLaw V)
    (O : Finset V) (hO : O ⊆ e) :
    inverseCell e (moment μ) O = (restrictLaw μ e).mass O := by
  have hm : moment (restrictLaw μ e) = edgeMomentExtension e (moment μ) := by
    funext s
    by_cases hs : s ⊆ e
    · simp [edgeMomentExtension, hs, moment_restrict μ e s hs]
    · simp [edgeMomentExtension, hs, moment_restrict_eq_zero μ e s hs]
  have h := mass_eq_signed_moments (restrictLaw μ e) O
  change (restrictLaw μ e).mass O = inverseMomentMap (moment (restrictLaw μ e)) O at h
  rw [hm, inverseMomentMap_edgeMomentExtension] at h
  simpa [hO] using h.symm

omit [Fintype V] in
/-- Two moment lists agreeing on an edge have identical inverse cells there. -/
theorem inverseCell_congr (e : Finset V) (z w : Finset V → ℝ)
    (hz : ∀ s, s ⊆ e → z s = w s) (O : Finset V) (hO : O ⊆ e) :
    inverseCell e z O = inverseCell e w O := by
  unfold inverseCell
  apply Finset.sum_congr rfl
  intro W hW
  rw [hz (O ∪ W) (Finset.union_subset hO
    ((Finset.mem_powerset.mp hW).trans Finset.sdiff_subset))]

/-- Normalization and all inverse-cell inequalities are exactly the existence of
a law realizing the entire list of edge moments. -/
theorem exists_law_with_moments_iff (e : Finset V) (z : Finset V → ℝ) :
    (∃ μ : BooleanLaw V, ∀ s, s ⊆ e → moment μ s = z s) ↔
      z ∅ = 1 ∧ ∀ O, O ⊆ e → 0 ≤ inverseCell e z O := by
  constructor
  · rintro ⟨μ, hμ⟩
    constructor
    · rw [← hμ ∅ (Finset.empty_subset _), moment_empty]
    · intro O hO
      rw [inverseCell_congr e z (moment μ) (fun s hs => (hμ s hs).symm) O hO,
        inverseCell_eq_restrictLaw_mass e μ O hO]
      exact (restrictLaw μ e).nonneg O
  · rintro ⟨hzero, hpos⟩
    exact ⟨lawOfInverseCells e z hzero hpos, moment_lawOfInverseCells e z hzero hpos⟩

/-- Read the completed vector on one edge, setting all other moments to zero. -/
noncomputable def edgeCoordinates (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) (i : Fin 3) (s : Finset V) : ℝ :=
  if hs : s ⊆ e i then z ⟨s, mem_completedSupport_of_subset e i s hs⟩ else 0

theorem edgeCoordinates_of_subset (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) (i : Fin 3) (s : Finset V)
    (hs : s ⊆ e i) :
    edgeCoordinates e z i s = z ⟨s, mem_completedSupport_of_subset e i s hs⟩ := by
  simp [edgeCoordinates, hs]

/-- The complete-edge inequality for the exact assignment with ones `O`. -/
noncomputable def completeEdgeCell (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) (i : Fin 3) (O : Finset V) : ℝ :=
  inverseCell (e i) (edgeCoordinates e z i) O

/-- The local-law definition of CER equals its full system of complete-edge cell
inequalities, together with the adjoined empty coordinate equal to one. -/
theorem mem_completeEdgeRelaxation_iff_cell_inequalities (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) :
    z ∈ completeEdgeRelaxation e ↔
      z ⟨∅, mem_completedSupport_of_subset e 0 ∅ (Finset.empty_subset _)⟩ = 1 ∧
      ∀ i O, O ⊆ e i → 0 ≤ completeEdgeCell e z i O := by
  have hlocal (i : Fin 3) :
      (∃ μ : BooleanLaw V, ∀ s (hs : s ⊆ e i),
        moment μ s = z ⟨s, mem_completedSupport_of_subset e i s hs⟩) ↔
      (∃ μ : BooleanLaw V, ∀ s, s ⊆ e i → moment μ s = edgeCoordinates e z i s) := by
    constructor <;> rintro ⟨μ, hμ⟩ <;> refine ⟨μ, ?_⟩ <;> intro s hs
    · rw [edgeCoordinates_of_subset e z i s hs]
      exact hμ s hs
    · rw [← edgeCoordinates_of_subset e z i s hs]
      exact hμ s hs
  constructor
  · intro hz
    have hi (i : Fin 3) := (exists_law_with_moments_iff (e i) (edgeCoordinates e z i)).mp
      ((hlocal i).mp (hz i))
    constructor
    · simpa [edgeCoordinates] using (hi 0).1
    · intro i O hO
      exact (hi i).2 O hO
  · rintro ⟨hzero, hpos⟩ i
    apply (hlocal i).mpr
    apply (exists_law_with_moments_iff (e i) (edgeCoordinates e z i)).mpr
    refine ⟨?_, hpos i⟩
    simpa [edgeCoordinates] using hzero

end AlphaCycle
