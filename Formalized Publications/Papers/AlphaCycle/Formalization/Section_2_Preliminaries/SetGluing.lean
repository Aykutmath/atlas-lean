import Section_2_Preliminaries.Gluing
import Section_2_Preliminaries.MomentInversion
import Mathlib.Tactic.Tauto

/-! Gluing laws on overlapping vertex sets, followed by restoration of private vertices. -/
noncomputable section
namespace AlphaCycle
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem restrictLaw_restrict (μ : BooleanLaw V) (s t : Finset V) :
    restrictLaw (restrictLaw μ s) t = restrictLaw μ (s ∩ t) := by
  simp only [restrictLaw, Law.map_map, Function.comp_def, Finset.inter_assoc]

theorem restrictLaw_of_subset {μ ν : BooleanLaw V} {s t : Finset V}
    (h : restrictLaw μ s = restrictLaw ν s) (ht : t ⊆ s) :
    restrictLaw μ t = restrictLaw ν t := by
  have he := congrArg (fun ρ => restrictLaw ρ t) h
  simpa only [restrictLaw_restrict, Finset.inter_eq_right.mpr ht] using he

/-- The union of two sampled assignments preserves the first assignment on its
edge whenever the samples agree on the intersection. -/
theorem merge_restrict_left (s t x y : Finset V)
    (h : x ∩ (s ∩ t) = y ∩ (s ∩ t)) :
    ((x ∩ s) ∪ (y ∩ t)) ∩ s = x ∩ s := by
  ext v
  have hv := Finset.ext_iff.mp h v
  simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
  tauto

theorem merge_restrict_right (s t x y : Finset V)
    (h : x ∩ (s ∩ t) = y ∩ (s ∩ t)) :
    ((x ∩ s) ∪ (y ∩ t)) ∩ t = y ∩ t := by
  ext v
  have hv := Finset.ext_iff.mp h v
  simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
  tauto

/-- A finite version of the standard two-set marginal gluing lemma. -/
theorem glue_on_sets (μ ν : BooleanLaw V) (s t : Finset V)
    (h : restrictLaw μ (s ∩ t) = restrictLaw ν (s ∩ t)) :
    ∃ ρ : BooleanLaw V,
      restrictLaw ρ s = restrictLaw μ s ∧ restrictLaw ρ t = restrictLaw ν t := by
  let f : Finset V → Finset V := fun x => x ∩ (s ∩ t)
  let glued := Law.glue μ ν f f h
  let merge : Finset V × Finset V → Finset V := fun xy => (xy.1 ∩ s) ∪ (xy.2 ∩ t)
  refine ⟨glued.map merge, ?_, ?_⟩
  · change (glued.map merge).map (fun x => x ∩ s) = μ.map (fun x => x ∩ s)
    rw [Law.map_map]
    calc
      _ = glued.map (fun xy => xy.1 ∩ s) := by
        apply Law.map_congr_support
        intro xy hxy
        exact merge_restrict_left s t xy.1 xy.2 (Law.glue_support μ ν f f h _ _ hxy)
      _ = (glued.map Prod.fst).map (fun x => x ∩ s) := (Law.map_map Prod.fst (fun x => x ∩ s) glued).symm
      _ = μ.map (fun x => x ∩ s) := by exact congrArg (Law.map (fun x => x ∩ s)) (Law.glue_left μ ν f f h)
  · change (glued.map merge).map (fun x => x ∩ t) = ν.map (fun x => x ∩ t)
    rw [Law.map_map]
    calc
      _ = glued.map (fun xy => xy.2 ∩ t) := by
        apply Law.map_congr_support
        intro xy hxy
        exact merge_restrict_right s t xy.1 xy.2 (Law.glue_support μ ν f f h _ _ hxy)
      _ = (glued.map Prod.snd).map (fun x => x ∩ t) := (Law.map_map Prod.snd (fun x => x ∩ t) glued).symm
      _ = ν.map (fun x => x ∩ t) := by exact congrArg (Law.map (fun x => x ∩ t)) (Law.glue_right μ ν f f h)

/-- Adding a private edge outside a core cannot change another core marginal. -/
theorem union_inter_eq_core_inter {s a b : Finset V} (hab : a ∩ b ⊆ s) :
    (s ∪ a) ∩ b = s ∩ b := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvsa, hvb⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hvsa with hvs | hva
    · exact Finset.mem_inter.mpr ⟨hvs, hvb⟩
    · exact Finset.mem_inter.mpr ⟨hab (Finset.mem_inter.mpr ⟨hva,hvb⟩), hvb⟩
  · exact fun hv => Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

/-- If the core contains every overlap, a realization of the reduced local laws
extends to all three original laws.  The complements of the core are precisely
the private blocks, and may have arbitrary size. -/
theorem restore_private_on_sets (s e₁ e₂ e₃ : Finset V)
    (μ μ₁ μ₂ μ₃ : BooleanLaw V)
    (h₁₂ : e₁ ∩ e₂ ⊆ s) (h₁₃ : e₁ ∩ e₃ ⊆ s) (h₂₃ : e₂ ∩ e₃ ⊆ s)
    (h₁ : restrictLaw μ (s ∩ e₁) = restrictLaw μ₁ (s ∩ e₁))
    (h₂ : restrictLaw μ (s ∩ e₂) = restrictLaw μ₂ (s ∩ e₂))
    (h₃ : restrictLaw μ (s ∩ e₃) = restrictLaw μ₃ (s ∩ e₃)) :
    ∃ ρ : BooleanLaw V,
      restrictLaw ρ e₁ = restrictLaw μ₁ e₁ ∧
      restrictLaw ρ e₂ = restrictLaw μ₂ e₂ ∧
      restrictLaw ρ e₃ = restrictLaw μ₃ e₃ := by
  obtain ⟨ρ₁, hρ₁s, hρ₁e⟩ := glue_on_sets μ μ₁ s e₁ h₁
  have hover₂ : restrictLaw ρ₁ ((s ∪ e₁) ∩ e₂) =
      restrictLaw μ₂ ((s ∪ e₁) ∩ e₂) := by
    rw [union_inter_eq_core_inter h₁₂]
    exact (restrictLaw_of_subset hρ₁s Finset.inter_subset_left).trans h₂
  obtain ⟨ρ₂, hρ₂s, hρ₂e⟩ := glue_on_sets ρ₁ μ₂ (s ∪ e₁) e₂ hover₂
  have hc : (s ∪ e₁ ∪ e₂) ∩ e₃ = s ∩ e₃ := by
    ext v
    have ha : v ∈ e₁ ∩ e₃ → v ∈ s ∩ e₃ := fun h =>
      Finset.mem_inter.mpr ⟨h₁₃ h, (Finset.mem_inter.mp h).2⟩
    have hb : v ∈ e₂ ∩ e₃ → v ∈ s ∩ e₃ := fun h =>
      Finset.mem_inter.mpr ⟨h₂₃ h, (Finset.mem_inter.mp h).2⟩
    simp only [Finset.mem_union, Finset.mem_inter] at ha hb ⊢
    tauto
  have hover₃ : restrictLaw ρ₂ ((s ∪ e₁ ∪ e₂) ∩ e₃) =
      restrictLaw μ₃ ((s ∪ e₁ ∪ e₂) ∩ e₃) := by
    rw [hc]
    exact (restrictLaw_of_subset hρ₂s (Finset.inter_subset_left.trans Finset.subset_union_left)).trans
      ((restrictLaw_of_subset hρ₁s Finset.inter_subset_left).trans h₃)
  obtain ⟨ρ₃, hρ₃s, hρ₃e⟩ := glue_on_sets ρ₂ μ₃ (s ∪ e₁ ∪ e₂) e₃ hover₃
  refine ⟨ρ₃, ?_, ?_, hρ₃e⟩
  · exact (restrictLaw_of_subset hρ₃s
      (Finset.subset_union_right.trans Finset.subset_union_left)).trans
      ((restrictLaw_of_subset hρ₂s Finset.subset_union_right).trans hρ₁e)
  · exact (restrictLaw_of_subset hρ₃s Finset.subset_union_right).trans hρ₂e

end AlphaCycle
