import Section_2_Preliminaries.Gluing

/-! Simultaneous restoration of the three disjoint private blocks. -/
noncomputable section
namespace AlphaCycle

/-- Any core realization extends to all three prescribed private-block laws.
The product order is only bookkeeping: the state is `(((core,d₁),d₂),d₃)`. -/
theorem restore_private_blocks
    {K E₁ E₂ E₃ D₁ D₂ D₃ : Type*}
    [Fintype K] [Fintype E₁] [Fintype E₂] [Fintype E₃]
    [Fintype D₁] [Fintype D₂] [Fintype D₃]
    (μ : Law K) (ν₁ : Law (E₁ × D₁)) (ν₂ : Law (E₂ × D₂)) (ν₃ : Law (E₃ × D₃))
    (f₁ : K → E₁) (f₂ : K → E₂) (f₃ : K → E₃)
    (h₁ : μ.map f₁ = ν₁.map Prod.fst)
    (h₂ : μ.map f₂ = ν₂.map Prod.fst)
    (h₃ : μ.map f₃ = ν₃.map Prod.fst) :
    ∃ glued : Law (((K × D₁) × D₂) × D₃),
      glued.map (fun x => x.1.1.1) = μ ∧
      glued.map (fun x => (f₁ x.1.1.1, x.1.1.2)) = ν₁ ∧
      glued.map (fun x => (f₂ x.1.1.1, x.1.2)) = ν₂ ∧
      glued.map (fun x => (f₃ x.1.1.1, x.2)) = ν₃ := by
  let μ₁ := μ.attach ν₁ f₁ h₁
  have h₂' : μ₁.map (fun x => f₂ x.1) = ν₂.map Prod.fst :=
    (Law.attach_preserves μ ν₁ f₁ h₁ f₂).trans h₂
  let μ₂ := μ₁.attach ν₂ (fun x => f₂ x.1) h₂'
  have h₃' : μ₂.map (fun x => f₃ x.1.1) = ν₃.map Prod.fst := by
    exact (Law.attach_preserves μ₁ ν₂ (fun x => f₂ x.1) h₂'
      (fun x => f₃ x.1)).trans ((Law.attach_preserves μ ν₁ f₁ h₁ f₃).trans h₃)
  let μ₃ := μ₂.attach ν₃ (fun x => f₃ x.1.1) h₃'
  refine ⟨μ₃, ?_, ?_, ?_, ?_⟩
  · exact (Law.attach_preserves μ₂ ν₃ (fun x => f₃ x.1.1) h₃'
      (fun x => x.1.1)).trans
      ((Law.attach_preserves μ₁ ν₂ (fun x => f₂ x.1) h₂' Prod.fst).trans
        (Law.attach_core μ ν₁ f₁ h₁))
  · exact (Law.attach_preserves μ₂ ν₃ (fun x => f₃ x.1.1) h₃'
      (fun x => (f₁ x.1.1, x.1.2))).trans
      ((Law.attach_preserves μ₁ ν₂ (fun x => f₂ x.1) h₂'
        (fun x => (f₁ x.1, x.2))).trans (Law.attach_edge μ ν₁ f₁ h₁))
  · exact (Law.attach_preserves μ₂ ν₃ (fun x => f₃ x.1.1) h₃'
      (fun x => (f₂ x.1.1, x.2))).trans
      (Law.attach_edge μ₁ ν₂ (fun x => f₂ x.1) h₂')
  · exact Law.attach_edge μ₂ ν₃ (fun x => f₃ x.1.1) h₃'

end AlphaCycle
