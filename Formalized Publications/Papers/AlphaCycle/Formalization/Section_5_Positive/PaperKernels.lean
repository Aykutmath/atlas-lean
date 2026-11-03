import Section_2_Preliminaries.Gluing

/-! Explicit conditional kernels and independent sampling of the three private
blocks, including arbitrary normalized fallback laws on zero-mass states. -/
noncomputable section
namespace AlphaCycle.Law
open Classical

variable {Ω B D D₁ D₂ D₃ : Type*}
  [Fintype Ω] [Fintype B] [Fintype D] [Fintype D₁] [Fintype D₂] [Fintype D₃]

/-- The marginal mass of a core state is the sum over its private states. -/
theorem fst_mass_eq_sum (ν : Law (B × D)) (b : B) :
    (ν.map Prod.fst).mass b = ∑ d, ν.mass (b, d) := by
  classical
  simp only [map_mass, prob, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb
    simp [hb]
  · simp

/-- Conditional private law given a core state. The chosen fallback law is used
exactly on zero-probability core states. -/
def conditionalKernel (ν : Law (B × D)) (fallback : Law D) (b : B) : Law D where
  mass d := if (ν.map Prod.fst).mass b = 0 then fallback.mass d
    else ν.mass (b, d) / (ν.map Prod.fst).mass b
  nonneg d := by
    split_ifs
    · exact fallback.nonneg d
    · exact div_nonneg (ν.nonneg _) ((ν.map Prod.fst).nonneg b)
  total := by
    classical
    by_cases hz : (ν.map Prod.fst).mass b = 0
    · simp only [hz, ↓reduceIte, fallback.total]
    · simp only [hz, ↓reduceIte, ← Finset.sum_div, ← fst_mass_eq_sum, div_self hz]

/-- Each conditional law is normalized, including a zero-mass conditioning state. -/
theorem conditionalKernel_total (ν : Law (B × D)) (fallback : Law D) (b : B) :
    (∑ d, (conditionalKernel ν fallback b).mass d) = 1 :=
  (conditionalKernel ν fallback b).total

/-- Any prescribed fallback can be chosen on an event of probability zero. -/
theorem conditionalKernel_of_zero (ν : Law (B × D)) (fallback : Law D) (b : B)
    (hz : (ν.map Prod.fst).mass b = 0) :
    conditionalKernel ν fallback b = fallback := by
  ext d
  simp only [conditionalKernel, hz, ↓reduceIte]

/-- On positive-probability states the kernel is the usual conditional ratio. -/
theorem conditionalKernel_of_nonzero (ν : Law (B × D)) (fallback : Law D) (b : B)
    (hz : (ν.map Prod.fst).mass b ≠ 0) (d : D) :
    (conditionalKernel ν fallback b).mass d =
      ν.mass (b, d) / (ν.map Prod.fst).mass b := by
  simp only [conditionalKernel, hz, ↓reduceIte]

/-- Multiplying a conditional law by its core marginal exactly reconstructs the
local joint law, regardless of fallback choices. -/
theorem conditionalKernel_reconstruct (ν : Law (B × D)) (fallback : Law D)
    (b : B) (d : D) :
    (ν.map Prod.fst).mass b * (conditionalKernel ν fallback b).mass d = ν.mass (b, d) := by
  by_cases hz : (ν.map Prod.fst).mass b = 0
  · have hcell := mass_eq_zero_of_map_mass_eq_zero ν Prod.fst (b, d) hz
    simp only [hz, hcell, zero_mul]
  · rw [conditionalKernel_of_nonzero ν fallback b hz]
    exact mul_div_cancel₀ _ hz

/-- Sample the core, then sample three private blocks independently conditional
on that core. The factorization is literal in the law's atom formula. -/
def kernelProduct (μ : Law Ω) (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) :
    Law (Ω × D₁ × D₂ × D₃) where
  mass x := μ.mass x.1 * (κ₁ x.1).mass x.2.1 *
    (κ₂ x.1).mass x.2.2.1 * (κ₃ x.1).mass x.2.2.2
  nonneg x := mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg _)
    ((κ₁ _).nonneg _)) ((κ₂ _).nonneg _)) ((κ₃ _).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Law.total, mul_one]

/-- Summing the product law over all private blocks recovers its core mass. -/
theorem kernelProduct_core_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) (ω : Ω) :
    (∑ d₁, ∑ d₂, ∑ d₃, (kernelProduct μ κ₁ κ₂ κ₃).mass (ω, d₁, d₂, d₃)) = μ.mass ω := by
  simp only [kernelProduct, ← Finset.mul_sum, Law.total, mul_one]

/-- The first core-private marginal retains exactly its prescribed kernel. -/
theorem kernelProduct_first_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) (ω : Ω) (d₁ : D₁) :
    (∑ d₂, ∑ d₃, (kernelProduct μ κ₁ κ₂ κ₃).mass (ω, d₁, d₂, d₃)) =
      μ.mass ω * (κ₁ ω).mass d₁ := by
  simp only [kernelProduct, ← Finset.mul_sum, Law.total, mul_one]

/-- The second core-private marginal retains exactly its prescribed kernel. -/
theorem kernelProduct_second_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) (ω : Ω) (d₂ : D₂) :
    (∑ d₁, ∑ d₃, (kernelProduct μ κ₁ κ₂ κ₃).mass (ω, d₁, d₂, d₃)) =
      μ.mass ω * (κ₂ ω).mass d₂ := by
  simp only [kernelProduct, ← Finset.mul_sum, Law.total, mul_one]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Law.total, mul_one]

/-- The third core-private marginal retains exactly its prescribed kernel. -/
theorem kernelProduct_third_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) (ω : Ω) (d₃ : D₃) :
    (∑ d₁, ∑ d₂, (kernelProduct μ κ₁ κ₂ κ₃).mass (ω, d₁, d₂, d₃)) =
      μ.mass ω * (κ₃ ω).mass d₃ := by
  simp only [kernelProduct, ← Finset.sum_mul, ← Finset.mul_sum, Law.total, mul_one]

/-- The core marginal of the independent conditional product is the sampled law. -/
theorem kernelProduct_core (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃) :
    (kernelProduct μ κ₁ κ₂ κ₃).map Prod.fst = μ := by
  classical
  ext ω
  simp only [map_mass, prob, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ω]
  · simp only [↓reduceIte]
    exact kernelProduct_core_mass μ κ₁ κ₂ κ₃ ω
  · intro ω' _ hω
    simp [hω]
  · simp

/-- Marginal formula after observing a function of the core and the first private block. -/
theorem kernelProduct_project_first_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃)
    (f : Ω → B) (b : B) (d : D₁) :
    ((kernelProduct μ κ₁ κ₂ κ₃).map (fun x => (f x.1, x.2.1))).mass (b, d) =
      ∑ ω, if f ω = b then μ.mass ω * (κ₁ ω).mass d else 0 := by
  classical
  simp only [map_mass, prob, Fintype.sum_prod_type, Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : f ω = b
  · simp only [hb, true_and, ↓reduceIte]
    rw [Finset.sum_eq_single d]
    · simp only [↓reduceIte]
      exact kernelProduct_first_mass μ κ₁ κ₂ κ₃ ω d
    · intro d' _ hd
      simp [hd]
    · simp
  · simp [hb]

/-- Marginal formula after observing a function of the core and the second private block. -/
theorem kernelProduct_project_second_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃)
    (f : Ω → B) (b : B) (d : D₂) :
    ((kernelProduct μ κ₁ κ₂ κ₃).map (fun x => (f x.1, x.2.2.1))).mass (b, d) =
      ∑ ω, if f ω = b then μ.mass ω * (κ₂ ω).mass d else 0 := by
  classical
  simp only [map_mass, prob, Fintype.sum_prod_type, Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : f ω = b
  · simp only [hb, true_and, ↓reduceIte]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single d]
    · simp only [↓reduceIte]
      exact kernelProduct_second_mass μ κ₁ κ₂ κ₃ ω d
    · intro d' _ hd
      simp [hd]
    · simp
  · simp [hb]

/-- Marginal formula after observing a function of the core and the third private block. -/
theorem kernelProduct_project_third_mass (μ : Law Ω)
    (κ₁ : Ω → Law D₁) (κ₂ : Ω → Law D₂) (κ₃ : Ω → Law D₃)
    (f : Ω → B) (b : B) (d : D₃) :
    ((kernelProduct μ κ₁ κ₂ κ₃).map (fun x => (f x.1, x.2.2.2))).mass (b, d) =
      ∑ ω, if f ω = b then μ.mass ω * (κ₃ ω).mass d else 0 := by
  classical
  simp only [map_mass, prob, Fintype.sum_prod_type, Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : f ω = b
  · simp only [hb, true_and, ↓reduceIte]
    calc
      _ = ∑ d₁, ∑ d₂, (kernelProduct μ κ₁ κ₂ κ₃).mass (ω, d₁, d₂, d) := by
        apply Finset.sum_congr rfl
        intro d₁ _
        apply Finset.sum_congr rfl
        intro d₂ _
        simp
      _ = _ := kernelProduct_third_mass μ κ₁ κ₂ κ₃ ω d
  · simp [hb]

/-- Sampling any core with the correct observed marginal and then its local
conditional kernel reconstructs the local joint distribution. -/
theorem conditionalKernel_pushforward (μ : Law Ω) (ν : Law (B × D))
    (f : Ω → B) (h : μ.map f = ν.map Prod.fst) (fallback : Law D)
    (b : B) (d : D) :
    (∑ ω, if f ω = b then μ.mass ω * (conditionalKernel ν fallback (f ω)).mass d else 0) =
      ν.mass (b, d) := by
  classical
  calc
    _ = (∑ ω, if f ω = b then μ.mass ω else 0) *
        (conditionalKernel ν fallback b).mass d := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hb : f ω = b <;> simp [hb]
    _ = (ν.map Prod.fst).mass b * (conditionalKernel ν fallback b).mass d := by
      change (μ.map f).mass b * _ = _
      rw [h]
    _ = _ := conditionalKernel_reconstruct ν fallback b d

variable {B₁ B₂ B₃ : Type*} [Fintype B₁] [Fintype B₂] [Fintype B₃]

/-- The paper's private-block construction: sample the common global core law
and use the three local conditional kernels, independently given that core. -/
def restorePrivateWithKernels (μ : Law Ω)
    (ν₁ : Law (B₁ × D₁)) (ν₂ : Law (B₂ × D₂)) (ν₃ : Law (B₃ × D₃))
    (f₁ : Ω → B₁) (f₂ : Ω → B₂) (f₃ : Ω → B₃)
    (fallback₁ : Law D₁) (fallback₂ : Law D₂) (fallback₃ : Law D₃) :
    Law (Ω × D₁ × D₂ × D₃) :=
  kernelProduct μ (fun ω => conditionalKernel ν₁ fallback₁ (f₁ ω))
    (fun ω => conditionalKernel ν₂ fallback₂ (f₂ ω))
    (fun ω => conditionalKernel ν₃ fallback₃ (f₃ ω))

/-- The independent conditional construction preserves the entire core law and
each specified edge law. All three arbitrary zero-state fallback choices are
allowed, and the conclusion has no positivity assumption on core atoms. -/
theorem restorePrivateWithKernels_marginals (μ : Law Ω)
    (ν₁ : Law (B₁ × D₁)) (ν₂ : Law (B₂ × D₂)) (ν₃ : Law (B₃ × D₃))
    (f₁ : Ω → B₁) (f₂ : Ω → B₂) (f₃ : Ω → B₃)
    (h₁ : μ.map f₁ = ν₁.map Prod.fst) (h₂ : μ.map f₂ = ν₂.map Prod.fst)
    (h₃ : μ.map f₃ = ν₃.map Prod.fst)
    (fallback₁ : Law D₁) (fallback₂ : Law D₂) (fallback₃ : Law D₃) :
    let ρ := restorePrivateWithKernels μ ν₁ ν₂ ν₃ f₁ f₂ f₃ fallback₁ fallback₂ fallback₃
    ρ.map Prod.fst = μ ∧
    ρ.map (fun x => (f₁ x.1, x.2.1)) = ν₁ ∧
    ρ.map (fun x => (f₂ x.1, x.2.2.1)) = ν₂ ∧
    ρ.map (fun x => (f₃ x.1, x.2.2.2)) = ν₃ := by
  dsimp only [restorePrivateWithKernels]
  refine ⟨kernelProduct_core μ _ _ _, ?_, ?_, ?_⟩
  · ext x
    rcases x with ⟨b, d⟩
    rw [kernelProduct_project_first_mass]
    exact conditionalKernel_pushforward μ ν₁ f₁ h₁ fallback₁ b d
  · ext x
    rcases x with ⟨b, d⟩
    rw [kernelProduct_project_second_mass]
    exact conditionalKernel_pushforward μ ν₂ f₂ h₂ fallback₂ b d
  · ext x
    rcases x with ⟨b, d⟩
    rw [kernelProduct_project_third_mass]
    exact conditionalKernel_pushforward μ ν₃ f₃ h₃ fallback₃ b d

end AlphaCycle.Law
