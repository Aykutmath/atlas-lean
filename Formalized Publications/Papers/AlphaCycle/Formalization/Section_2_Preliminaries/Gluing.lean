import Section_2_Preliminaries.FiniteLaw

/-! Gluing finite laws over a common marginal.  Zero-mass fibers are handled
without choosing a conditional law. -/
noncomputable section
open scoped BigOperators
open Classical

namespace AlphaCycle.Law

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A zero marginal cell forces every cell above it to have zero mass. -/
theorem mass_eq_zero_of_map_mass_eq_zero (μ : Law α) (f : α → γ) (a : α)
    (h : (μ.map f).mass (f a) = 0) : μ.mass a = 0 := by
  exact (μ.prob_eq_zero_iff (fun a' => f a' = f a)).mp h a rfl

/-- The finite conditional-product construction over a shared image. -/
def glueMass (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (a : α) (b : β) : ℝ :=
  if f a = g b then μ.mass a * ν.mass b / (μ.map f).mass (f a) else 0

theorem glueMass_nonneg (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (a : α) (b : β) : 0 ≤ glueMass μ ν f g a b := by
  unfold glueMass
  split_ifs
  · exact div_nonneg (mul_nonneg (μ.nonneg a) (ν.nonneg b)) ((μ.map f).nonneg _)
  · exact le_rfl

theorem glueMass_left (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) (a : α) :
    (∑ b, glueMass μ ν f g a b) = μ.mass a := by
  classical
  have hf : (∑ b, if g b = f a then ν.mass b else 0) = (μ.map f).mass (f a) := by
    rw [h]; rfl
  calc
    (∑ b, glueMass μ ν f g a b) =
        μ.mass a / (μ.map f).mass (f a) * (∑ b, if g b = f a then ν.mass b else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases he : f a = g b
      · simp only [glueMass, if_pos he, if_pos he.symm]; ring
      · simp [glueMass, he, Ne.symm he]
    _ = μ.mass a / (μ.map f).mass (f a) * (μ.map f).mass (f a) := by rw [hf]
    _ = μ.mass a := by
      by_cases hz : (μ.map f).mass (f a) = 0
      · simp [hz, mass_eq_zero_of_map_mass_eq_zero μ f a hz]
      · exact div_mul_cancel₀ _ hz

theorem glueMass_right (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) (b : β) :
    (∑ a, glueMass μ ν f g a b) = ν.mass b := by
  classical
  have swap : ∀ a, glueMass μ ν f g a b = glueMass ν μ g f b a := by
    intro a
    by_cases he : f a = g b
    · simp only [glueMass, if_pos he, if_pos he.symm, h, he, mul_comm]
    · simp [glueMass, he, Ne.symm he]
  simp only [swap]
  exact glueMass_left ν μ g f h.symm b

/-- Gluing preserves both full laws, not merely selected moments. -/
def glue (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) : Law (α × β) where
  mass ab := glueMass μ ν f g ab.1 ab.2
  nonneg ab := glueMass_nonneg μ ν f g ab.1 ab.2
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [glueMass_left μ ν f g h]
    exact μ.total

theorem glue_left (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) : (glue μ ν f g h).map Prod.fst = μ := by
  classical
  ext a
  simp only [map, glue, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [glueMass_left μ ν f g h]

theorem glue_right (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) : (glue μ ν f g h).map Prod.snd = ν := by
  classical
  ext b
  simp only [map, glue, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact glueMass_right μ ν f g h b

/-- The two copies of the common variables agree on every positive-mass cell. -/
theorem glue_support (μ : Law α) (ν : Law β) (f : α → γ) (g : β → γ)
    (h : μ.map f = ν.map g) (a : α) (b : β)
    (hab : (glue μ ν f g h).mass (a, b) ≠ 0) : f a = g b := by
  by_contra hn
  exact hab (by simp [glue, glueMass, hn])

/-- Pushforwards only depend on the values of a function on the support. -/
theorem map_congr_support (μ : Law α) (f g : α → β)
    (h : ∀ a, μ.mass a ≠ 0 → f a = g a) : μ.map f = μ.map g := by
  classical
  ext b
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : μ.mass a = 0
  · simp [hz]
  · rw [h a hz]

/-- Restore a private block using its conditional law given an observed core. -/
def attach {D : Type*} [Fintype D] (μ : Law α) (ν : Law (β × D))
    (f : α → β) (h : μ.map f = ν.map Prod.fst) : Law (α × D) :=
  (glue μ ν f Prod.fst h).map (fun x => (x.1, x.2.2))

theorem attach_core {D : Type*} [Fintype D] (μ : Law α) (ν : Law (β × D))
    (f : α → β) (h : μ.map f = ν.map Prod.fst) :
    (attach μ ν f h).map Prod.fst = μ := by
  simpa only [attach, map_map, Function.comp_def] using glue_left μ ν f Prod.fst h

theorem attach_edge {D : Type*} [Fintype D] (μ : Law α) (ν : Law (β × D))
    (f : α → β) (h : μ.map f = ν.map Prod.fst) :
    (attach μ ν f h).map (fun x => (f x.1, x.2)) = ν := by
  rw [attach, map_map]
  calc
    _ = (glue μ ν f Prod.fst h).map Prod.snd := by
      apply map_congr_support
      intro x hx
      exact Prod.ext (glue_support μ ν f Prod.fst h x.1 x.2 hx) rfl
    _ = ν := glue_right μ ν f Prod.fst h

/-- Attaching a private block preserves every other core marginal. -/
theorem attach_preserves {D : Type*} [Fintype D] (μ : Law α) (ν : Law (β × D))
    (f : α → β) (h : μ.map f = ν.map Prod.fst) (g : α → γ) :
    (attach μ ν f h).map (fun x => g x.1) = μ.map g := by
  simpa only [map_map, Function.comp_def] using congrArg (map g) (attach_core μ ν f h)

end AlphaCycle.Law
