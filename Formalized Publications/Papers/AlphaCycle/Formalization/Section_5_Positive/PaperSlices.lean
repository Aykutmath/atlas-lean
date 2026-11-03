import Section_5_Positive.Positive

/-! Additional exact statements about the explicit slices: necessity of the
eight displayed cells, zero slices, and Fréchet bounds before imposing triangles. -/
namespace AlphaCycle.Slice

/-- All eight cells are forced by the pair marginals and the chosen `111` mass. -/
theorem atom_reconstruction (s : Moments) (q : Bool → Bool → Bool → ℝ)
    (hab : ∀ i j, (∑ k : Bool, q i j k) = pairAtom s.mass s.a s.b s.ab i j)
    (hac : ∀ i k, (∑ j : Bool, q i j k) = pairAtom s.mass s.a s.c s.ac i k)
    (hbc : ∀ j k, (∑ i : Bool, q i j k) = pairAtom s.mass s.b s.c s.bc j k) :
    ∀ i j k, q i j k = atom s (q true true true) i j k := by
  have e₁ := hab true true
  have e₂ := hac true true
  have e₃ := hbc true true
  have e₄ := hab true false
  have e₅ := hab false true
  have e₆ := hac false true
  have e₇ := hab false false
  simp only [Fintype.sum_bool, pairAtom] at e₁ e₂ e₃ e₄ e₅ e₆ e₇
  intro i j k
  cases i <;> cases j <;> cases k <;> simp only [atom] <;> linarith

theorem pairBounds_zero_mass {p q pq : ℝ} (h : PairBounds 0 p q pq) :
    p = 0 ∧ q = 0 ∧ pq = 0 := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  constructor
  · linarith
  constructor <;> linarith

/-- A zero-mass slice has no nonzero first or second moments. -/
theorem zero_mass_moments (s : Moments) (hm : s.mass = 0)
    (hab : PairBounds s.mass s.a s.b s.ab)
    (hac : PairBounds s.mass s.a s.c s.ac)
    (hbc : PairBounds s.mass s.b s.c s.bc) :
    s.a = 0 ∧ s.b = 0 ∧ s.c = 0 ∧ s.ab = 0 ∧ s.ac = 0 ∧ s.bc = 0 := by
  rw [hm] at hab hac hbc
  obtain ⟨ha, hb, hab⟩ := pairBounds_zero_mass hab
  obtain ⟨_, hc, hac⟩ := pairBounds_zero_mass hac
  obtain ⟨_, _, hbc⟩ := pairBounds_zero_mass hbc
  exact ⟨ha, hb, hc, hab, hac, hbc⟩

theorem zero_mass_extension (s : Moments) (h : Conditions s) (hm : s.mass = 0) :
    IsExtension s (fun _ _ _ => 0) := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ :=
    zero_mass_moments s hm h.pair_ab h.pair_ac h.pair_bc
  simp [IsExtension, hm, ha, hb, hc, hab, hac, hbc, pairAtom,
    Bool.forall_bool]

/-- The endpoint comparison in the paper is the sixteen individual comparisons. -/
theorem each_lower_le_each_upper (s : Moments) (h : Conditions s) :
    ∀ l ∈ ({0, s.ab + s.ac - s.a, s.ab + s.bc - s.b,
      s.ac + s.bc - s.c} : Finset ℝ),
    ∀ u ∈ ({s.ab, s.ac, s.bc,
      s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc} : Finset ℝ), l ≤ u := by
  classical
  intro l hl u hu
  have hlo : l ≤ lower s := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> simp [lower]
  have hup : upper s ≤ u := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp [upper]
  exact hlo.trans ((interval_nonempty s h).trans hup)

/-- The displayed cancellation comparing the `a` lower bound to the last upper bound. -/
theorem upperFinal_sub_lowerA (s : Moments) :
    (s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc) -
      (s.ab + s.ac - s.a) = s.mass - s.b - s.c + s.bc := by ring

theorem upperFinal_sub_lowerB (s : Moments) :
    (s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc) -
      (s.ab + s.bc - s.b) = s.mass - s.a - s.c + s.ac := by ring

theorem upperFinal_sub_lowerC (s : Moments) :
    (s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc) -
      (s.ac + s.bc - s.c) = s.mass - s.a - s.b + s.ab := by ring

end AlphaCycle.Slice

namespace AlphaCycle.Positive
variable {T : Type*} [Fintype T]

/-- Overlap consistency determines the same common-slice mass from every pair. -/
theorem common_slice_masses (p : LocalTables T) (t : T) :
    (∑ i : Bool, ∑ k : Bool, p.ac t i k) = (moments p t).mass ∧
    (∑ j : Bool, ∑ k : Bool, p.bc t j k) = (moments p t).mass := by
  constructor
  · exact Finset.sum_congr rfl (fun i _ => (p.consistent_a t i).symm)
  · calc
      _ = ∑ j : Bool, ∑ i : Bool, p.ab t i j :=
        Finset.sum_congr rfl (fun j _ => (p.consistent_b t j).symm)
      _ = _ := Finset.sum_comm

/-- Pairwise Fréchet inequalities require only the local laws and consistency. -/
theorem slice_frechet (p : LocalTables T) (t : T) :
    let s := moments p t
    Slice.PairBounds s.mass s.a s.b s.ab ∧
    Slice.PairBounds s.mass s.a s.c s.ac ∧
    Slice.PairBounds s.mass s.b s.c s.bc := by
  refine ⟨Slice.pairBounds_of_nonnegative (p.ab t) (p.ab_nonneg t), ?_, ?_⟩
  · have hp := Slice.pairBounds_of_nonnegative (p.ac t) (p.ac_nonneg t)
    rw [(common_slice_masses p t).1, ← p.consistent_a t true] at hp
    exact hp
  · have hp := Slice.pairBounds_of_nonnegative (p.bc t) (p.bc_nonneg t)
    rw [(common_slice_masses p t).2, ← p.consistent_b t true,
      ← p.consistent_c t true] at hp
    exact hp

/-- The paper allows any triple mass in each feasible interval. -/
def jointWithMass (p : LocalTables T) (r : T → ℝ) (t : T) : Bool → Bool → Bool → ℝ :=
  Slice.atom (moments p t) (r t)

/-- Gluing arbitrary feasible slice choices gives total mass one and exactly
the prescribed three pair tables. -/
theorem jointWithMass_valid (p : LocalTables T) (r : T → ℝ)
    (hr : ∀ t, Slice.lower (moments p t) ≤ r t ∧ r t ≤ Slice.upper (moments p t)) :
    (∀ t i j k, 0 ≤ jointWithMass p r t i j k) ∧
    (∑ t : T, ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, jointWithMass p r t i j k) = 1 ∧
    (∀ t i j, (∑ k : Bool, jointWithMass p r t i j k) = p.ab t i j) ∧
    (∀ t i k, (∑ j : Bool, jointWithMass p r t i j k) = p.ac t i k) ∧
    (∀ t j k, (∑ i : Bool, jointWithMass p r t i j k) = p.bc t j k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (Slice.atom_nonnegative_iff _ _).mpr (hr t)
  · simp only [jointWithMass, Slice.atom_mass]
    exact p.total
  · intro t i j
    rw [jointWithMass, Slice.atom_marginal_ab, pair_ab]
  · intro t i k
    rw [jointWithMass, Slice.atom_marginal_ac, pair_ac]
  · intro t j k
    rw [jointWithMass, Slice.atom_marginal_bc, pair_bc]

end AlphaCycle.Positive
