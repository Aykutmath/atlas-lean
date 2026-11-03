import Section_5_Positive.PositiveSlice
import Section_2_Preliminaries.Core

/-!
# Gluing three singleton pair-only blocks over an arbitrary common block

The state type `T` represents all Boolean assignments to the common vertex
block.  Working directly with finite state types avoids any restriction on
its cardinality.  Pair consistency is imposed separately in every `T` slice.
-/

namespace AlphaCycle.Positive

open scoped BigOperators

variable {T : Type*} [Fintype T]

/-- Three consistent local tables on `T × {a,b}`, `T × {a,c}`, and `T × {b,c}`. -/
structure LocalTables (T : Type*) [Fintype T] where
  ab : T → Bool → Bool → ℝ
  ac : T → Bool → Bool → ℝ
  bc : T → Bool → Bool → ℝ
  ab_nonneg : ∀ t i j, 0 ≤ ab t i j
  ac_nonneg : ∀ t i k, 0 ≤ ac t i k
  bc_nonneg : ∀ t j k, 0 ≤ bc t j k
  consistent_a : ∀ t i, (∑ j : Bool, ab t i j) = ∑ k : Bool, ac t i k
  consistent_b : ∀ t j, (∑ i : Bool, ab t i j) = ∑ k : Bool, bc t j k
  consistent_c : ∀ t k, (∑ i : Bool, ac t i k) = ∑ j : Bool, bc t j k
  total : (∑ t : T, ∑ i : Bool, ∑ j : Bool, ab t i j) = 1

/-- Seven unnormalized moments in a common-block slice. -/
def moments (p : LocalTables T) (t : T) : Slice.Moments where
  mass := ∑ i : Bool, ∑ j : Bool, p.ab t i j
  a := ∑ j : Bool, p.ab t true j
  b := ∑ i : Bool, p.ab t i true
  c := ∑ i : Bool, p.ac t i true
  ab := p.ab t true true
  ac := p.ac t true true
  bc := p.bc t true true

/-- The four generalized triangle inequalities, conditioned on every common state. -/
def TriangleConditions (p : LocalTables T) : Prop := ∀ t,
  let s := moments p t
  s.ab + s.ac ≤ s.a + s.bc ∧
  s.ab + s.bc ≤ s.b + s.ac ∧
  s.ac + s.bc ≤ s.c + s.ab ∧
  s.a + s.b + s.c ≤ s.mass + s.ab + s.ac + s.bc

private theorem mass_ac (p : LocalTables T) (t : T) :
    (∑ i : Bool, ∑ k : Bool, p.ac t i k) = (moments p t).mass := by
  exact Finset.sum_congr rfl (fun i _ => (p.consistent_a t i).symm)

private theorem mass_bc (p : LocalTables T) (t : T) :
    (∑ j : Bool, ∑ k : Bool, p.bc t j k) = (moments p t).mass := by
  calc
    _ = ∑ j : Bool, ∑ i : Bool, p.ab t i j :=
      Finset.sum_congr rfl (fun j _ => (p.consistent_b t j).symm)
    _ = _ := Finset.sum_comm

/-- Each locally consistent family supplies the three pairwise Fréchet conditions. -/
theorem slice_conditions (p : LocalTables T) (h : TriangleConditions p) (t : T) :
    Slice.Conditions (moments p t) := by
  rcases h t with ⟨ha, hb, hc, hs⟩
  refine ⟨Slice.pairBounds_of_nonnegative (p.ab t) (p.ab_nonneg t), ?_, ?_, ha, hb, hc, hs⟩
  · have hp := Slice.pairBounds_of_nonnegative (p.ac t) (p.ac_nonneg t)
    rw [mass_ac p t, ← p.consistent_a t true] at hp
    exact hp
  · have hp := Slice.pairBounds_of_nonnegative (p.bc t) (p.bc_nonneg t)
    rw [mass_bc p t, ← p.consistent_b t true, ← p.consistent_c t true] at hp
    exact hp

/-- The `ab` slice table is reconstructed from its moments. -/
theorem pair_ab (p : LocalTables T) (t : T) (i j : Bool) :
    Slice.pairAtom (moments p t).mass (moments p t).a
      (moments p t).b (moments p t).ab i j = p.ab t i j := by
  exact (Slice.pairAtom_reconstruction (p.ab t) _ _ _ _ rfl rfl rfl rfl i j).symm

/-- The `ac` slice table is reconstructed from its moments. -/
theorem pair_ac (p : LocalTables T) (t : T) (i k : Bool) :
    Slice.pairAtom (moments p t).mass (moments p t).a
      (moments p t).c (moments p t).ac i k = p.ac t i k := by
  exact (Slice.pairAtom_reconstruction (p.ac t) _ _ _ _ (mass_ac p t)
    (p.consistent_a t true).symm rfl rfl i k).symm

/-- The `bc` slice table is reconstructed from its moments. -/
theorem pair_bc (p : LocalTables T) (t : T) (j k : Bool) :
    Slice.pairAtom (moments p t).mass (moments p t).b
      (moments p t).c (moments p t).bc j k = p.bc t j k := by
  exact (Slice.pairAtom_reconstruction (p.bc t) _ _ _ _ (mass_bc p t)
    (p.consistent_b t true).symm (p.consistent_c t true).symm rfl j k).symm

/-- An explicit global joint table, using the lower endpoint in each slice. -/
def joint (p : LocalTables T) (t : T) : Bool → Bool → Bool → ℝ :=
  Slice.atom (moments p t) (Slice.lower (moments p t))

theorem joint_nonneg (p : LocalTables T) (h : TriangleConditions p) :
    ∀ t i j k, 0 ≤ joint p t i j k := by
  intro t
  exact (Slice.atom_nonnegative_iff _ _).2
    ⟨le_rfl, Slice.interval_nonempty _ (slice_conditions p h t)⟩

theorem joint_total (p : LocalTables T) :
    (∑ t : T, ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, joint p t i j k) = 1 := by
  simp_rw [joint, Slice.atom_mass]
  exact p.total

theorem joint_ab (p : LocalTables T) (t : T) (i j : Bool) :
    (∑ k : Bool, joint p t i j k) = p.ab t i j := by
  rw [joint, Slice.atom_marginal_ab, pair_ab]

theorem joint_ac (p : LocalTables T) (t : T) (i k : Bool) :
    (∑ j : Bool, joint p t i j k) = p.ac t i k := by
  rw [joint, Slice.atom_marginal_ac, pair_ac]

theorem joint_bc (p : LocalTables T) (t : T) (j k : Bool) :
    (∑ i : Bool, joint p t i j k) = p.bc t j k := by
  rw [joint, Slice.atom_marginal_bc, pair_bc]

/-- Slice gluing yields a normalized global law with all three prescribed marginals. -/
theorem extension (p : LocalTables T) (h : TriangleConditions p) :
    ∃ q : T → Bool → Bool → Bool → ℝ,
      (∀ t i j k, 0 ≤ q t i j k) ∧
      (∑ t : T, ∑ i : Bool, ∑ j : Bool, ∑ k : Bool, q t i j k) = 1 ∧
      (∀ t i j, (∑ k : Bool, q t i j k) = p.ab t i j) ∧
      (∀ t i k, (∑ j : Bool, q t i j k) = p.ac t i k) ∧
      (∀ t j k, (∑ i : Bool, q t i j k) = p.bc t j k) := by
  exact ⟨joint p, joint_nonneg p h, joint_total p, joint_ab p, joint_ac p, joint_bc p⟩

/-- The global probability law furnished by the explicit slice construction. -/
def jointLaw (p : LocalTables T) (h : TriangleConditions p) :
    Law (T × Bool × Bool × Bool) where
  mass x := joint p x.1 x.2.1 x.2.2.1 x.2.2.2
  nonneg x := joint_nonneg p h x.1 x.2.1 x.2.2.1 x.2.2.2
  total := by simpa only [Fintype.sum_prod_type] using joint_total p

/-- The first prescribed local probability law. -/
def abLaw (p : LocalTables T) : Law (T × Bool × Bool) where
  mass x := p.ab x.1 x.2.1 x.2.2
  nonneg x := p.ab_nonneg x.1 x.2.1 x.2.2
  total := by simpa only [Fintype.sum_prod_type] using p.total

/-- The second prescribed local probability law. -/
def acLaw (p : LocalTables T) : Law (T × Bool × Bool) where
  mass x := p.ac x.1 x.2.1 x.2.2
  nonneg x := p.ac_nonneg x.1 x.2.1 x.2.2
  total := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ t : T, (moments p t).mass := Finset.sum_congr rfl (fun t _ => mass_ac p t)
      _ = 1 := p.total

/-- The third prescribed local probability law. -/
def bcLaw (p : LocalTables T) : Law (T × Bool × Bool) where
  mass x := p.bc x.1 x.2.1 x.2.2
  nonneg x := p.bc_nonneg x.1 x.2.1 x.2.2
  total := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ t : T, (moments p t).mass := Finset.sum_congr rfl (fun t _ => mass_bc p t)
      _ = 1 := p.total

/-- The global law has exactly the given `ab` marginal. -/
theorem jointLaw_ab (p : LocalTables T) (h : TriangleConditions p) :
    (jointLaw p h).map (fun x => (x.1, x.2.1, x.2.2.1)) = abLaw p := by
  classical
  ext x
  rcases x with ⟨t, i, j⟩
  simp only [Law.map_mass, Law.prob, jointLaw, abLaw, Fintype.sum_prod_type,
    Prod.mk.injEq]
  simp only [ite_and]
  simpa [Finset.sum_ite_irrel] using joint_ab p t i j

/-- The global law has exactly the given `ac` marginal. -/
theorem jointLaw_ac (p : LocalTables T) (h : TriangleConditions p) :
    (jointLaw p h).map (fun x => (x.1, x.2.1, x.2.2.2)) = acLaw p := by
  classical
  ext x
  rcases x with ⟨t, i, k⟩
  simp only [Law.map_mass, Law.prob, jointLaw, acLaw, Fintype.sum_prod_type,
    Prod.mk.injEq]
  simp only [ite_and]
  simpa [Finset.sum_ite_irrel] using joint_ac p t i k

/-- The global law has exactly the given `bc` marginal. -/
theorem jointLaw_bc (p : LocalTables T) (h : TriangleConditions p) :
    (jointLaw p h).map (fun x => (x.1, x.2.2.1, x.2.2.2)) = bcLaw p := by
  classical
  ext x
  rcases x with ⟨t, j, k⟩
  simp only [Law.map_mass, Law.prob, jointLaw, bcLaw, Fintype.sum_prod_type,
    Prod.mk.injEq]
  simp only [ite_and]
  simpa [Finset.sum_ite_irrel] using joint_bc p t j k

/-- Every joint extension satisfies the four triangle inequalities in each slice. -/
theorem triangle_of_extension (p : LocalTables T)
    (q : T → Bool → Bool → Bool → ℝ)
    (hn : ∀ t i j k, 0 ≤ q t i j k)
    (hab : ∀ t i j, (∑ k : Bool, q t i j k) = p.ab t i j)
    (hac : ∀ t i k, (∑ j : Bool, q t i j k) = p.ac t i k)
    (hbc : ∀ t j k, (∑ i : Bool, q t i j k) = p.bc t j k) :
    TriangleConditions p := by
  intro t
  have hext : Slice.IsExtension (moments p t) (q t) := by
    refine ⟨hn t, ?_, ?_, ?_, ?_⟩
    · simp_rw [hab]
      rfl
    · intro i j
      rw [pair_ab, hab]
    · intro i k
      rw [pair_ac, hac]
    · intro j k
      rw [pair_bc, hbc]
  have hs := Slice.conditions_of_extension (moments p t) (q t) hext
  exact ⟨hs.triangle_a, hs.triangle_b, hs.triangle_c, hs.triangle_sum⟩

private theorem map_ab_mass (μ : Law (T × Bool × Bool × Bool))
    (t : T) (i j : Bool) :
    (μ.map (fun x => (x.1, x.2.1, x.2.2.1))).mass (t, i, j) =
      ∑ k : Bool, μ.mass (t, i, j, k) := by
  classical
  simp only [Law.map_mass, Law.prob, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  cases j <;> simp [Finset.sum_ite_irrel]

private theorem map_ac_mass (μ : Law (T × Bool × Bool × Bool))
    (t : T) (i k : Bool) :
    (μ.map (fun x => (x.1, x.2.1, x.2.2.2))).mass (t, i, k) =
      ∑ j : Bool, μ.mass (t, i, j, k) := by
  classical
  simp only [Law.map_mass, Law.prob, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_irrel]

private theorem map_bc_mass (μ : Law (T × Bool × Bool × Bool))
    (t : T) (j k : Bool) :
    (μ.map (fun x => (x.1, x.2.2.1, x.2.2.2))).mass (t, j, k) =
      ∑ i : Bool, μ.mass (t, i, j, k) := by
  classical
  simp only [Law.map_mass, Law.prob, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_irrel]

/-- Exact classification for singleton pair-only blocks with any finite common
state space, stated entirely as compatibility of probability laws. -/
theorem triangle_iff_global_law (p : LocalTables T) : TriangleConditions p ↔
    ∃ μ : Law (T × Bool × Bool × Bool),
      μ.map (fun x => (x.1, x.2.1, x.2.2.1)) = abLaw p ∧
      μ.map (fun x => (x.1, x.2.1, x.2.2.2)) = acLaw p ∧
      μ.map (fun x => (x.1, x.2.2.1, x.2.2.2)) = bcLaw p := by
  constructor
  · intro h
    exact ⟨jointLaw p h, jointLaw_ab p h, jointLaw_ac p h, jointLaw_bc p h⟩
  · rintro ⟨μ, hab, hac, hbc⟩
    apply triangle_of_extension p (fun t i j k => μ.mass (t, i, j, k))
    · exact fun t i j k => μ.nonneg (t, i, j, k)
    · intro t i j
      rw [← map_ab_mass, hab]
      rfl
    · intro t i k
      rw [← map_ac_mass, hac]
      rfl
    · intro t j k
      rw [← map_bc_mass, hbc]
      rfl

/-- Convert three consistent probability laws into their cell tables. -/
def ofCoreFamily (P : CoreFamily T Bool Bool Bool) (h : P.Consistent) : LocalTables T where
  ab t i j := P.ab.mass (t, i, j)
  ac t i k := P.ac.mass (t, i, k)
  bc t j k := P.bc.mass (t, j, k)
  ab_nonneg t i j := P.ab.nonneg (t, i, j)
  ac_nonneg t i k := P.ac.nonneg (t, i, k)
  bc_nonneg t j k := P.bc.nonneg (t, j, k)
  consistent_a t i := by
    have he := congrArg (fun μ => μ.mass (t, i)) h.1
    simpa only [CoreFamily.map_first_mass] using he
  consistent_b t j := by
    have he := congrArg (fun μ => μ.mass (t, j)) h.2.1
    simpa only [CoreFamily.map_first_mass, CoreFamily.map_second_mass] using he
  consistent_c t k := by
    have he := congrArg (fun μ => μ.mass (t, k)) h.2.2
    simpa only [CoreFamily.map_second_mass] using he
  total := by simpa only [Fintype.sum_prod_type] using P.ab.total

@[simp] theorem abLaw_ofCoreFamily (P : CoreFamily T Bool Bool Bool) (h : P.Consistent) :
    abLaw (ofCoreFamily P h) = P.ab := by ext x; rfl

@[simp] theorem acLaw_ofCoreFamily (P : CoreFamily T Bool Bool Bool) (h : P.Consistent) :
    acLaw (ofCoreFamily P h) = P.ac := by ext x; rfl

@[simp] theorem bcLaw_ofCoreFamily (P : CoreFamily T Bool Bool Bool) (h : P.Consistent) :
    bcLaw (ofCoreFamily P h) = P.bc := by ext x; rfl

/-- Singleton pair-only blocks are globally realizable exactly when each
common-block slice satisfies the four generalized triangle inequalities. -/
theorem core_exact (P : CoreFamily T Bool Bool Bool) (h : P.Consistent) :
    TriangleConditions (ofCoreFamily P h) ↔ P.Realizable := by
  simpa only [CoreFamily.Realizable, CoreFamily.IsRealization, abLaw_ofCoreFamily,
    acLaw_ofCoreFamily, bcLaw_ofCoreFamily] using triangle_iff_global_law (ofCoreFamily P h)

end AlphaCycle.Positive
