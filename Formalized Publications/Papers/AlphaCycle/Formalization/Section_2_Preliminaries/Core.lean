import Section_2_Preliminaries.FiniteLaw

/-! Local-law language for a length-three cycle with a finite common state space.
The four type parameters represent full assignments to the blocks `T`, `A`, `B`,
and `C`; each vertex block may therefore contain any finite number of vertices. -/

namespace AlphaCycle

variable (T A B C : Type*) [Fintype T] [Fintype A] [Fintype B] [Fintype C]

/-- The three full local distributions in the private-free cycle. -/
structure CoreFamily where
  ab : Law (T × A × B)
  ac : Law (T × A × C)
  bc : Law (T × B × C)

namespace CoreFamily

variable {T A B C}

/-- Agreement on all pairwise intersections, including the common block. -/
def Consistent (P : CoreFamily T A B C) : Prop :=
  P.ab.map (fun x => (x.1, x.2.1)) = P.ac.map (fun x => (x.1, x.2.1)) ∧
  P.ab.map (fun x => (x.1, x.2.2)) = P.bc.map (fun x => (x.1, x.2.1)) ∧
  P.ac.map (fun x => (x.1, x.2.2)) = P.bc.map (fun x => (x.1, x.2.2))

/-- A law realizes the complete distributions on all three local edges. -/
def IsRealization (P : CoreFamily T A B C) (μ : Law (T × A × B × C)) : Prop :=
  μ.map (fun x => (x.1, x.2.1, x.2.2.1)) = P.ab ∧
  μ.map (fun x => (x.1, x.2.1, x.2.2.2)) = P.ac ∧
  μ.map (fun x => (x.1, x.2.2.1, x.2.2.2)) = P.bc

/-- Membership in the multilinear polytope in local-law coordinates. -/
def Realizable (P : CoreFamily T A B C) : Prop := ∃ μ, P.IsRealization μ

/-- Forgetting the last local block amounts to summing its cells. -/
theorem map_first_mass (μ : Law (T × A × B)) (t : T) (a : A) :
    (μ.map (fun x => (x.1, x.2.1))).mass (t, a) = ∑ b : B, μ.mass (t, a, b) := by
  classical
  simp only [Law.map_mass, Law.prob, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp

/-- Forgetting the first pair-only block amounts to summing its cells. -/
theorem map_second_mass (μ : Law (T × A × B)) (t : T) (b : B) :
    (μ.map (fun x => (x.1, x.2.2))).mass (t, b) = ∑ a : A, μ.mass (t, a, b) := by
  classical
  simp only [Law.map_mass, Law.prob, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_irrel]

/-- A global law necessarily gives a consistent local family. -/
theorem consistent_of_realizable (P : CoreFamily T A B C) (h : P.Realizable) :
    P.Consistent := by
  rcases h with ⟨μ, hab, hac, hbc⟩
  simp [Consistent, ← hab, ← hac, ← hbc, Law.map_map, Function.comp_def]

variable {T' A' B' C' : Type*} [Fintype T'] [Fintype A'] [Fintype B'] [Fintype C']

/-- Relabel the four state spaces by pushing all three local laws forward. -/
noncomputable def map (P : CoreFamily T A B C)
    (u : T → T') (f : A → A') (g : B → B') (h : C → C') :
    CoreFamily T' A' B' C' where
  ab := P.ab.map (fun x => (u x.1, f x.2.1, g x.2.2))
  ac := P.ac.map (fun x => (u x.1, f x.2.1, h x.2.2))
  bc := P.bc.map (fun x => (u x.1, g x.2.1, h x.2.2))

theorem consistent_map (P : CoreFamily T A B C) (hp : P.Consistent)
    (u : T → T') (f : A → A') (g : B → B') (h : C → C') :
    (P.map u f g h).Consistent := by
  rcases hp with ⟨ha, hb, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · change (P.ab.map _).map _ = (P.ac.map _).map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × A => (u x.1, f x.2))) ha
  · change (P.ab.map _).map _ = (P.bc.map _).map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × B => (u x.1, g x.2))) hb
  · change (P.ac.map _).map _ = (P.bc.map _).map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × C => (u x.1, h x.2))) hc

theorem realizable_map (P : CoreFamily T A B C) (hp : P.Realizable)
    (u : T → T') (f : A → A') (g : B → B') (h : C → C') :
    (P.map u f g h).Realizable := by
  rcases hp with ⟨μ, hab, hac, hbc⟩
  refine ⟨μ.map (fun x => (u x.1, f x.2.1, g x.2.2.1, h x.2.2.2)), ?_, ?_, ?_⟩
  · change (μ.map _).map _ = P.ab.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × A × B => (u x.1, f x.2.1, g x.2.2))) hab
  · change (μ.map _).map _ = P.ac.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × A × C => (u x.1, f x.2.1, h x.2.2))) hac
  · change (μ.map _).map _ = P.bc.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : T × B × C => (u x.1, g x.2.1, h x.2.2))) hbc

/-- Retractions preserve a failure of global realizability. -/
theorem not_realizable_map (P : CoreFamily T A B C) (hp : ¬ P.Realizable)
    (u : T → T') (f : A → A') (g : B → B') (h : C → C')
    (u' : T' → T) (f' : A' → A) (g' : B' → B) (h' : C' → C)
    (hu : Function.LeftInverse u' u) (hf : Function.LeftInverse f' f)
    (hg : Function.LeftInverse g' g) (hh : Function.LeftInverse h' h) :
    ¬ (P.map u f g h).Realizable := by
  simp only [Function.LeftInverse] at hu hf hg hh
  intro hr
  have hr' := realizable_map _ hr u' f' g' h'
  have he : (P.map u f g h).map u' f' g' h' = P := by
    cases P with
    | mk ab ac bc =>
      simp only [map, Law.map_map, Function.comp_def, hu, hf, hg, hh]
      change CoreFamily.mk (ab.map id) (ac.map id) (bc.map id) = _
      rw [Law.map_id, Law.map_id, Law.map_id]
  rw [he] at hr'
  exact hp hr'

end CoreFamily
end AlphaCycle
