import Section_2_Preliminaries.FiniteLaw

/-! Local-law language for the private-free core.  In the paper, `A`, `B`,
and `C` here are the *state spaces* of the three pair-only vertex blocks. -/
namespace AlphaCycle

variable (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]

/-- Local laws on the three pair blocks; edge order is `ab`, `ac`, `bc`. -/
structure PairFamily where
  ab : Law (A × B)
  ac : Law (A × C)
  bc : Law (B × C)

namespace PairFamily
variable {A B C}

/-- Agreement of the full distributions on all overlaps. -/
def Consistent (P : PairFamily A B C) : Prop :=
  P.ab.map Prod.fst = P.ac.map Prod.fst ∧
  P.ab.map Prod.snd = P.bc.map Prod.fst ∧
  P.ac.map Prod.snd = P.bc.map Prod.snd

/-- One law realizes the three prescribed edge laws. -/
def IsRealization (P : PairFamily A B C) (μ : Law (A × B × C)) : Prop :=
  μ.map (fun x => (x.1, x.2.1)) = P.ab ∧
  μ.map (fun x => (x.1, x.2.2)) = P.ac ∧
  μ.map (fun x => (x.2.1, x.2.2)) = P.bc

def Realizable (P : PairFamily A B C) : Prop := ∃ μ, P.IsRealization μ

variable {A' B' C' : Type*} [Fintype A'] [Fintype B'] [Fintype C']

/-- Changing the state spaces transports all three local laws. -/
noncomputable def map (P : PairFamily A B C) (f : A → A') (g : B → B') (h : C → C') :
    PairFamily A' B' C' where
  ab := P.ab.map (fun x => (f x.1, g x.2))
  ac := P.ac.map (fun x => (f x.1, h x.2))
  bc := P.bc.map (fun x => (g x.1, h x.2))

theorem consistent_map (P : PairFamily A B C) (hp : P.Consistent)
    (f : A → A') (g : B → B') (h : C → C') : (P.map f g h).Consistent := by
  rcases hp with ⟨ha, hb, hc⟩
  constructor
  · change (P.ab.map _).map _ = (P.ac.map _).map _
    simpa only [Law.map_map, Function.comp_def] using congrArg (Law.map f) ha
  constructor
  · change (P.ab.map _).map _ = (P.bc.map _).map _
    simpa only [Law.map_map, Function.comp_def] using congrArg (Law.map g) hb
  · change (P.ac.map _).map _ = (P.bc.map _).map _
    simpa only [Law.map_map, Function.comp_def] using congrArg (Law.map h) hc

theorem realizable_map (P : PairFamily A B C) (hp : P.Realizable)
    (f : A → A') (g : B → B') (h : C → C') : (P.map f g h).Realizable := by
  obtain ⟨μ, hab, hac, hbc⟩ := hp
  refine ⟨μ.map (fun x => (f x.1, g x.2.1, h x.2.2)), ?_, ?_, ?_⟩
  · change (μ.map _).map _ = P.ab.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : A × B => (f x.1, g x.2))) hab
  · change (μ.map _).map _ = P.ac.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : A × C => (f x.1, h x.2))) hac
  · change (μ.map _).map _ = P.bc.map _
    simpa only [Law.map_map, Function.comp_def] using
      congrArg (Law.map (fun x : B × C => (g x.1, h x.2))) hbc

/-- An injective embedding with explicit left inverses cannot remove an obstruction. -/
theorem not_realizable_map (P : PairFamily A B C) (hp : ¬ P.Realizable)
    (f : A → A') (g : B → B') (h : C → C')
    (f' : A' → A) (g' : B' → B) (h' : C' → C)
    (hf : Function.LeftInverse f' f) (hg : Function.LeftInverse g' g)
    (hh : Function.LeftInverse h' h) : ¬ (P.map f g h).Realizable := by
  simp only [Function.LeftInverse] at hf hg hh
  intro hr
  have hr' := realizable_map _ hr f' g' h'
  have he : (P.map f g h).map f' g' h' = P := by
    cases P with
    | mk ab ac bc =>
      simp only [map, Law.map_map, Function.comp_def, hf, hg, hh]
      change PairFamily.mk (ab.map id) (ac.map id) (bc.map id) = _
      rw [Law.map_id, Law.map_id, Law.map_id]
  rw [he] at hr'
  exact hp hr'

end PairFamily
end AlphaCycle
