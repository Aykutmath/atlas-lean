import Section_2_Preliminaries.Basic
import Section_3_Obstruction.FourVariable

/-! Transport of the four-variable obstruction into larger pair-only blocks. -/
noncomputable section
open scoped BigOperators
namespace AlphaCycle.Negative

/-- The parity law viewed as a law on a two-bit block and a one-bit block. -/
def parityLaw : Law ((Bool × Bool) × Bool) where
  mass x := FourVariable.odd x.1.1 x.1.2 x.2
  nonneg x := FourVariable.odd_nonneg _ _ _
  total := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact FourVariable.odd_total

/-- The independent law on the two singleton blocks. -/
def independentLaw : Law (Bool × Bool) where
  mass x := FourVariable.independent x.1 x.2
  nonneg x := by norm_num [FourVariable.independent]
  total := by
    simpa only [Fintype.sum_prod_type] using FourVariable.independent_total

/-- The three local laws of the minimal obstruction. -/
def parityFamily : PairFamily (Bool × Bool) Bool Bool where
  ab := parityLaw
  ac := parityLaw
  bc := independentLaw

theorem parityFamily_consistent : parityFamily.Consistent := by
  refine ⟨rfl, ?_, ?_⟩
  all_goals
    ext b
    cases b <;>
      norm_num [parityFamily, parityLaw, independentLaw, Law.map,
        Fintype.sum_prod_type, Fintype.sum_bool, FourVariable.odd, FourVariable.independent]

theorem parityFamily_not_realizable : ¬ parityFamily.Realizable := by
  rintro ⟨μ, hab, hac, hbc⟩
  apply FourVariable.no_global (fun a b c d => μ.mass ((a,b),c,d))
    (fun a b c d => μ.nonneg _) 
  refine ⟨?_, ?_, ?_⟩
  · intro a b c
    have he := congrArg (fun ν : Law ((Bool × Bool) × Bool) => ν.mass ((a,b),c)) hab
    cases a <;> cases b <;> cases c <;>
      simpa [Law.map, Fintype.sum_prod_type, parityFamily, parityLaw] using he
  · intro a b d
    have he := congrArg (fun ν : Law ((Bool × Bool) × Bool) => ν.mass ((a,b),d)) hac
    cases a <;> cases b <;> cases d <;>
      simpa [Law.map, Fintype.sum_prod_type, parityFamily, parityLaw] using he
  · intro c d
    have he := congrArg (fun ν : Law (Bool × Bool) => ν.mass (c,d)) hbc
    simpa [Law.map, Fintype.sum_prod_type, parityFamily, independentLaw] using he

/-- Every choice of embeddings of the four active bits gives compatible local
laws in the larger state spaces, still with no global realization. -/
theorem lifted_obstruction {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : Bool × Bool → A) (g : Bool → B) (h : Bool → C)
    (f' : A → Bool × Bool) (g' : B → Bool) (h' : C → Bool)
    (hf : Function.LeftInverse f' f) (hg : Function.LeftInverse g' g)
    (hh : Function.LeftInverse h' h) :
    (parityFamily.map f g h).Consistent ∧ ¬ (parityFamily.map f g h).Realizable :=
  ⟨PairFamily.consistent_map _ parityFamily_consistent f g h,
    PairFamily.not_realizable_map _ parityFamily_not_realizable f g h f' g' h' hf hg hh⟩

/-- Embed two distinct active vertices in a Boolean block, fixing all other bits to one. -/
def twoBits {A : Type*} [DecidableEq A] (u v : A) (x : Bool × Bool) : A → Bool :=
  fun w => if w = u then x.1 else if w = v then x.2 else true

def oneBit {A : Type*} [DecidableEq A] (u : A) (x : Bool) : A → Bool :=
  fun w => if w = u then x else true

theorem twoBits_leftInverse {A : Type*} [DecidableEq A] (u v : A) (hne : u ≠ v) :
    Function.LeftInverse (fun x : A → Bool => (x u, x v)) (twoBits u v) := by
  intro x
  simp [twoBits, hne, Ne.symm hne]

theorem oneBit_leftInverse {A : Type*} [DecidableEq A] (u : A) :
    Function.LeftInverse (fun x : A → Bool => x u) (oneBit u) := by
  intro x; simp [oneBit]

/-- The paper's lifted nonrealizability construction for arbitrary finite
pair-only vertex blocks, with two selected vertices in the first block. -/
theorem boolean_block_obstruction {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (u v : A) (b : B) (c : C) (hne : u ≠ v) :
    ∃ P : PairFamily (A → Bool) (B → Bool) (C → Bool),
      P.Consistent ∧ ¬ P.Realizable := by
  refine ⟨parityFamily.map (twoBits u v) (oneBit b) (oneBit c), ?_⟩
  exact lifted_obstruction _ _ _ (fun x => (x u, x v)) (fun x => x b) (fun x => x c)
    (twoBits_leftInverse u v hne) (oneBit_leftInverse b) (oneBit_leftInverse c)

end AlphaCycle.Negative
