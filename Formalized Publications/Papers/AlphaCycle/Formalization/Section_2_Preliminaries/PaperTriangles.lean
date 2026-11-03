import Section_2_Preliminaries.CyclePermutation
import Section_2_Preliminaries.GeometryCycle

/-! Explicit scalar computations and relaxation identities used in the paper's
switched-triangle proof. -/
noncomputable section
namespace AlphaCycle.Triangle

/-- The four Fréchet inequalities for the two one-marginals and their joint mass. -/
def Frechet (p q pq : ℝ) : Prop :=
  0 ≤ pq ∧ pq ≤ p ∧ pq ≤ q ∧ p + q - pq ≤ 1

/-- Substitution of a constant zero first variable gives exactly Fréchet. -/
theorem GT_constant_zero_iff (q r qr : ℝ) :
    GT 1 0 q r 0 0 qr ↔ Frechet q r qr := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Substitution of a constant one first variable gives exactly Fréchet. -/
theorem GT_constant_one_iff (q r qr : ℝ) :
    GT 1 1 q r q r qr ↔ Frechet q r qr := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem GT_constant_middle_zero_iff (p r pr : ℝ) :
    GT 1 p 0 r 0 pr 0 ↔ Frechet p r pr := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem GT_constant_middle_one_iff (p r pr : ℝ) :
    GT 1 p 1 r p pr r ↔ Frechet p r pr := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem GT_constant_last_zero_iff (p q pq : ℝ) :
    GT 1 p q 0 pq 0 0 ↔ Frechet p q pq := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem GT_constant_last_one_iff (p q pq : ℝ) :
    GT 1 p q 1 pq p q ↔ Frechet p q pq := by
  unfold GT Frechet
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The exact three scalar inequalities displayed in the nonconstant case of
the lifted-obstruction proof. -/
theorem GT_half_quarter_iff (p a d : ℝ) :
    GT 1 p (1/2) (1/2) a d (1/4) ↔
      a + d ≤ p + 1/4 ∧ |a - d| ≤ 1/4 ∧ p - a - d ≤ 1/4 := by
  simp only [GT, abs_le]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, ⟨by linarith, by linarith⟩, by linarith⟩
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨h1, by linarith, by linarith, by linarith⟩

/-- A nonconstant signed literal is either the positive or the negative bit. -/
def Literal.IsBit (l : Literal) : Prop := l = .pos ∨ l = .neg

theorem fairMoment_bit (l : Literal) (hl : l.IsBit) : fairMoment l = 1/2 := by
  rcases hl with rfl | rfl <;> norm_num [fairMoment, Literal.eval]

/-- Independent fair bits give moment one quarter for every pair of literals. -/
theorem fairPair_bits (l k : Literal) (hl : l.IsBit) (hk : k.IsBit) :
    fairPair l k = 1/4 := by
  rcases hl with rfl | rfl <;> rcases hk with rfl | rfl <;>
    norm_num [fairPair, activeX, Literal.eval]

/-- A single literal of either active bit has expectation one half. -/
theorem fairPair_single (l : Literal) (hl : l.IsBit) :
    fairPair l .one = 1/2 ∧ fairPair .one l = 1/2 := by
  rcases hl with rfl | rfl <;> norm_num [fairPair, activeX, Literal.eval]

/-- The parity law makes each single-bit literal independent of its parity literal. -/
theorem parityMoment_single (l k : Literal) (hl : l.IsBit) (hk : k.IsBit) :
    parityMoment l .one k = 1/4 ∧ parityMoment .one l k = 1/4 := by
  rcases hl with rfl | rfl <;> rcases hk with rfl | rfl <;>
    norm_num [parityMoment, activeX, Literal.eval, FourVariable.odd, Fintype.sum_bool]

/-- A two-literal active conjunction is one of four equiprobable active pairs,
and its joint mass with a parity literal is either zero or one quarter. -/
theorem parityMoment_double (l k w : Literal)
    (hl : l.IsBit) (hk : k.IsBit) (hw : w.IsBit) :
    fairPair l k = 1/4 ∧
      (parityMoment l k w = 0 ∨ parityMoment l k w = 1/4) := by
  rcases hl with rfl | rfl <;> rcases hk with rfl | rfl <;>
    rcases hw with rfl | rfl <;>
    norm_num [fairPair, parityMoment, activeX, Literal.eval, FourVariable.odd, Fintype.sum_bool]

/-- The one-literal numerical case satisfies all three displayed scalar inequalities. -/
theorem scalar_single_literal :
    (1/4:ℝ) + 1/4 ≤ 1/2 + 1/4 ∧ |(1/4:ℝ) - 1/4| ≤ 1/4 ∧
      (1/2:ℝ) - 1/4 - 1/4 ≤ 1/4 := by norm_num

/-- Each of the four possible pairs of parity masses satisfies the displayed
scalar inequalities in the two-literal case. -/
theorem scalar_double_literal (a d : ℝ)
    (ha : a = 0 ∨ a = 1/4) (hd : d = 0 ∨ d = 1/4) :
    a + d ≤ (1/4:ℝ) + 1/4 ∧ |a - d| ≤ 1/4 ∧ 1/4 - a - d ≤ 1/4 := by
  rcases ha with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num

/-- The elementary Boolean inequality used for the fourth deterministic triangle inequality. -/
theorem boolean_triangle_inequality (x y z : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    x + y + z ≤ 1 + x*y + x*z + y*z := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> norm_num

/-- Every two events in one genuine finite probability law satisfy Fréchet. -/
theorem frechet_probability {I : Type*} [Fintype I] (μ : Law I) (P Q : I → Prop) :
    Frechet (μ.prob P) (μ.prob Q) (μ.prob (fun i => P i ∧ Q i)) := by
  classical
  refine ⟨μ.prob_nonneg _, μ.prob_mono (fun _ => And.left),
    μ.prob_mono (fun _ => And.right), ?_⟩
  have h : μ.prob P + μ.prob Q - μ.prob (fun i => P i ∧ Q i) =
      μ.prob (fun i => P i ∨ Q i) := by
    simp only [Law.prob, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : P i <;> by_cases hq : Q i <;> simp [hp, hq]
  rw [h]
  exact μ.prob_le_one _

end AlphaCycle.Triangle

namespace AlphaCycle
open Classical
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's standalone set `GT(F)`: all switchings of the four generalized
triangle inequalities for the supported triple `F`. -/
def switchedGeneralizedTriangleSet (e f : Fin 3 → Finset V)
    (hf : ∀ i, f i ∈ completedSupport e) : Set (MomentVector (completedSupport e)) :=
  {z | ∀ u : Finset V, generalizedTriangle e f hf (switchVector e u z)}

/-- The distinguished relaxation is exactly `CER(H) ∩ GT(C̄)`. -/
theorem distinguishedRelaxation_eq_inter (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    distinguishedRelaxation e f = completeEdgeRelaxation e ∩
      switchedGeneralizedTriangleSet e f.edge f.supported := rfl

/-- The all-cycle relaxation is exactly `CER(H)` intersected with all `GT(F)`. -/
theorem allCycleRelaxation_eq_inter (e : Fin 3 → Finset V) :
    allCycleRelaxation e = completeEdgeRelaxation e ∩
      ⋂ f : SupportedCycle e, switchedGeneralizedTriangleSet e f.edge f.supported := by
  ext z
  simp only [allCycleRelaxation, switchedGeneralizedTriangleSet,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- All switchings for any no-private supported triple are valid on `MP(H)`. -/
theorem multilinearPolytope_subset_switchedGeneralizedTriangleSet
    (e f : Fin 3 → Finset V) (hf : ∀ i, f i ∈ completedSupport e)
    (hn : Triangle.NoPrivate (f 0) (f 1) (f 2)) :
    multilinearPolytope (completedSupport e) ⊆ switchedGeneralizedTriangleSet e f hf := by
  intro z hz u
  obtain ⟨μ, rfl⟩ := (mem_multilinearPolytope_iff _ _).mp hz
  rw [switchVector_momentVector]
  exact generalizedTriangle_momentVector e f hf hn _

theorem distinguishedRelaxation_subset_completeEdgeRelaxation
    (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    distinguishedRelaxation e f ⊆ completeEdgeRelaxation e := fun _ hz => hz.1

/-- The complete four-term inclusion chain displayed before the main theorem. -/
theorem relaxation_inclusion_chain (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    multilinearPolytope (completedSupport e) ⊆ allCycleRelaxation e ∧
    allCycleRelaxation e ⊆ distinguishedRelaxation e f ∧
    distinguishedRelaxation e f ⊆ completeEdgeRelaxation e :=
  ⟨multilinearPolytope_subset_allCycleRelaxation e,
    allCycleRelaxation_subset_distinguishedRelaxation e f,
    distinguishedRelaxation_subset_completeEdgeRelaxation e f⟩

/-- A deterministic law has exactly the deterministic multilinear coordinates. -/
theorem momentVector_dirac_eq_monomialLift (S : Finset (Finset V)) (x : Finset V) :
    momentVector S (Law.dirac x) = monomialLift S x := by
  funext s
  simp [momentVector, moment, monomialLift]

/-- On every deterministic Boolean lift, the signed switching formula is exactly
coordinate complementation of the switched vertices. -/
theorem switchVector_monomialLift (e : Fin 3 → Finset V) (u x : Finset V) :
    switchVector e u (monomialLift (completedSupport e) x) =
      monomialLift (completedSupport e) (x ∆ u) := by
  rw [← momentVector_dirac_eq_monomialLift]
  funext s
  rw [switchVector_moment_probability, Law.prob_dirac]
  simp only [monomialLift, switched_subset_iff]
  split_ifs <;> rfl

/-- Applying the same switching twice recovers any point of the multilinear polytope. -/
theorem switchVector_involutive_on_multilinearPolytope
    (e : Fin 3 → Finset V) (u : Finset V)
    {z : MomentVector (completedSupport e)} (hz : z ∈ multilinearPolytope (completedSupport e)) :
    switchVector e u (switchVector e u z) = z := by
  obtain ⟨μ, rfl⟩ := (mem_multilinearPolytope_iff _ _).mp hz
  rw [switchVector_momentVector, switchVector_momentVector, Law.map_map]
  have he : (fun x : Finset V => x ∆ u) ∘ (fun x : Finset V => x ∆ u) = id := by
    funext x
    ext v
    simp only [Function.comp_apply, id_eq, Finset.mem_symmDiff]
    tauto
  rw [he, Law.map_id]

/-- The switching map takes `MP(H)` onto itself, as stated in the paper. -/
theorem switchVector_image_multilinearPolytope
    (e : Fin 3 → Finset V) (u : Finset V) :
    switchVector e u '' multilinearPolytope (completedSupport e) =
      multilinearPolytope (completedSupport e) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact switchVector_mem_multilinearPolytope e u hz
  · intro z hz
    exact ⟨switchVector e u z, switchVector_mem_multilinearPolytope e u hz,
      switchVector_involutive_on_multilinearPolytope e u hz⟩

end AlphaCycle
