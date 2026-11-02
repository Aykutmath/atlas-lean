import SparseNormNet
import FiniteSupportCount

noncomputable section
open MeasureTheory GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoid.SparseSupport

/-- Enumerated restriction to a finite column support. -/
def supportEntries (h n : ℕ) (I : Finset (Fin n))
    (x : (Fin h × Fin n) → ℝ) : (Fin h × Fin I.card) → ℝ :=
  fun p => x (p.1, (I.equivFin.symm p.2).val)

theorem supportEntries_continuous (h n : ℕ) (I : Finset (Fin n)) :
    Continuous (supportEntries h n I) :=
  continuous_pi (fun p => continuous_apply _)

theorem supportEntries_law (h n : ℕ) (I : Finset (Fin n)) :
    (gaussianProductLaw (Fin h × Fin n)).map (supportEntries h n I) =
      gaussianProductLaw (Fin h × Fin I.card) := by
  apply gaussianProductLaw_map_subfamily
  intro a b hab
  rcases a with ⟨a₁,a₂⟩
  rcases b with ⟨b₁,b₂⟩
  simp only [Prod.mk.injEq] at hab ⊢
  refine ⟨hab.1, ?_⟩
  exact I.equivFin.symm.injective (Subtype.ext hab.2)

/-- The actual Euclidean submatrix as an operator, indexed by Fin |I|. -/
def supportOperator (h n : ℕ) (I : Finset (Fin n)) (x : (Fin h × Fin n) → ℝ) :=
  gaussianMatrixCLM h I.card (supportEntries h n I x)

theorem supportOperator_continuous (h n : ℕ) (I : Finset (Fin n)) :
    Continuous (supportOperator h n I) :=
  (gaussianMatrixCLM_continuous h I.card).comp (supportEntries_continuous h n I)

/-- Failure of a quadratic all-vector lower bound on one support. -/
def supportFailure (h n : ℕ) (I : Finset (Fin n)) : Set ((Fin h × Fin n) → ℝ) :=
  {x | ∃ v : EuclideanSpace ℝ (Fin I.card),
    ‖supportOperator h n I x v‖^2 < (h : ℝ)/5 * ‖v‖^2}

theorem supportFailure_isOpen (h n : ℕ) (I : Finset (Fin n)) :
    IsOpen (supportFailure h n I) := by
  change IsOpen {x | ∃ v : EuclideanSpace ℝ (Fin I.card),
    ‖supportOperator h n I x v‖^2 < (h : ℝ)/5 * ‖v‖^2}
  simp only [Set.setOf_exists]
  apply isOpen_iUnion
  intro v
  exact isOpen_lt (((supportOperator_continuous h n I).clm_apply continuous_const).norm.pow 2)
    continuous_const

/-- Tail for one prescribed support, transferred from its actual iid submatrix law. -/
theorem supportFailure_le (h n : ℕ) (I : Finset (Fin n)) :
    (gaussianProductLaw (Fin h × Fin n)).real (supportFailure h n I) ≤
      2 * (9 : ℝ)^I.card * Real.exp (-(h : ℝ)/256) := by
  let S : Set ((Fin h × Fin I.card) → ℝ) :=
    {x | ∃ v : EuclideanSpace ℝ (Fin I.card),
      ‖gaussianMatrixCLM h I.card x v‖^2 < (h : ℝ)/5 * ‖v‖^2}
  have hS : MeasurableSet S := by
    apply IsOpen.measurableSet
    dsimp [S]
    simp only [Set.setOf_exists]
    apply isOpen_iUnion
    intro v
    exact isOpen_lt (((gaussianMatrixCLM_continuous h I.card).clm_apply continuous_const).norm.pow 2)
      continuous_const
  have ht := gaussianMatrixCLM_lower_tail h I.card
  change (gaussianProductLaw (Fin h × Fin I.card)).real S ≤ _ at ht
  rw [← supportEntries_law h n I, Measure.real,
    Measure.map_apply (supportEntries_continuous h n I).measurable hS] at ht
  exact ht

/-- All support sets of cardinality at most m, including the empty support. -/
def smallSupports (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun I => I.card ≤ m)

@[simp] theorem mem_smallSupports {n m : ℕ} (I : Finset (Fin n)) :
    I ∈ smallSupports n m ↔ I.card ≤ m := by
  simp [smallSupports]

theorem smallSupports_card_le (n m : ℕ) : (smallSupports n m).card ≤ (n+1)^m := by
  simpa only [smallSupports, Finset.card_univ, Fintype.card_fin] using
    GaussianEllipsoid.card_small_supports_le (Finset.univ : Finset (Fin n)) m

/-- A simultaneous bad event over every small support. -/
def sparseFailure (h n m : ℕ) : Set ((Fin h × Fin n) → ℝ) :=
  ⋃ I ∈ smallSupports n m, supportFailure h n I

theorem sparseFailure_measurable (h n m : ℕ) : MeasurableSet (sparseFailure h n m) := by
  apply IsOpen.measurableSet
  exact isOpen_iUnion fun I => isOpen_iUnion fun _ => supportFailure_isOpen h n I

/-- The actual-law simultaneous sparse singular-value estimate, valid in every
dimension. No independence between different supports is assumed. -/
theorem sparseFailure_le (h n m : ℕ) :
    (gaussianProductLaw (Fin h × Fin n)).real (sparseFailure h n m) ≤
      2 * (9 * (n+1) : ℝ)^m * Real.exp (-(h : ℝ)/256) := by
  classical
  calc
    _ ≤ ∑ I ∈ smallSupports n m,
        (gaussianProductLaw (Fin h × Fin n)).real (supportFailure h n I) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _I ∈ smallSupports n m, 2 * (9 : ℝ)^m * Real.exp (-(h : ℝ)/256) := by
      apply Finset.sum_le_sum
      intro I hI
      apply (supportFailure_le h n I).trans
      have hIm : I.card ≤ m := (mem_smallSupports I).mp hI
      gcongr
      norm_num
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : ((smallSupports n m).card : ℝ) ≤ (n+1 : ℝ)^m := by
        exact_mod_cast smallSupports_card_le n m
      rw [mul_pow]
      have hb := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ 2 * (9 : ℝ)^m * Real.exp (-(h : ℝ)/256) by positivity)
      nlinarith only [hb]

/-- Two independent matrices represented by the product of the actual entry laws. -/
def matrixPairLaw (h n : ℕ) :=
  (gaussianProductLaw (Fin h × Fin n)).prod (gaussianProductLaw (Fin h × Fin n))

instance matrixPairLaw_probability (h n : ℕ) : IsProbabilityMeasure (matrixPairLaw h n) := by
  unfold matrixPairLaw
  infer_instance

/-- On this concrete measurable event both actual matrices obey all small-support
all-vector lower bounds. -/
def sparseGood (h n m : ℕ) : Set (((Fin h × Fin n) → ℝ) × ((Fin h × Fin n) → ℝ)) :=
  (Prod.fst ⁻¹' sparseFailure h n m ∪ Prod.snd ⁻¹' sparseFailure h n m)ᶜ

theorem sparseGood_measurable (h n m : ℕ) : MeasurableSet (sparseGood h n m) :=
  ((sparseFailure_measurable h n m).preimage measurable_fst |>.union
    ((sparseFailure_measurable h n m).preimage measurable_snd)).compl

theorem sparseGood_failure_le (h n m : ℕ) :
    (matrixPairLaw h n).real (sparseGood h n m)ᶜ ≤
      4 * (9 * (n+1) : ℝ)^m * Real.exp (-(h : ℝ)/256) := by
  have hf : (matrixPairLaw h n).real (Prod.fst ⁻¹' sparseFailure h n m) =
      (gaussianProductLaw (Fin h × Fin n)).real (sparseFailure h n m) := by
    rw [Measure.real, ← Measure.map_apply measurable_fst (sparseFailure_measurable h n m),
      matrixPairLaw, Measure.map_fst_prod]
    simp [Measure.real]
  have hs : (matrixPairLaw h n).real (Prod.snd ⁻¹' sparseFailure h n m) =
      (gaussianProductLaw (Fin h × Fin n)).real (sparseFailure h n m) := by
    rw [Measure.real, ← Measure.map_apply measurable_snd (sparseFailure_measurable h n m),
      matrixPairLaw, Measure.map_snd_prod]
    simp [Measure.real]
  simp only [sparseGood, compl_compl]
  apply (measureReal_union_le _ _).trans
  rw [hf, hs]
  linarith [sparseFailure_le h n m]

/-- Consumer interface: simultaneous quadratic lower estimates for both
matrices and all vectors on every support of size at most m. -/
theorem sparseGood_lower (h n m : ℕ) {p}
    (hp : p ∈ sparseGood h n m) (I : Finset (Fin n)) (hI : I.card ≤ m)
    (v : EuclideanSpace ℝ (Fin I.card)) :
    (h : ℝ)/5 * ‖v‖^2 ≤ ‖supportOperator h n I p.1 v‖^2 ∧
    (h : ℝ)/5 * ‖v‖^2 ≤ ‖supportOperator h n I p.2 v‖^2 := by
  have hnot := hp
  change p ∉ (Prod.fst ⁻¹' sparseFailure h n m ∪ Prod.snd ⁻¹' sparseFailure h n m) at hnot
  constructor
  · by_contra hh
    apply hnot
    apply Or.inl
    exact Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨(mem_smallSupports I).mpr hI, v, lt_of_not_ge hh⟩⟩
  · by_contra hh
    apply hnot
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨(mem_smallSupports I).mpr hI, v, lt_of_not_ge hh⟩⟩

/-- The even half-dimension used by the block construction has enough rows. -/
theorem even_half_dim_lower {d : ℕ} (hd : 24 ≤ d) : (d : ℝ)/12 ≤ (2*(d/4) : ℕ)/5 := by
  have hrem := Nat.mod_lt d (by decide : 0 < 4)
  have hsplit := Nat.mod_add_div d 4
  have hnat : 5*d ≤ 24*(d/4) := by omega
  have hr : 5*(d : ℝ) ≤ 24*(d/4 : ℕ) := by exact_mod_cast hnat
  push_cast
  linarith

/-- Conservative dimension-normalized lower bound used by the multiscale
prefix. The event controls the two matrices simultaneously. -/
theorem sparseGood_dimension_lower {d n m : ℕ} (hd : 24 ≤ d) {p}
    (hp : p ∈ sparseGood (2*(d/4)) n m) (I : Finset (Fin n)) (hI : I.card ≤ m)
    (v : EuclideanSpace ℝ (Fin I.card)) :
    (d : ℝ)/12 * ‖v‖^2 ≤ ‖supportOperator (2*(d/4)) n I p.1 v‖^2 ∧
    (d : ℝ)/12 * ‖v‖^2 ≤ ‖supportOperator (2*(d/4)) n I p.2 v‖^2 := by
  have hb := sparseGood_lower (2*(d/4)) n m hp I hI v
  have hdv := mul_le_mul_of_nonneg_right (even_half_dim_lower hd) (sq_nonneg ‖v‖)
  exact ⟨hdv.trans hb.1, hdv.trans hb.2⟩

end GaussianEllipsoid.SparseSupport
