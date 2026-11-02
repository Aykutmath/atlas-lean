import PaperBilinearOriginalBlocks
import CanonicalMultiscaleLaw
import AtomAsymptotics

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.SparseSupport
open GaussianMixedNormHelpers GaussianEllipsoidCandidate GaussianEllipsoid.ProjectedClusters
open scoped BigOperators Topology
namespace GaussianTensorMoments

/-- Literal normalized rank-one product event, on canonical (b,a) pairs. -/
def paperPairAtomEvent (C : ℝ) (d n h : ℕ) : Set (Fin n → Euclid h × Euclid h) :=
  {X | ∀ i, ‖(X i).1‖*‖(X i).2‖/Real.sqrt (d:ℝ) ≤ C*Real.sqrt (d:ℝ)}

theorem paperPairAtomEvent_measurable (C : ℝ) (d n h : ℕ) :
    MeasurableSet (paperPairAtomEvent C d n h) := by
  unfold paperPairAtomEvent
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

theorem atomRowsGood_subset_paperPairAtomEvent (d n h : ℕ) :
    atomRowsGood d n h ⊆ paperPairAtomEvent 1 d n h := by
  intro X hX i
  have hl : ‖(X i).1‖ ≤ Real.sqrt d :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr (hX i).1
  have hr : ‖(X i).2‖ ≤ Real.sqrt d :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr (hX i).2
  have hp : ‖(X i).1‖*‖(X i).2‖ ≤ (d:ℝ) :=
    (mul_le_mul hl hr (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt (Nat.cast_nonneg _))
  have hid : (d:ℝ)/Real.sqrt d = Real.sqrt d := by
    by_cases hd : d=0
    · simp [hd]
    · have hs : Real.sqrt (d:ℝ) ≠ 0 := by positivity
      apply (div_eq_iff hs).mpr
      exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
  simpa only [one_mul,hid] using div_le_div_of_nonneg_right hp (Real.sqrt_nonneg (d:ℝ))

theorem paperPairAtomEvent_row_bound {d n h : ℕ} {C : ℝ}
    {X : Fin n → Euclid h × Euclid h} (hX : X ∈ paperPairAtomEvent C d n h) (i : Fin n) :
    spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearRowOperator (X i))) ≤
      C*Real.sqrt d := by
  rw [operatorFrobenius_smul_eq,spectralNuclear_smul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt (d:ℝ))⁻¹*(‖(X i).1‖*‖(X i).2‖) :=
      mul_le_mul_of_nonneg_left (bilinearRowOperator_nuclear_le _) (by positivity)
    _ = ‖(X i).1‖*‖(X i).2‖/Real.sqrt (d:ℝ) := by ring
    _ ≤ _ := hX i

theorem paperPairAtomEvent_all_coefficients {d n h : ℕ} {C : ℝ}
    {X : Fin n → Euclid h × Euclid h} (hX : X ∈ paperPairAtomEvent C d n h)
    (u : Fin n → ℝ) : scaledBilinearNuclear d u X ≤ C*Real.sqrt d*(∑ i, |u i|) := by
  unfold scaledBilinearNuclear bilinearSynthesis
  rw [Finset.smul_sum]
  apply (nuclearOperator_sum_le Finset.univ _).trans
  calc
    _ = ∑ i, |u i| *spectralNuclearNorm (operatorFrobenius
      ((Real.sqrt (d:ℝ))⁻¹ • bilinearRowOperator (X i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_comm,operatorFrobenius_smul_eq,spectralNuclear_smul]
    _ ≤ ∑ i, |u i| *(C*Real.sqrt d) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (paperPairAtomEvent_row_bound hX i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem paperPairAtomEvent_failure_tendsto (A : ℝ) (hA : 0 < A) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
      (paperPairAtomEvent 1 d (n d) (d/2))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun d => measureReal_nonneg)) _
    (atomFailureBound_tendsto_zero A)
  filter_upwards [hn,eventually_ge_atTop 2] with d hnd hd
  have hhlo : (d:ℝ) ≤ 3*((d/2:ℕ):ℝ) := by exact_mod_cast (show d ≤ 3*(d/2) by omega)
  have hhup : (5/4:ℝ)*((d/2:ℕ):ℝ) ≤ d := by
    have hnat : 2*(d/2) ≤ d := Nat.mul_div_le d 2
    have hreal : 2*((d/2:ℕ):ℝ) ≤ d := by exact_mod_cast hnat
    nlinarith only [hreal,Nat.cast_nonneg (d/2) (α := ℝ)]
  calc
    _ ≤ (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
        (atomRowsGood d (n d) (d/2))ᶜ :=
      measureReal_mono (Set.compl_subset_compl.mpr (atomRowsGood_subset_paperPairAtomEvent _ _ _))
    _ ≤ 2*(n d:ℝ)*Real.exp (-((d/2:ℕ):ℝ)/256) := atomRowsGood_failure_le _ _ _ hhup
    _ ≤ atomFailureBound A d := by
      unfold atomFailureBound
      apply mul_le_mul
      · nlinarith only [hnd]
      · exact Real.exp_le_exp.mpr (by linarith only [hhlo])
      · positivity
      · positivity

/-- Paper E_atom in the original sample, with exact first/last halves.
The pair order is (b,a), so the product is the paper's ||a_i||||b_i|| by commutativity. -/
def paperAtomEvent (C : ℝ) (d n : ℕ) : Set (Fin n → Euclid d) :=
  extractedRows (paperBlockLeft d) (paperBlockRight d) ⁻¹' paperPairAtomEvent C d n (d/2)

theorem paper_atom_lemma (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ → ℕ,
      (∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) →
      Tendsto (fun d => (Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d))).real
        (paperAtomEvent C d (n d))ᶜ) atTop (𝓝 0) ∧
      ∀ d, ∀ x ∈ paperAtomEvent C d (n d), ∀ z : Fin (n d) → ℝ,
        spectralNuclearNorm (paperBilinearOperator d (n d) x ((MeasurableEquiv.toLp 2 (Fin (n d) → ℝ)) z)) ≤
          C*Real.sqrt d*(∑ i, |z i|) := by
  refine ⟨1,by norm_num,?_⟩
  intro n hn
  constructor
  · have hh := paperPairAtomEvent_failure_tendsto A hA n hn
    apply hh.congr'
    filter_upwards with d
    symm
    exact (extractedRows_preserving (paperBlockLeft d) (paperBlockRight d) (paperBlock_disjoint d)).measureReal_preimage
      (paperPairAtomEvent_measurable 1 d (n d) (d/2)).compl.nullMeasurableSet
  · intro d x hx z
    have hb := paperPairAtomEvent_all_coefficients hx z
    unfold scaledBilinearNuclear at hb
    rw [extractedRows_eq_tensorToCanonicalRows,scaled_bilinearSynthesis_tensorToCanonicalRows] at hb
    exact hb

end GaussianTensorMoments
#print axioms GaussianTensorMoments.paper_atom_lemma
