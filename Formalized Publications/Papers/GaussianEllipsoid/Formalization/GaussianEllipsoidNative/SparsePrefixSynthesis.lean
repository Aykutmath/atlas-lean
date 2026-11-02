import GaussianMatrixColumns
import BilinearSynthesis

noncomputable section
open MeasureTheory GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.SparseSupport

/-- Reindexing a finite support by its canonical Fin |I| enumeration. -/
theorem sum_support_enumeration {n : ℕ} {M : Type*} [AddCommMonoid M]
    (I : Finset (Fin n)) (f : Fin n → M) :
    (∑ a : Fin I.card, f (I.equivFin.symm a).val) = ∑ i ∈ I, f i := by
  rw [I.equivFin.symm.sum_comp (fun i : I => f i.val)]
  exact (Finset.sum_subtype I (fun _ => Iff.rfl) f).symm

/-- Exact observable identity between the rectangular-diagonal factorization
and the canonical rank-one synthesis, on an arbitrary prescribed support. -/
theorem sparsePrefixOperator_eq_scaled_synthesis {d n : ℕ} (I : Finset (Fin n))
    (X : Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4))) (u : Fin n → ℝ)
    (hu : ∀ i, i ∉ I → u i = 0) :
    sparsePrefixOperator d n I (rowsToMatrixPair (2*(d/4)) n X)
      (fun a => u (I.equivFin.symm a).val) =
        (Real.sqrt (d : ℝ))⁻¹ • GaussianEllipsoid.bilinearSynthesis u X := by
  apply_fun operatorFrobenius using fun S T h => by
    have hh := congrArg frobeniusOperator h
    simpa only [frobeniusOperator_operatorFrobenius] using hh
  ext j i
  rw [sparsePrefixOperator_entry, operatorFrobenius_smul_eq]
  change (Real.sqrt (d : ℝ))⁻¹ *
      (∑ a : Fin I.card, u (I.equivFin.symm a).val *
        (X (I.equivFin.symm a).val).2 i * (X (I.equivFin.symm a).val).1 j) =
    (Real.sqrt (d : ℝ))⁻¹ * operatorFrobenius (GaussianEllipsoid.bilinearSynthesis u X) j i
  rw [GaussianEllipsoid.bilinearSynthesis_entry,
    sum_support_enumeration I (fun k => u k * (X k).2 i * (X k).1 j)]
  congr 1
  calc
    (∑ k ∈ I, u k * (X k).2 i * (X k).1 j) =
        ∑ k, u k * (X k).2 i * (X k).1 j := by
      apply Finset.sum_subset (Finset.subset_univ I)
      intro k _ hk
      simp [hu k hk]
    _ = _ := Finset.sum_congr rfl (fun k _ => by ring)

/-- The l1 coefficient mass is unchanged by support restriction and enumeration. -/
theorem l1_support_enumeration {n : ℕ} (I : Finset (Fin n)) (u : Fin n → ℝ)
    (hu : ∀ i, i ∉ I → u i = 0) :
    (∑ a : Fin I.card, |u (I.equivFin.symm a).val|) = ∑ i, |u i| := by
  rw [sum_support_enumeration I (fun i => |u i|)]
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  simp [hu i hi]

/-- Consumer-ready sparse nuclear lower bound for the canonical synthesis,
under its actual row-pair sample event. -/
theorem sparseRowsGood_supported_nuclear_lower {d n m : ℕ} (hd : 24 ≤ d)
    {X : Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4))}
    (hX : X ∈ sparseRowsGood (2*(d/4)) n m)
    (I : Finset (Fin n)) (hI : I.card ≤ m) (u : Fin n → ℝ)
    (hu : ∀ i, i ∉ I → u i = 0) :
    Real.sqrt (d : ℝ)/12 * (∑ i, |u i|) ≤
      spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d : ℝ))⁻¹ • GaussianEllipsoid.bilinearSynthesis u X)) := by
  have hh := sparseGood_prefix_nuclear_lower hd hX I hI
    (fun a => u (I.equivFin.symm a).val)
  rw [sparsePrefixOperator_eq_scaled_synthesis I X u hu, l1_support_enumeration I u hu] at hh
  exact hh

/-- The complete requested sparse-prefix event in the canonical independent
Gaussian sample law used by the multiscale MGF proof. -/
theorem canonical_sparse_nuclear_event (A : ℝ) (hA : 0 < A) (d n : ℕ)
    (hd : GaussianEllipsoid.sparseEntropyCutoff A ≤ d)
    (hn : (n : ℝ) ≤ A*(d : ℝ)^2) :
    MeasurableSet (sparseRowsGood (2*(d/4)) n (sparseSupportSize d)) ∧
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      (sparseRowsGood (2*(d/4)) n (sparseSupportSize d))ᶜ ≤ Real.exp (-(d : ℝ)/2048) ∧
    ∀ X ∈ sparseRowsGood (2*(d/4)) n (sparseSupportSize d),
      ∀ u : Fin n → ℝ, (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ sparseSupportSize d →
        Real.sqrt (d : ℝ)/12 * (∑ i, |u i|) ≤
          spectralNuclearNorm (operatorFrobenius
            ((Real.sqrt (d : ℝ))⁻¹ • GaussianEllipsoid.bilinearSynthesis u X)) := by
  have hE := sparse_good_event A hA d n hd hn
  refine ⟨sparseRowsGood_measurable _ _ _, ?_, ?_⟩
  · rw [sparseRowsGood_failure_eq]
    exact hE.2.1
  · intro X hX u hu
    have hd8192 : 8192 ≤ d := (le_max_left _ _).trans hd
    apply sparseRowsGood_supported_nuclear_lower (by omega) hX
      (Finset.univ.filter (fun i => u i ≠ 0)) hu u
    intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi

end GaussianEllipsoid.SparseSupport
