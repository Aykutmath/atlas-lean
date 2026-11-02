import ActualLateFixedVector
import AtomAsymptotics
import MultiscaleNetEntropy

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- The actual whole sparse coefficient-class failure event at μ=2⁻³⁰. -/
def actualMultiscaleBad (d n : ℕ) (K : ℝ) :
    Set (Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4))) :=
  {X | ∃ u : Fin n → ℝ,
    ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d ∧
    scaledBilinearNuclear d u X < multiscaleConstant K * Real.sqrt d * coefficientMass u}

theorem continuous_scaledBilinearNuclear {n h : ℕ} (d : ℕ) (u : Fin n → ℝ) :
    Continuous (fun X : Fin n → Euclid h × Euclid h => scaledBilinearNuclear d u X) := by
  apply (continuous_spectralNuclear h h).comp
  apply (continuous_operatorFrobenius h h).comp
  have hsyn : Continuous (bilinearSynthesis u :
      (Fin n → Euclid h × Euclid h) → (Euclid h →L[ℝ] Euclid h)) := by
    unfold bilinearSynthesis
    apply continuous_finset_sum
    intro i _
    simpa only [Pi.smul_def, Function.comp_def] using!
      (((continuous_bilinearRowOperator h h).comp (continuous_apply i)).const_smul (u i))
  simpa only [Pi.smul_def] using! hsyn.const_smul ((Real.sqrt (d : ℝ))⁻¹)

theorem actualMultiscaleBad_isOpen (d n : ℕ) (K : ℝ) : IsOpen (actualMultiscaleBad d n K) := by
  unfold actualMultiscaleBad
  simp only [Set.setOf_exists]
  apply isOpen_iUnion
  intro u
  by_cases hs : ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d
  · simpa only [hs, true_and] using
      isOpen_lt (continuous_scaledBilinearNuclear d u) continuous_const
  · simp [hs]

/-- A concrete finite-dimension bound: sparse-prefix and atom probabilities are
proved from the actual Gaussian law. The only input remaining is the fixed-vector
multiscale probability, to be supplied by the retained/captured/late proof. -/
theorem actual_multiscale_uniform_probability_le (A K : ℝ) (hA : 0 < A) (hK : 0 ≤ K)
    (d n : ℕ) (hd : max 24 (sparseEntropyCutoff A) ≤ d)
    (hn : (n:ℝ) ≤ A*(d:ℝ)^2) (p : ℝ) (hp : 0 ≤ p)
    (hfixed : ∀ u : Fin n → ℝ, coefficientMass u = 1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤ p) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real (actualMultiscaleBad d n K) ≤
      Real.exp (-(d:ℝ)/2048) + atomFailureBound A d +
        ((1+8/multiscaleFixedConstant K)*(n+1))^⌊K*d⌋₊ * p := by
  let E := sparseRowsGood (2*(d/4)) n (sparseSupportSize d)
  let F := atomRowsGood d n (2*(d/4))
  let U := actualMultiscaleBad d n K
  let μ := gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))
  have hsp := (canonical_sparse_nuclear_event A hA d n ((le_max_right _ _).trans hd) hn).2.1
  have hatom := (canonical_atom_event A hA d n ((le_max_left _ _).trans hd) hn).2.1
  have hnet := actual_uniform_failure_le_net (d:=d) (n:=n) (h:=2*(d/4)) (m:=⌊K*d⌋₊)
    (multiscaleFixedConstant_pos K) hp E (fun u hu hs => by
      apply hfixed u hu
      have hsc : ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ (⌊K*d⌋₊:ℝ) := by
        exact_mod_cast hs
      exact hsc.trans (Nat.floor_le (by positivity)))
  have heq : {X | ∃ u : Fin n → ℝ, (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ ⌊K*d⌋₊ ∧
      scaledBilinearNuclear d u X < (multiscaleFixedConstant K/2)*Real.sqrt d*coefficientMass u} = U := by
    ext X
    simp only [U, actualMultiscaleBad, Set.mem_setOf_eq, multiscaleConstant_eq_half,
      Nat.le_floor_iff (show 0 ≤ K*(d:ℝ) by positivity)]
  rw [heq] at hnet
  have hsub : U ⊆ (Eᶜ ∪ Fᶜ) ∪ (U ∩ E ∩ F) := by
    intro X hX
    by_cases hE : X ∈ E
    · by_cases hF : X ∈ F
      · exact Or.inr ⟨⟨hX,hE⟩,hF⟩
      · exact Or.inl (Or.inr hF)
    · exact Or.inl (Or.inl hE)
  calc
    μ.real U ≤ μ.real ((Eᶜ ∪ Fᶜ) ∪ (U ∩ E ∩ F)) := measureReal_mono hsub
    _ ≤ μ.real (Eᶜ ∪ Fᶜ) + μ.real (U ∩ E ∩ F) := measureReal_union_le _ _
    _ ≤ (μ.real Eᶜ + μ.real Fᶜ) + μ.real (U ∩ E ∩ F) :=
      add_le_add_left (measureReal_union_le _ _) _
    _ ≤ _ := add_le_add (add_le_add hsp hatom) hnet

/-- End-to-end net/entropy/atom/sparse-prefix implication in the actual law.
Its fixed-vector hypothesis is the precise remaining probabilistic interface;
there are no supplied nets, supplied atom laws, or entropy assumptions. -/
theorem actual_multiscale_tendsto_zero_of_fixed_vector (A K C b : ℝ) (a : ℕ)
    (hA : 0 < A) (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b)
    (hfixed : ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ u : Fin n → ℝ, coefficientMass u = 1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
            C*(n+1)^a*Real.exp (-b*(d:ℝ)^2/Real.log d))
    (n : ℕ → ℕ) (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (2*(d/4)) (2*(d/4))).real
      (actualMultiscaleBad d (n d) K)) atTop (nhds 0) := by
  have hsp : Tendsto (fun d : ℕ => Real.exp (-(d:ℝ)/2048)) atTop (nhds 0) := by
    have hh : Tendsto (fun d : ℕ => (d:ℝ)/2048) atTop atTop := by
      simpa only [div_eq_mul_inv, mul_comm] using
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop).const_mul_atTop
          (by norm_num : (0:ℝ)<(2048:ℝ)⁻¹)
    simpa only [neg_div] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp hh
  have hlim := (hsp.add (atomFailureBound_tendsto_zero A)).add
    (multiscale_exponential_tendsto_zero (b/2) (by positivity))
  simp only [zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hlim
  have hB : 1 ≤ 1+8/multiscaleFixedConstant K := by
    linarith [div_pos (by norm_num : (0:ℝ)<8) (multiscaleFixedConstant_pos K)]
  have hent := eventually_multiscale_net_tail A K (1+8/multiscaleFixedConstant K) C b a hA hK hB hC hb
  filter_upwards [hn, hfixed, hent, eventually_ge_atTop (max 24 (sparseEntropyCutoff A))]
    with d hnd hfd hed hd
  apply (actual_multiscale_uniform_probability_le A K hA hK d (n d) hd hnd
    (C*(n d+1)^a*Real.exp (-b*(d:ℝ)^2/Real.log d)) (by positivity)
      (hfd (n d) hnd)).trans
  exact add_le_add_right (hed (n d) ⌊K*d⌋₊ hnd (Nat.floor_le (by positivity))) _

end GaussianEllipsoidCandidate
