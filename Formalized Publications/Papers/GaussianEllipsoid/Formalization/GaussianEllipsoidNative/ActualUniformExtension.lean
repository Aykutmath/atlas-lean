import ActualAtomEvent
import NuclearNormBounds

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- The paper's exact normalized nuclear observable, on ordered (b,a) rows. -/
def scaledBilinearNuclear {n h : ℕ} (d : ℕ) (u : Fin n → ℝ)
    (X : Fin n → Euclid h × Euclid h) : ℝ :=
  spectralNuclearNorm (operatorFrobenius
    ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))

theorem nuclearOperator_sum_le {ι : Type*} {r q : ℕ} (s : Finset ι)
    (T : ι → (Euclid q →L[ℝ] Euclid r)) :
    spectralNuclearNorm (operatorFrobenius (∑ i ∈ s, T i)) ≤
      ∑ i ∈ s, spectralNuclearNorm (operatorFrobenius (T i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz : operatorFrobenius (0 : Euclid q →L[ℝ] Euclid r) = 0 := by ext j i; rfl
    rw [hz, spectralNuclear_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, operatorFrobenius_add]
    exact (spectralNuclear_add_le _ _).trans (add_le_add_right ih _)

/-- On the actual atom event the synthesis is uniformly l1-Lipschitz. -/
theorem scaledBilinearNuclear_le_mass {d n h : ℕ}
    {X : Fin n → Euclid h × Euclid h} (hX : X ∈ atomRowsGood d n h)
    (u : Fin n → ℝ) : scaledBilinearNuclear d u X ≤ Real.sqrt d * coefficientMass u := by
  unfold scaledBilinearNuclear bilinearSynthesis
  rw [Finset.smul_sum]
  apply (nuclearOperator_sum_le Finset.univ _).trans
  calc
    _ = ∑ i, |u i| * spectralNuclearNorm (operatorFrobenius
      ((Real.sqrt (d:ℝ))⁻¹ • bilinearRowOperator (X i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_comm, operatorFrobenius_smul_eq, spectralNuclear_smul]
    _ ≤ ∑ i, |u i| * Real.sqrt d := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (atomRowsGood_row_bound hX i) (abs_nonneg _)
    _ = _ := by simp [coefficientMass, Finset.mul_sum, mul_comm]

theorem scaledBilinearNuclear_smul {d n h : ℕ} (t : ℝ) (u : Fin n → ℝ)
    (X : Fin n → Euclid h × Euclid h) :
    scaledBilinearNuclear d (t • u) X = |t| * scaledBilinearNuclear d u X := by
  have hs : bilinearSynthesis (t • u) X = t • bilinearSynthesis u X := by
    simp [bilinearSynthesis, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  unfold scaledBilinearNuclear
  rw [hs, smul_comm, operatorFrobenius_smul_eq, spectralNuclear_smul]

theorem scaledBilinearNuclear_sub_le {d n h : ℕ} (u v : Fin n → ℝ)
    (X : Fin n → Euclid h × Euclid h) :
    scaledBilinearNuclear d v X ≤ scaledBilinearNuclear d u X +
      scaledBilinearNuclear d (u-v) X := by
  have hs : bilinearSynthesis (u-v) X = bilinearSynthesis u X - bilinearSynthesis v X := by
    exact synthesis_sub (fun i => bilinearRowOperator (X i)) u v
  have hf : operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (u-v) X) =
      operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X) -
      operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis v X) := by
    rw [hs, smul_sub]
    ext j i
    rfl
  have hh := (abs_le.mp (abs_sub_spectralNuclear_le
    (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X))
    (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis v X)))).1
  unfold scaledBilinearNuclear
  rw [hf]
  linarith

/-- Deterministic extension with the requested factor-two loss. The atom event
actually supplies a stronger constant 1 rather than 2. -/
theorem actual_net_uniform_extension {d n h m : ℕ} {c : ℝ} (hc : 0 < c)
    (N : Finset (Fin n → ℝ))
    (hcover : ∀ u : Fin n → ℝ, coefficientMass u = 1 →
      (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m →
      ∃ v ∈ N, coefficientMass (u-v) < c/4)
    {X : Fin n → Euclid h × Euclid h} (hX : X ∈ atomRowsGood d n h)
    (hN : ∀ v ∈ N, c * Real.sqrt d ≤ scaledBilinearNuclear d v X)
    (u : Fin n → ℝ) (hu : (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m) :
    (c/2) * Real.sqrt d * coefficientMass u ≤ scaledBilinearNuclear d u X := by
  have hunit (w : Fin n → ℝ) (hw : coefficientMass w = 1)
      (hws : (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ m) :
      (c/2)*Real.sqrt d ≤ scaledBilinearNuclear d w X := by
    obtain ⟨v, hv, hdist⟩ := hcover w hw hws
    have he := (scaledBilinearNuclear_le_mass hX (w-v)).trans
      (mul_le_mul_of_nonneg_left hdist.le (Real.sqrt_nonneg _))
    have ht := scaledBilinearNuclear_sub_le (d:=d) w v X
    have hn := hN v hv
    nlinarith [Real.sqrt_nonneg (d:ℝ)]
  by_cases hz : coefficientMass u = 0
  · rw [hz, mul_zero]
    exact spectralNuclear_nonneg _
  · have hp : 0 < coefficientMass u :=
      lt_of_le_of_ne (coefficientMass_nonneg u) (Ne.symm hz)
    let w : Fin n → ℝ := (coefficientMass u)⁻¹ • u
    have hw : coefficientMass w = 1 := by
      rw [show w = (coefficientMass u)⁻¹ • u from rfl, coefficientMass_smul,
        abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hz]
    have hws : (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ m := by
      apply (Finset.card_le_card (show Finset.univ.filter (fun i => w i ≠ 0) ⊆
        Finset.univ.filter (fun i => u i ≠ 0) from ?_)).trans hu
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro hi0
      apply hi
      simp [w, Pi.smul_apply, hi0]
    have hh := hunit w hw hws
    rw [show w = (coefficientMass u)⁻¹ • u from rfl, scaledBilinearNuclear_smul,
      abs_of_pos (inv_pos.mpr hp), inv_mul_eq_div] at hh
    exact (le_div_iff₀ hp).mp hh

/-- No continuum union bound is used: genuine deterministic nets reduce the
actual uniform failure event to a finite union of actual fixed-vector failures. -/
theorem actual_uniform_failure_le_net {d n h m : ℕ} {c p : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p) (E : Set (Fin n → Euclid h × Euclid h))
    (hfixed : ∀ u : Fin n → ℝ, coefficientMass u = 1 →
      (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m →
      (gaussianBilinearSampleLaw (Fin n) h h).real
        ({X | scaledBilinearNuclear d u X < c*Real.sqrt d} ∩ E ∩ atomRowsGood d n h) ≤ p) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      ({X | ∃ u : Fin n → ℝ,
        (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m ∧
        scaledBilinearNuclear d u X < (c/2)*Real.sqrt d*coefficientMass u} ∩ E ∩ atomRowsGood d n h) ≤
      ((1+8/c)*(n+1))^m * p := by
  classical
  obtain ⟨N, hN, hcard, hcover⟩ := exists_sparse_coefficient_net n m (c/4) (by positivity)
  let F (u : Fin n → ℝ) :=
    {X | scaledBilinearNuclear d u X < c*Real.sqrt d} ∩ E ∩ atomRowsGood d n h
  have hsub : ({X | ∃ u : Fin n → ℝ,
      (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m ∧
      scaledBilinearNuclear d u X < (c/2)*Real.sqrt d*coefficientMass u} ∩ E ∩ atomRowsGood d n h)
        ⊆ ⋃ v ∈ N, F v := by
    rintro X ⟨⟨⟨u, hu, hbad⟩, hE⟩, hX⟩
    by_contra hnot
    have hlower : ∀ v ∈ N, c*Real.sqrt d ≤ scaledBilinearNuclear d v X := by
      intro v hv
      by_contra hvbad
      exact hnot (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, ⟨⟨lt_of_not_ge hvbad, hE⟩, hX⟩⟩⟩)
    exact (not_lt_of_ge (actual_net_uniform_extension hc N hcover hX hlower u hu)) hbad
  calc
    _ ≤ (gaussianBilinearSampleLaw (Fin n) h h).real (⋃ v ∈ N, F v) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ v ∈ N, (gaussianBilinearSampleLaw (Fin n) h h).real (F v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ N, p := Finset.sum_le_sum fun v hv => hfixed v (hN v hv).1 (hN v hv).2
    _ = (N.card:ℝ)*p := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hp
      convert hcard using 1 <;> congr 2 <;> field_simp <;> ring

end GaussianEllipsoidCandidate
