import PaperNuisanceNet
import PaperL1Entropy
import PaperL1Continuum
import UCGaussianFreeEnergyFloor
import UCDiffuseFiniteModel
import UCDiffuseParameters

/-! Actual diffuse continuum tail: all covers, comparison estimates,
concentration, and continuity inputs are proved. The Gaussian loss good event
is the concrete event supplied by the completed compact escape chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Module BMClippedL1Bridge
open scoped BigOperators
namespace GaussianEllipsoid.PaperDiffuseActualBound
open UCContinuityGeometry UCUniformContinuity UCDiffuseNets UCDiffuseFiniteModel
open UCDiffuseParameters UCRationalLoss UCContinuumTransfer UCFiniteMarginAssembly

 def diffuseBad (d n : ℕ) (τ B c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (Sample d n) :=
  {x | ∃ A ∈ sourceDiffuseClass d τ, ∃ v : EuclideanSpace ℝ (Fin n),
    v ∈ L ∧ ∑ i, |v i| ≤ B*n ∧ (1/(n:ℝ))*∑ i, |measurementQ x A i-v i| < c}

/-- Every remaining premise is either a fixed numerical parameter budget or
the concrete Gaussian good event. In particular no net, one-row comparison,
concentration, or continuity proposition remains as a premise. -/
theorem diffuse_tail_of_gaussian_good_event {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (haspect : (1/4:ℝ)*(d:ℝ)^2 ≤ n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (B η r s β τ : ℝ) (hB : 0 ≤ B) (hη : 0 < η)
    (hr : 0 < r) (hs : 0 < s) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (hmesh : continuityConstant (1/4)*r+s ≤ 3*η/16)
    (hβEnt : PaperL1Entropy.entropyConstant r B s ≤ (η/16)*β)
    (hsmall : normalizedComparisonConstant β hβ.le*τ ≤ η/16)
    (G : Set (Fin n → (Fin (d*d) → ℝ))) (hG : MeasurableSet G)
    (hp : (Measure.pi (fun _ : Fin n => GaussianTensorMoments.gaussianProductLaw (Fin (d*d)))).real Gᶜ ≤ 1/16)
    (hGfloor : ∀ z ∈ G, ∀ A : Square d, A.PosSemidef → frobeniusNorm A = 1 →
      ∀ v : EuclideanSpace ℝ (Fin n), v ∈ L → η ≤
        (∑ i, smoothLoss (UCNormalizedRows.gaussianRow A (z i)-v i))/(n:ℝ)) :
    (gaussianSampleLaw d n).real (diffuseBad d n τ B (η/2) L) ≤
      Real.exp (-(n:ℝ))+Real.exp (-(n:ℝ)*η^2/128) := by
  classical
  by_cases hne : (sourceDiffuseClass d τ).Nonempty
  swap
  · have he : diffuseBad d n τ B (η/2) L = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨A,hA,_⟩
      exact hne ⟨A,hA⟩
    rw [he,measureReal_empty]
    positivity
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨sn, hsn, hscard, hscover⟩ := exists_diffuse_net d τ r hr
    obtain ⟨tn, htn, htcard, htcover⟩ := PaperNuisanceNet.exists_intrinsic_l1_net (n+1) hn L B s hB hs
    obtain ⟨A0,hA0⟩ := (source_diffuse_nonempty_iff d τ).mp hne
    obtain ⟨S0,hS0,_⟩ := hscover A0 hA0
    have hsne : sn.Nonempty := ⟨S0,hS0⟩
    have hz : ∑ i : Fin (n+1), |(0 : EuclideanSpace ℝ (Fin (n+1))) i| ≤ B*(n+1:ℕ) := by simp; positivity
    obtain ⟨v0,hv0,_⟩ := htcover 0 L.zero_mem hz
    have htne : tn.Nonempty := ⟨v0,hv0⟩
    letI : Nonempty ↥sn := ⟨⟨S0,hS0⟩⟩
    letI : Nonempty ↥tn := ⟨⟨v0,hv0⟩⟩
    let κ := ↥sn × ↥tn
    let Ac : κ → Square d := fun k => matrix k.1.val
    let vc : κ → EuclideanSpace ℝ (Fin (n+1)) := fun k => k.2.val
    have hAc (k : κ) : (Ac k).PosSemidef ∧ (Ac k).transpose = Ac k ∧
        frobeniusNorm (Ac k) = 1 ∧ matrixOpNorm (Ac k) ≤ τ :=
      candidate_matrix_conditions sn hsn k.1
    have hvc (k : κ) : vc k ∈ L := (htn k.2.val k.2.property).1
    have hcκ : Fintype.card κ = sn.card*tn.card := by simp [κ]
    have hEnt : Real.log (Fintype.card κ:ℝ) ≤ (η/16)*β*(n+1:ℕ) := by
      rw [hcκ]
      have h := PaperL1Entropy.combined_entropy hr hB hs L haspect
        sn.card tn.card hsne.card_pos htne.card_pos hscard htcard
      exact h.trans (mul_le_mul_of_nonneg_right hβEnt (by positivity))
    have hGmean := UCGaussianFreeEnergyFloor.gaussian_freeEnergy_mean_floor β η hβ hη.le hd hn Ac vc G hG hp
      (fun z hz k => hGfloor z hz (Ac k) (hAc k).1 (hAc k).2.2.1 (vc k) (hvc k))
    have hfinite := finite_loss_margin_tail β η τ hβ hη hτ Ac
      (fun k => (hAc k).2.1) hd (fun k => (hAc k).2.2.2) (fun k => (hAc k).2.2.1.le)
      n vc hEnt hsmall hGmean
    have hsub : diffuseBad d (n+1) τ B (η/2) L ⊆
        {x | continuityConstant (1/4) < ‖empiricalOperator x‖} ∪
        {x | ∃ k : κ, meanLoss x (Ac k) (vc k) < 11*η/16} := by
      intro x hx
      obtain ⟨A,hA,v,hv,hvB,hbad⟩ := hx
      by_cases hC : continuityConstant (1/4) < ‖empiricalOperator x‖
      · exact Or.inl hC
      · have hC' := le_of_not_gt hC
        let A' := ofMatrix A (psd_transpose hA.1)
        obtain ⟨S,hS,hAS⟩ := hscover A' (ofMatrix_mem_diffuse hA)
        obtain ⟨w,hw,hvw⟩ := htcover v hv hvB
        let k : κ := (⟨S,hS⟩,⟨w,hw⟩)
        have hmat : frobeniusNorm (A-Ac k) ≤ r := by
          change frobeniusNorm (A-matrix S) ≤ r
          have he : frobeniusNorm (A-matrix S) = ‖A'-S‖ := by
            rw [← frobenius_matrix_sub, matrix_ofMatrix]
          rw [he]
          exact hAS.le
        have hnR : (0:ℝ) < (n+1:ℕ) := by positivity
        have hvmean : (1/((n+1:ℕ):ℝ))*∑ i, |v i-vc k i| ≤ s := by
          change (1/((n+1:ℕ):ℝ))*∑ i, |v i-w i| ≤ s
          have hh := (div_le_iff₀ hnR).mpr hvw.le
          simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
        have herr := (abs_le.mp (meanLoss_abs_sub_l1_le hn x A (Ac k)
          (psd_transpose hA.1) (hAc k).2.1 v (vc k) (continuityConstant (1/4)) hC')).1
        have hcont0 : 0 ≤ continuityConstant (1/4) := (continuityConstant_pos (by norm_num)).le
        have he := add_le_add (mul_le_mul_of_nonneg_left hmat hcont0) hvmean
        have hb := (meanLoss_le_abs x A v).trans_lt hbad
        refine Or.inr ⟨k, ?_⟩
        linarith
    have hcont := empiricalOperator_tail (a := 1/4) (by norm_num) hd hn haspect
    calc
      _ ≤ (gaussianSampleLaw d (n+1)).real
          ({x | continuityConstant (1/4) < ‖empiricalOperator x‖} ∪
            {x | ∃ k : κ, meanLoss x (Ac k) (vc k) < 11*η/16}) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (gaussianSampleLaw d (n+1)).real {x | continuityConstant (1/4) < ‖empiricalOperator x‖} +
          (gaussianSampleLaw d (n+1)).real {x | ∃ k : κ, meanLoss x (Ac k) (vc k) < 11*η/16} :=
        measureReal_union_le _ _
      _ ≤ _ := add_le_add hcont hfinite

#print axioms diffuse_tail_of_gaussian_good_event
end GaussianEllipsoid.PaperDiffuseActualBound
