import UCGaussianFreeEnergyFloor
import UCDiffuseFiniteModel
import UCDiffuseParameters

/-! Actual diffuse continuum tail: all covers, comparison estimates,
concentration, and continuity inputs are proved. The Gaussian loss good event
is the concrete event supplied by the completed compact escape chain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Module BMClippedL1Bridge
open scoped BigOperators
namespace GaussianEllipsoid.UCDiffuseActualBound
open UCContinuityGeometry UCUniformContinuity UCDiffuseNets UCDiffuseFiniteModel
open UCDiffuseParameters UCRationalLoss UCContinuumTransfer UCFiniteMarginAssembly

 def diffuseBad (d n : ℕ) (τ B c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (Sample d n) :=
  {x | ∃ A ∈ sourceDiffuseClass d τ, ∃ v : EuclideanSpace ℝ (Fin n),
    v ∈ L ∧ ‖v‖ ≤ B*n ∧ (1/(n:ℝ))*∑ i, |measurementQ x A i-v i| < c}

/-- Every remaining premise is either a fixed numerical parameter budget or
the concrete Gaussian good event. In particular no net, one-row comparison,
concentration, or continuity proposition remains as a premise. -/
theorem diffuse_tail_of_gaussian_good_event {d n M : ℕ}
    (hd : 0 < d) (hn : 0 < n) (haspect : (1/4:ℝ)*(d:ℝ)^2 ≤ n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hL : finrank ℝ L ≤ M)
    (B η r s β τ : ℝ) (hB : 0 ≤ B) (hη : 0 < η)
    (hr : 0 < r) (hs : 0 < s) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (hmesh : continuityConstant (1/4)*r+s ≤ 3*η/16)
    (hβEnt : entropyConstant r ≤ (η/16)*β)
    (hsmall : normalizedComparisonConstant β hβ.le*τ ≤ η/16)
    (hNEnt : (M:ℝ)*Real.log (1+2*B*n/s) ≤ n)
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
    obtain ⟨tn, htn, htcard, htcover⟩ := exists_nuisance_net (n+1) M L hL B s hB hs
    obtain ⟨A0,hA0⟩ := (source_diffuse_nonempty_iff d τ).mp hne
    obtain ⟨S0,hS0,_⟩ := hscover A0 hA0
    have hsne : sn.Nonempty := ⟨S0,hS0⟩
    have hz : ‖(0:L)‖ ≤ B*(n+1:ℕ) := by simp; positivity
    obtain ⟨v0,hv0,_⟩ := htcover 0 hz
    have htne : tn.Nonempty := ⟨v0,hv0⟩
    letI : Nonempty ↥sn := ⟨⟨S0,hS0⟩⟩
    letI : Nonempty ↥tn := ⟨⟨v0,hv0⟩⟩
    let κ := ↥sn × ↥tn
    let Ac : κ → Square d := fun k => matrix k.1.val
    let vc : κ → EuclideanSpace ℝ (Fin (n+1)) := fun k => k.2.val.val
    have hAc (k : κ) : (Ac k).PosSemidef ∧ (Ac k).transpose = Ac k ∧
        frobeniusNorm (Ac k) = 1 ∧ matrixOpNorm (Ac k) ≤ τ :=
      candidate_matrix_conditions sn hsn k.1
    have hvc (k : κ) : vc k ∈ L := k.2.val.property
    have hcκ : Fintype.card κ = sn.card*tn.card := by simp [κ]
    have hEnt : Real.log (Fintype.card κ:ℝ) ≤ (η/16)*β*(n+1:ℕ) := by
      rw [hcκ]
      have h := combined_entropy (a := 1/4) (by norm_num) hr hB hs haspect
        sn.card tn.card hsne.card_pos htne.card_pos hscard htcard hNEnt
      have he : (Real.log (1+2/r)/(1/4)+1)*(n+1:ℕ) = entropyConstant r*(n+1:ℕ) := by
        unfold entropyConstant
        ring
      rw [he] at h
      exact h.trans (mul_le_mul_of_nonneg_right hβEnt (by positivity))
    have hGmean := UCGaussianFreeEnergyFloor.gaussian_freeEnergy_mean_floor β η hβ hη.le hd hn Ac vc G hG hp
      (fun z hz k => hGfloor z hz (Ac k) (hAc k).1 (hAc k).2.2.1 (vc k) (hvc k))
    have hfinite := finite_loss_margin_tail β η τ hβ hη hτ Ac
      (fun k => (hAc k).2.1) hd (fun k => (hAc k).2.2.2) (fun k => (hAc k).2.2.1.le)
      n vc hEnt hsmall hGmean
    let V : Set (EuclideanSpace ℝ (Fin (n+1))) := {v | v ∈ L ∧ ‖v‖ ≤ B*(n+1:ℕ)}
    have hcover : ∀ A ∈ sourceDiffuseClass d τ, ∀ v ∈ V,
        ∃ k : κ, frobeniusNorm (A-Ac k) ≤ r ∧ ‖v-vc k‖ ≤ s := by
      intro A hA v hv
      obtain ⟨k,hk1,hk2⟩ := joint_cover L sn tn hscover htcover A hA v hv.1 hv.2
      exact ⟨k,hk1.le,hk2.le⟩
    have hsub : diffuseBad d (n+1) τ B (η/2) L ⊆
        {x | continuityConstant (1/4) < ‖empiricalOperator x‖} ∪
        {x | ∃ k : κ, meanLoss x (Ac k) (vc k) < 11*η/16} := by
      intro x hx
      obtain ⟨A,hA,v,hv,hvB,hbad⟩ := hx
      apply continuum_bad_subset hn (fun A hA => psd_transpose hA.1) Ac
        (fun k => (hAc k).2.1) vc (continuityConstant (1/4)) r s η hη hcover hmesh
      exact ⟨A,hA,v,⟨hv,hvB⟩,hbad⟩
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
end GaussianEllipsoid.UCDiffuseActualBound
