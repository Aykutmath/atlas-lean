import PaperFullHalfLogDepth

noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory Filter GaussianMixedNormHelpers GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators InnerProductSpace Topology
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

/-- The internal retained-vector tail uses the literal sparse event and needs no
atom event. The statement holds for every actual retained decomposition satisfying
the source record and cutoff properties, in particular at amplitude `‖u‖`. -/
theorem paper_retained_tail_literal_sparse {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 < amp)
    (groups : List (List ℕ)) (T p q : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 1 ≤ J)
    (hfull : 2*(d/4) ≤ h) (hd24 : 24 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hfloor : (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ))
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*T*Real.log (d:ℝ)))
    (hlate : 65536*(T:ℝ) ≤ d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (hpq : p ≤ q)
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) p)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (hsp : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (hS : ∀ j, p ≤ j → j < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hcount : ((groups.length-q:ℕ):ℝ) ≤ J)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T)) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      ({X | scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
        (1/2:ℝ)^24/(Real.sqrt K*J)*Real.sqrt d*
          coefficientMass (retainedGroupVector u amp groups T)} ∩ paperSparseSingularGood d n h) ≤
      (n+1:ℝ)*Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ))) := by
  let E : ℝ := Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ)))
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hambient : (d:ℝ)/3 ≤ (h:ℝ) := by
    have hn : d ≤ 3*(2*(d/4)) := by omega
    have hr : (d:ℝ) ≤ 3*((2*(d/4):ℕ):ℝ) := by exact_mod_cast hn
    have hh : ((2*(d/4):ℕ):ℝ) ≤ (h:ℝ) := Nat.cast_le.mpr hfull
    linarith
  have hE : 0 ≤ E := Real.exp_nonneg _
  by_cases hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ r ∈ range q,dyadicGroupMass u amp groups T r
  · have hsub : ({X : Fin n → Euclid h × Euclid h |
        scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
          (1/2:ℝ)^24/(Real.sqrt K*J)*Real.sqrt d*
            coefficientMass (retainedGroupVector u amp groups T)} ∩ paperSparseSingularGood d n h) ⊆
      actualCapturedProjectionBad u amp ha.le groups T d p q hreg hflat ∪
      {X | actualExactCapturedCross u amp ha.le groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} := by
      rintro X ⟨hbad,hgood⟩
      by_cases hx : X ∈ actualCapturedProjectionBad u amp ha.le groups T d p q hreg hflat
      · exact Or.inl hx
      · right
        by_contra hc
        have hl := actual_captured_retained_lower_literal_sparse u amp ha.le groups T p q hreg hflat
          hpq hq.1 hsp hcapt X hgood hx (le_of_not_ge hc)
        have hsK : 1 ≤ Real.sqrt K := by simpa using Real.sqrt_le_sqrt hK
        have hden : 1 ≤ Real.sqrt K*J := one_le_mul_of_one_le_of_one_le hsK hJ
        have hcoef := div_le_self (show (0:ℝ) ≤ (1/2:ℝ)^24 by positivity) hden
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (d:ℝ))) hM.le
        exact (not_lt_of_ge hl) (hbad.trans_le ht)
    have hprojected := actualCapturedProjectionBad_probability u amp ha.le groups T hT hreg hchain hflat
      p q hp hq (show 0 < d by omega) hambient hfloor hnum
    have hcross := actualExactCapturedCross_common_tail (h:=h) u amp ha.le groups T p q hT hreg hflat hchain
      hd hlog hS hM
    have hprojCommon : (groups.length:ℝ)*Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log (d:ℝ))) ≤
        (n:ℝ)*E := by
      apply mul_le_mul
      · exact_mod_cast actual_group_count_le_ambient u amp ha.le groups T hreg hflat
      · exact projected_tail_le_common d T hd.le hTr hlog0
      · exact Real.exp_nonneg _
      · positivity
    calc
      _ ≤ _ := measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ (groups.length:ℝ)*Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log (d:ℝ)))+E :=
        add_le_add hprojected hcross
      _ ≤ (n:ℝ)*E+E := add_le_add_left hprojCommon E
      _ = _ := by dsimp [E]; push_cast; ring
  · have hl := actual_retained_late_smallball u amp ha groups T hT hreg hchain hflat K J hK
      (by linarith) hlate hsupp q hq hcount hM (lt_of_not_ge hcapt)
    have hl' : (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
        {X | scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
          (1/2:ℝ)^24/(Real.sqrt K*J)*Real.sqrt d*coefficientMass (retainedGroupVector u amp groups T)} ≤
        Real.exp (-(d:ℝ)^2/(1048576*T)) := by
      convert hl using 1 <;> norm_num [scaledBilinearNuclear]
    have hprob := (fixed_bilinear_bad_probability_mono hfull d (retainedGroupVector u amp groups T)
      ((1/2:ℝ)^24/(Real.sqrt K*J)*Real.sqrt d*coefficientMass (retainedGroupVector u amp groups T))).trans hl'
    calc
      _ ≤ _ := measureReal_mono (Set.inter_subset_left)
      _ ≤ Real.exp (-(d:ℝ)^2/(1048576*T)) := hprob
      _ ≤ E := late_tail_le_common d T hd.le hTr hlog
      _ ≤ (n+1:ℝ)*E := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hE]


/-- Actual source-amplitude construction, with its retained vector and literal
full-half sparse-guard probability shown together. -/
theorem exists_source_retained_logarithmic_tail {n d : ℕ} (K : ℝ) (hK : 1 ≤ K)
    (hd24 : 24 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hfloor : (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ))
    (hbudget : (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ≤ (d:ℝ)/256)
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*((depth K:ℕ):ℝ)*Real.log (d:ℝ)))
    (hlate : 65536*((depth K:ℕ):ℝ) ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u=1)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d) :
    ∃ (N : ℕ) (groups : List (List ℕ)),
      0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u ‖u‖ t) ∧
      (∀ t, N ≤ t → dyadicBin u ‖u‖ t=∅) ∧
      groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
      (∀ g ∈ groups, RegularRetainedGroup u ‖u‖ (depth K) g) ∧
      groups.IsChain (RecordSuccessor fun t => (dyadicBin u ‖u‖ t).card) ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups (depth K)) ≤ 8*(1/2:ℝ)^(depth K) ∧
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups (depth K)) X <
          (1/2:ℝ)^24/(Real.sqrt K*(17*(1+Real.log K)))*Real.sqrt d*
            coefficientMass (retainedGroupVector u ‖u‖ groups (depth K))} ∩
          paperSparseSingularGood d n (d/2)) ≤
        (n+1:ℝ)*Real.exp (-(d:ℝ)^2/((2:ℝ)^67*((depth K:ℕ):ℝ)*Real.log (d:ℝ))) := by
  let T := depth K
  let J : ℝ := 17*(1+Real.log K)
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hT : 0 < T := depth_pos K hK
  have hTcap : (T:ℝ) ≤ 48*K := depth_le_linear K hK
  have hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37 := retention_error_scaled_logarithmic K hK
  have hJ : 1 ≤ J := by dsimp [J]; linarith [Real.log_nonneg hK]
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz, coefficientMass] at hu
  have hamp : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hcap : ∀ i, |u i| ≤ ‖u‖ := fun i => by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  obtain ⟨N,groups,p,q,hN,hcover,hempty,hflat0,hreg,hchain,herr,hpq,hp,hq,hpost,hcapR,hlateS⟩ :=
    exists_constructed_cutoff_geometry u ‖u‖ hamp hcap T hT d hd hlog0 hfloor hbudget
  rw [hu,mul_one] at herr
  have hflat := actual_constructor_flatten_nodup u ‖u‖ groups N hflat0
  have hsp : supportCut (dyadicGroupSupport u ‖u‖ groups T) p ≤ sparseSupportSize d := by
    have hh : (supportCut (dyadicGroupSupport u ‖u‖ groups T) p:ℝ) ≤ (sparseSupportSize d:ℝ) := by
      rw [actual_dyadic_supportCut_cast]
      exact hp.2.1
    exact_mod_cast hh
  have hM0 := common_retained_tail_constants_flexible K J hK (by linarith) (by rfl) T hscale
  have hMpos : 0 < coefficientMass (retainedGroupVector u ‖u‖ groups T) := by
    have hh := retained_mass_ge_one_sub u ‖u‖ groups T (8*(1/2:ℝ)^T) hu herr
    change 8*(1/2:ℝ)^T ≤ 1/8 ∧ _ at hM0
    linarith [hM0.1]
  have hcount := actual_late_group_count_le_flexible u ‖u‖ hamp groups K d hK hd hsupp T hT hTcap
    hreg hchain q hq
  have hprob := paper_retained_tail_literal_sparse u ‖u‖ hamp groups T p q hT hreg hflat hchain K J hK hJ
    (show 2*(d/4) ≤ d/2 by omega) hd24 hlog hfloor hnum hlate hsupp hpq hp hq hsp
    (fun j hj hj' => (hpost j hj hj').1) hcount hMpos
  exact ⟨N,groups,hN,hcover,hempty,hflat0,hreg,hchain,herr,hprob⟩


/-- Source retained-vector statement with the displayed logarithmic prefactor. -/
theorem paper_source_retained_logarithmic_tail (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      ∃ (N : ℕ) (groups : List (List ℕ)),
        0 < N ∧
        (∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u ‖u‖ t) ∧
        (∀ t, N ≤ t → dyadicBin u ‖u‖ t=∅) ∧
        groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
        (∀ g ∈ groups, RegularRetainedGroup u ‖u‖ (depth K) g) ∧
        groups.IsChain (RecordSuccessor fun t => (dyadicBin u ‖u‖ t).card) ∧
        coefficientMass (u-retainedGroupVector u ‖u‖ groups (depth K)) ≤ 8*(1/2:ℝ)^(depth K) ∧
        (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
          ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups (depth K)) X <
            (1/2:ℝ)^24/(Real.sqrt K*(17*(1+Real.log K)))*Real.sqrt d*
              coefficientMass (retainedGroupVector u ‖u‖ groups (depth K))} ∩
            paperSparseSingularGood d n (d/2)) ≤
          Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  let T := depth K
  have hT : 0 < T := depth_pos K hK
  let C : ℝ := (2:ℝ)^67*T
  have hC : 0 < C := by dsimp [C]; positivity
  let c : ℝ := 1/(2*C)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ d : ℕ in atTop, 48*C^3*(A+1) ≤ (d:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp
    ((eventually_natural_cutoff_thresholds T hT).and (hlog.and (hlarge.and (eventually_ge_atTop 24))))
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn u hu hs
  obtain ⟨hcut,hlogd,hlargeD,hd24⟩ := hd₀ d hd
  obtain ⟨N,groups,hN,hcover,hempty,hflat,hreg,hchain,herr,hprob⟩ :=
    exists_source_retained_logarithmic_tail K hK hd24 hlogd hcut.2.2.1 hcut.2.2.2.1
      hcut.2.2.2.2.1 hcut.2.2.2.2.2 u hu hs
  refine ⟨N,groups,hN,hcover,hempty,hflat,hreg,hchain,herr,?_⟩
  have hp := paper_logarithmic_prefactor hA.le hC
    (show (1:ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega)) hlogd hn hlargeD
  have hh := hprob.trans hp
  apply hh.trans_eq
  congr 2
  dsimp [c]
  ring

end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_retained_tail_literal_sparse

#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.exists_source_retained_logarithmic_tail

#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_source_retained_logarithmic_tail
