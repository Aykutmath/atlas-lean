import ActualFixedVectorTail
import PaperLogarithmicDepth

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

theorem common_retained_tail_constants_flexible (K J : ℝ) (hK : 1 ≤ K)
    (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K))
    (T : ℕ) (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37) :
    let ε := 8*(1/2:ℝ)^(T)
    let c := (1/2:ℝ)^24/(Real.sqrt K*J)
    ε ≤ 1/8 ∧ 2*ε ≤ c/8 ∧
      3*c/4 ≤ c*(1-ε)-2*ε ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ 3*c/4 ∧
      ((1/2:ℝ)^29)/(Real.sqrt K*(1+Real.log K)) ≤ c*(1-ε)-2*ε := by
  dsimp only
  let ε := 8*(1/2:ℝ)^(T)
  let c := (1/2:ℝ)^24/(Real.sqrt K*J)
  let D := Real.sqrt K*(1+Real.log K)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hD := target_denominator_bounds K hK
  change ε*K^2 ≤ (1/2:ℝ)^37 at hscale
  have hεsmall : ε ≤ (1/2:ℝ)^37 := by
    have hsq : 1 ≤ K^2 := by nlinarith
    nlinarith
  have hεeighth : ε ≤ 1/8 := by norm_num at hεsmall ⊢; linarith
  have hJpos : 0 < Real.sqrt K*J := mul_pos hsK hJ
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hdenom : Real.sqrt K*J ≤ 17*D := by
    have hm := mul_le_mul_of_nonneg_left hJup hsK.le
    dsimp [D]
    nlinarith
  have hdenomK : Real.sqrt K*J ≤ 17*K^2 := by
    dsimp [D] at hdenom
    linarith [hD.2]
  have hcdenom : c*(Real.sqrt K*J) = (1/2:ℝ)^24 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hJpos.ne'
  have hsmall : 16*ε*(Real.sqrt K*J) ≤ (1/2:ℝ)^24 := by
    have he := mul_le_mul_of_nonneg_left hdenomK (by positivity : 0 ≤ 16*ε)
    have hnum : 16*ε*(Real.sqrt K*J) ≤ 272*(1/2:ℝ)^37 := by nlinarith
    have hconst : 272*(1/2:ℝ)^37 ≤ (1/2:ℝ)^24 := by norm_num
    exact hnum.trans hconst
  have habsorb : 2*ε ≤ c/8 := by nlinarith
  have hret : 3*c/4 ≤ c*(1-ε)-2*ε := by nlinarith
  have hfix : ((1/2:ℝ)^29)/D ≤ 3*c/4 := by
    apply (div_le_iff₀ hD.1).2
    have hcD : (1/2:ℝ)^24 ≤ c*(17*D) := by
      rw [← hcdenom]
      exact mul_le_mul_of_nonneg_left hdenom hc0.le
    have hconst : (1/2:ℝ)^29*68 ≤ 3*(1/2:ℝ)^24 := by norm_num
    nlinarith
  exact ⟨hεeighth, habsorb, hret, hfix, hfix.trans hret⟩


theorem actual_late_group_count_le_flexible {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ))
    (K d : ℝ) (hK : 1 ≤ K) (hd : 0 < d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card : ℝ) ≤ K*d)
    (T : ℕ) (hT0 : 0 < T) (hTcap : (T:ℝ) ≤ 48*K)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (q : ℕ) (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q) :
    ((groups.length-q : ℕ) : ℝ) ≤ 17*(1+Real.log K) := by
  classical
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT0
  refine late_group_count_le (dyadicGroupScale u amp groups) groups.length q K d T
    hq.1 hK hd hTpos ?_ (actual_group_doubling u amp groups T hreg hchain) ?_ ?_
  · exact hTcap
  · intro r hqr hr
    have hh := record_scale_after_cutoff (dyadicGroupScale u amp groups)
      (dyadicGroupSize u amp groups T) groups.length q T (d/256) hTpos
      (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).1.le)
      (actual_group_doubling u amp groups T hreg hchain)
      (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).2.2.1)
      hq r hqr hr
    convert hh using 1 <;> ring
  · intro r hr
    exact (actual_group_scale_le_support u amp ha groups r).trans hsupp


theorem actual_original_late_fixed_smallball_flexible {n d : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ))
    (K : ℝ) (hK : 1 ≤ K) (T : ℕ) (hT0 : 0 < T) (hTcap : (T:ℝ) ≤ 48*K)
    (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (hd : 65536*(T:ℝ) ≤ d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T)
    (hcapt : (∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) <
        multiscaleFixedConstant K * Real.sqrt d} ≤
      Real.exp (-(d:ℝ)^2/(1048576*T)) := by
  let J := 17*(1+Real.log K)
  let ε := 8*(1/2:ℝ)^T
  let c := (1/2:ℝ)^24 / (Real.sqrt K*J)
  let M := coefficientMass (retainedGroupVector u amp groups T)
  have hTpos : 0 < T := hT0
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hJ : 0 < J := by dsimp [J]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hconstants := common_retained_tail_constants_flexible K J hK hJ (by rfl) T hscale
  change ε ≤ 1/8 ∧ 2*ε ≤ c/8 ∧ 3*c/4 ≤ c*(1-ε)-2*ε ∧
    (1/2:ℝ)^29/(Real.sqrt K*(1+Real.log K)) ≤ 3*c/4 ∧
    (1/2:ℝ)^29/(Real.sqrt K*(1+Real.log K)) ≤ c*(1-ε)-2*ε at hconstants
  have hM : 1-ε ≤ M := retained_mass_ge_one_sub u amp groups T ε hu herr
  have hMpos : 0 < M := by linarith [hconstants.1]
  have hdpos : (0:ℝ) < d := by
    have hTr : (0:ℝ) < T := by exact_mod_cast hTpos
    linarith
  have hcount := actual_late_group_count_le_flexible u amp ha groups K d hK hdpos hsupp T hT0 hTcap hreg hchain q hq
  have hp := actual_original_late_smallball u amp ha groups T hTpos hreg hchain hflat
    K J hK hJ hd hsupp q hq hcount hMpos hcapt
  have hthreshold : multiscaleFixedConstant K * Real.sqrt d ≤ c * Real.sqrt d * M := by
    have hf : multiscaleFixedConstant K ≤ c*M := by
      unfold multiscaleFixedConstant
      rw [max_eq_left hK]
      have hh := mul_le_mul_of_nonneg_left hM hc.le
      linarith [hconstants.2.2.2.2]
    convert! mul_le_mul_of_nonneg_right hf (Real.sqrt_nonneg (d:ℝ)) using 1 <;> ring
  apply (measureReal_mono (fun X (hX : _ < _) => hX.trans_le hthreshold)).trans
  simpa only [c, show (1/2:ℝ)^24 = 1/16777216 by norm_num, M] using! hp


theorem actual_fixed_failure_subset_retained_flexible {n d h : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (groups : List (List ℕ))
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K))
    (T : ℕ) (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T) :
    {X : Fin n → Euclid h × Euclid h |
      scaledBilinearNuclear d u X < multiscaleFixedConstant K * Real.sqrt d} ∩ atomRowsGood d n h ⊆
    {X | scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
      ((1/2:ℝ)^24/(Real.sqrt K*J))*Real.sqrt d*
        coefficientMass (retainedGroupVector u amp groups T)} := by
  let V := retainedGroupVector u amp groups T
  let M := coefficientMass V
  let ε := 8*(1/2:ℝ)^T
  let c := (1/2:ℝ)^24/(Real.sqrt K*J)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hc : 0 < c := by dsimp [c]; positivity
  have hconstants := common_retained_tail_constants_flexible K J hK hJ hJup T hscale
  have hfinal : multiscaleFixedConstant K ≤ c*(1-ε)-2*ε := by
    unfold multiscaleFixedConstant
    rw [max_eq_left hK]
    exact hconstants.2.2.2.2
  have hM : 1-ε ≤ M := retained_mass_ge_one_sub u amp groups T ε hu herr
  rintro X ⟨hbad, hatom⟩
  have herror : scaledBilinearNuclear d (u-V) X ≤ Real.sqrt d*ε :=
    (scaledBilinearNuclear_le_mass hatom (u-V)).trans
      (mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _))
  have htri := scaledBilinearNuclear_sub_le (d:=d) u V X
  have hscale : multiscaleFixedConstant K*Real.sqrt d + Real.sqrt d*ε ≤ c*Real.sqrt d*M := by
    have h1 := mul_le_mul_of_nonneg_right hfinal (Real.sqrt_nonneg (d:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hM hc.le
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (d:ℝ))
    nlinarith [mul_nonneg hε (Real.sqrt_nonneg (d:ℝ))]
  exact lt_of_le_of_lt htri ((add_lt_add_of_lt_of_le hbad herror).trans_le hscale)


theorem actual_fixed_captured_failure_subset_flexible {n d : ℕ} (hd : 24 ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 1 ≤ J) (hJup : J ≤ 17*(1+Real.log K))
    (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) :
    ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
      sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ⊆
    actualCapturedProjectionBad u amp ha groups T d p q hreg hflat ∪
      {X | actualCapturedCross u amp ha groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} := by
  rintro X ⟨⟨hbad, hsp⟩, hatom⟩
  by_cases hp : X ∈ actualCapturedProjectionBad u amp ha groups T d p q hreg hflat
  · exact Or.inl hp
  · right
    by_contra hcross
    have hgood := actual_captured_retained_lower hd u amp ha groups T p q hreg hflat hpq hq
      hbudget K J hK hJ hcapt X hsp hp (le_of_not_ge hcross)
    have hret := actual_fixed_failure_subset_retained_flexible u hu amp groups K J hK (by linarith)
      hJup T hscale herr ⟨hbad, hatom⟩
    exact (not_lt_of_ge hgood) hret


theorem actual_fixed_vector_tail_logarithmic_depth {n d : ℕ} (K : ℝ) (hK : 1 ≤ K)
    (hd24 : 24 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hfloor : (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ))
    (hbudget : (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ≤ (d:ℝ)/256)
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*((depth K:ℕ):ℝ)*Real.log (d:ℝ)))
    (hlate : 65536*((depth K:ℕ):ℝ) ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
        sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
      (n+1:ℝ)*Real.exp (-(d:ℝ)^2/((2:ℝ)^67*((depth K:ℕ):ℝ)*Real.log (d:ℝ))) := by
  let T : ℕ := depth K
  let J : ℝ := 17*(1+Real.log K)
  let E : ℝ := Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ)))
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hT : 0 < T := depth_pos K hK
  have hTcap : (T:ℝ) ≤ 48*K := depth_le_linear K hK
  have hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37 := retention_error_scaled_logarithmic K hK
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hJ : 1 ≤ J := by dsimp [J]; linarith [Real.log_nonneg hK]
  have hcap : ∀ i, |u i| ≤ 1 := by
    intro i
    rw [← hu]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)
  obtain ⟨N, groups, p, q, hN, hcover, hempty, hflat0, hreg, hchain, herr,
    hpq, hp, hq, hpost, hcapR, hlateS⟩ :=
    exists_constructed_cutoff_geometry u 1 (by norm_num) hcap T hT d hd hlog0 hfloor hbudget
  rw [hu, mul_one] at herr
  have hflat := actual_constructor_flatten_nodup u 1 groups N hflat0
  have hsp : supportCut (dyadicGroupSupport u 1 groups T) p ≤ sparseSupportSize d := by
    have hh : (supportCut (dyadicGroupSupport u 1 groups T) p : ℝ) ≤ (sparseSupportSize d:ℝ) := by
      rw [actual_dyadic_supportCut_cast]
      exact hp.2.1
    exact_mod_cast hh
  have hM0 := common_retained_tail_constants_flexible K J hK (by linarith) (by rfl) T hscale
  have hMpos : 0 < coefficientMass (retainedGroupVector u 1 groups T) := by
    have hh := retained_mass_ge_one_sub u 1 groups T (8*(1/2:ℝ)^T) hu herr
    change 8*(1/2:ℝ)^T ≤ 1/8 ∧ _ at hM0
    linarith [hM0.1]
  have hambient : (d:ℝ)/3 ≤ ((2*(d/4):ℕ):ℝ) := by
    have hh : d ≤ 3*(2*(d/4)) := by omega
    have hh' : (d:ℝ) ≤ 3*((2*(d/4):ℕ):ℝ) := by exact_mod_cast hh
    linarith
  have hE : 0 ≤ E := Real.exp_nonneg _
  by_cases hcapt : coefficientMass (retainedGroupVector u 1 groups T)/2 ≤
      ∑ r ∈ Finset.range q, dyadicGroupMass u 1 groups T r
  · have hsub := actual_fixed_captured_failure_subset_flexible hd24 u hu 1 (by norm_num) groups T p q
      hreg hflat hpq hq.1 hsp K J hK hJ (by rfl) hscale herr hcapt
    have hprojected := actualCapturedProjectionBad_probability
      u 1 (by norm_num) groups T hT hreg hchain hflat p q hp hq
      (show 0 < d by omega) hambient hfloor hnum
    have hcross := actualCapturedCross_lower_tail u 1 (by norm_num) groups T p q hT hreg hflat
      hd hlog0 (fun r hpr hr => (hpost r hpr hr).1) hMpos
    have hprojCommon : (groups.length:ℝ)*Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log (d:ℝ))) ≤
        (n:ℝ)*E := by
      apply mul_le_mul
      · exact_mod_cast actual_group_count_le_ambient u 1 (by norm_num) groups T hreg hflat
      · exact projected_tail_le_common d T hd.le hTr hlog0
      · exact Real.exp_nonneg _
      · positivity
    calc
      _ ≤ _ := measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ (groups.length:ℝ)*Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log (d:ℝ))) + E :=
        add_le_add hprojected hcross
      _ ≤ (n:ℝ)*E+E := add_le_add_left hprojCommon E
      _ = _ := by dsimp [E,T]; push_cast; ring
  · have hlateProb := actual_original_late_fixed_smallball_flexible u hu 1 (by norm_num) groups K hK T hT hTcap hscale
      hreg hchain hflat hlate hsupp q hq herr (lt_of_not_ge hcapt)
    calc
      _ ≤ (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
          {X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} :=
        measureReal_mono (fun X hX => hX.1.1)
      _ ≤ Real.exp (-(d:ℝ)^2/(1048576*T)) := hlateProb
      _ ≤ E := late_tail_le_common d T hd.le hTr hlog
      _ ≤ (n+1:ℝ)*E := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hE]


#print axioms actual_fixed_vector_tail_logarithmic_depth
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
