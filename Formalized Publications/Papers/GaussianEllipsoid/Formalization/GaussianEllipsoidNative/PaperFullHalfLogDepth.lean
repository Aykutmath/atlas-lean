import PaperExactPolarAggregation
import PaperFullHalfSparseDiagonal
import ActualRankAwareTail
import PaperFixedVectorLogPrefactor
import CanonicalDimensionCompression

noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory Filter GaussianMixedNormHelpers GaussianEllipsoid GaussianEllipsoid.SparseSupport
open GaussianEllipsoid.PaperCanonicalPolar
open scoped BigOperators InnerProductSpace Topology
namespace GaussianEllipsoidCandidate

/-- Exact-canonical counterpart of the original captured cross observable. -/
def actualExactCapturedCross {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid h × Euclid h) : ℝ :=
  exactPrefixCross (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
    (fun i => postprefixCoefficients u amp groups T p
      ((actualDyadicSupportPermutation u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
    (capturedBlockLo (dyadicGroupSupport u amp groups T) p q)
    (capturedBlockHi (dyadicGroupSupport u amp groups T) p q)
    (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)

theorem paper_sparse_constant_le_projected : (1/4194304:ℝ) ≤ ProjectedClusters.projectedConstant := by
  unfold ProjectedClusters.projectedConstant
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (le_div_iff₀ (by positivity)).mpr
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg (2:ℝ)]

/-- The literal full-row E_sp, rather than a compressed subevent, supplies the
sparse diagonal. Exact polar attainment preserves the retained constant. -/
theorem actual_captured_retained_lower_literal_sparse {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ j ∈ range q,dyadicGroupMass u amp groups T j)
    (X : Fin n → Euclid h × Euclid h) (hX : X ∈ paperSparseSingularGood d n h)
    (hproj : X ∉ actualCapturedProjectionBad u amp ha groups T d p q hreg hflat)
    (hcross : -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d) ≤
      actualExactCapturedCross u amp ha groups T d p q hreg hflat X) :
    (1/2:ℝ)^24*Real.sqrt d*coefficientMass (retainedGroupVector u amp groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u amp groups T) X := by
  let G := dyadicGroupSupport u amp groups T
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let U := orderedRetainedCoefficients u amp ha groups T d hreg hflat
  let Y := permuteRows e X
  let mass : CapturedBlockIndex p q → ℝ := fun j => match j with
    | none => ∑ j ∈ range p,dyadicGroupMass u amp groups T j
    | some j => dyadicGroupMass u amp groups T j.val
  have hb (j : CapturedBlockIndex p q) :
      (1/4194304:ℝ)*Real.sqrt d*mass j ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    cases j with
    | none =>
      exact paper_actual_sparse_first_block_lower u amp ha groups T p hreg hflat
        (hpq.trans hq) hbudget X hX
    | some j =>
      have hj := le_of_not_gt (fun hbad => hproj ⟨j.val,j.property,hbad⟩)
      have hm : 0 ≤ dyadicGroupMass u amp groups T j.val := sum_nonneg (fun i _ => abs_nonneg _)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right paper_sparse_constant_le_projected (Real.sqrt_nonneg _)) hm).trans hj
  have hsum : (1/4194304:ℝ)*Real.sqrt d*(∑ j ∈ range q,dyadicGroupMass u amp groups T j) ≤
      ∑ j : CapturedBlockIndex p q,spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    calc
      _ = ∑ j : CapturedBlockIndex p q,(1/4194304:ℝ)*Real.sqrt d*mass j := by
        rw [← mul_sum]
        congr 1
        exact (capturedBlock_mass_sum (dyadicGroupMass u amp groups T) p q hpq).symm
      _ ≤ _ := sum_le_sum (fun j _ => hb j)
  have halg := exact_nuclear_lower_from_captured_blocks G
    (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)
    p q hpq hq U Y
  rw [← ordered_postprefix_coefficients u amp ha groups T d p hreg hflat (hpq.trans hq)] at halg
  rw [ordered_retained_synthesis u amp ha groups T d hreg hflat X] at halg
  change _ + actualExactCapturedCross u amp ha groups T d p q hreg hflat X ≤
    scaledBilinearNuclear d (retainedGroupVector u amp groups T) X at halg
  have hc := mul_le_mul_of_nonneg_left hcapt
    (show (0:ℝ) ≤ (1/4194304)*Real.sqrt d by positivity)
  nlinarith

namespace PaperLogarithmicDepth

theorem actual_fixed_captured_failure_subset_literal_sparse {n d h : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u=1)
    (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups,RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 1 ≤ J) (hJup : J ≤ 17*(1+Real.log K))
    (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ j ∈ range q,dyadicGroupMass u amp groups T j) :
    ({X : Fin n → Euclid h × Euclid h | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
      paperSparseSingularGood d n h ∩ atomRowsGood d n h) ⊆
      actualCapturedProjectionBad u amp ha groups T d p q hreg hflat ∪
      {X | actualExactCapturedCross u amp ha groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} := by
  rintro X ⟨⟨hbad,hsp⟩,hatom⟩
  by_cases hp : X ∈ actualCapturedProjectionBad u amp ha groups T d p q hreg hflat
  · exact Or.inl hp
  · right
    by_contra hcross
    have hgood := actual_captured_retained_lower_literal_sparse u amp ha groups T p q hreg hflat
      hpq hq hbudget hcapt X hsp hp (le_of_not_ge hcross)
    have hret := actual_fixed_failure_subset_retained_flexible u hu amp groups K J hK (by linarith)
      hJup T hscale herr ⟨hbad,hatom⟩
    have hsK : 1 ≤ Real.sqrt K := by simpa using Real.sqrt_le_sqrt hK
    have hden : 1 ≤ Real.sqrt K*J := one_le_mul_of_one_le_of_one_le hsK hJ
    have hc : (1/2:ℝ)^24/(Real.sqrt K*J) ≤ (1/2:ℝ)^24 := div_le_self (by positivity) hden
    have hth := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (d:ℝ))) (coefficientMass_nonneg (retainedGroupVector u amp groups T))
    exact (not_lt_of_ge hgood) (hret.trans_le hth)
end PaperLogarithmicDepth

theorem actualExactCapturedCross_rank_aware_tail {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hd : 0 < (d:ℝ)) (hlog : 1 ≤ Real.log (d:ℝ))
    (hS : ∀ j, p ≤ j → j < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (x : ℝ) (hx : 0 ≤ x) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | actualExactCapturedCross u amp ha groups T d p q hreg hflat X ≤ -x} ≤
      Real.exp (-(1/4:ℝ)*min
        (x^2 / (((2:ℝ)^17*T*Real.log (d:ℝ)/d)*(coefficientMass (retainedGroupVector u amp groups T))^2))
        (x / ((2:ℝ)^18*T*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)*
          coefficientMass (retainedGroupVector u amp groups T)))) := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let U := orderedRetainedCoefficients u amp ha groups T d hreg hflat
  let G := dyadicGroupSupport u amp groups T
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
  let V : ℝ := (2:ℝ)^17*T*Real.log (d:ℝ)/d*M^2
  let b : ℝ := (2:ℝ)^18*T*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)*M
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hV : 0 < V := by dsimp [V,M]; positivity
  have hb : 0 < b := by dsimp [b,M]; positivity
  have hc := actual_postprefix_log_cap_energy u amp groups T p hT hreg d hd hlog0 hS
  have hcoef (i : Fin n) : (v i)^2 ≤ b^2/2 := by
    have habs : |v i| ≤ b/2 := by
      dsimp [v]
      rw [abs_div,abs_of_pos hroot]
      apply (div_le_iff₀ hroot).mpr
      have hi := hc.1 (e.symm i)
      have heq : b/2*Real.sqrt (d:ℝ) =
          131072*T*Real.log (d:ℝ)/(d:ℝ)*M := by
        dsimp [b]
        field_simp [hd.ne',hroot.ne']
        ring
      rw [heq]
      exact hi
    have hs := pow_le_pow_left₀ (abs_nonneg (v i)) habs 2
    rw [sq_abs] at hs
    nlinarith
  have hv : (∑ i, (v i)^2*(i.val:ℝ)) ≤ V := by
    apply (actual_postprefix_rank_variance_le u amp ha groups T p hreg hflat hchain d hd).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
    apply div_le_div_of_nonneg_right _ hd.le
    have h1 := mul_le_mul_of_nonneg_right (show (128/3:ℝ) ≤ 2^17 by norm_num) (Nat.cast_nonneg T : (0:ℝ) ≤ T)
    have h2 := mul_le_mul_of_nonneg_left hlog (show (0:ℝ) ≤ (2:ℝ)^17*T by positivity)
    nlinarith
  let F : Set (Fin n → Euclid h × Euclid h) :=
    {X | exactPrefixCross U v (capturedBlockLo G p q) (capturedBlockHi G p q) X ≤ -x}
  have hF : MeasurableSet F := measurableSet_le
    (measurable_exactPrefixCross U v _ _ (capturedBlock_ordered G p q)) measurable_const
  change (gaussianBilinearSampleLaw (Fin n) h h).real (permuteRows e ⁻¹' F) ≤ _
  rw [(permuteRows_preserving e h h).measureReal_preimage hF.nullMeasurableSet]
  exact exactPrefixCross_rank_weighted_lower_tail U v _ _
    (capturedBlock_ordered G p q) (capturedBlock_separated G p q) V b x hV hb hx hcoef hv

theorem actualExactCapturedCross_common_tail {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups,RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hd : 0 < (d:ℝ)) (hlog : 1 ≤ Real.log (d:ℝ))
    (hS : ∀ j,p ≤ j → j < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T)) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | actualExactCapturedCross u amp ha groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} ≤
      Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ))) := by
  have hh := actualExactCapturedCross_rank_aware_tail (h:=h) u amp ha groups T p q hT hreg hflat hchain
    hd hlog hS hM ((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d) (by positivity)
  have hp := actual_cross_chernoff_exponent d T (coefficientMass (retainedGroupVector u amp groups T))
    hd (Nat.cast_pos.mpr hT) hM (by linarith)
  rw [hp.2.2.2] at hh
  exact hh

/-- Dimension monotonicity for an unguarded fixed-vector lower-tail event.
No inference from a full sparse-good event to a compressed one is made. -/
theorem fixed_bilinear_bad_probability_mono {n k h : ℕ} (hkh : k ≤ h)
    (d : ℕ) (u : Fin n → ℝ) (c : ℝ) :
    (gaussianBilinearSampleLaw (Fin n) h h).real {X | scaledBilinearNuclear d u X < c} ≤
      (gaussianBilinearSampleLaw (Fin n) k k).real {X | scaledBilinearNuclear d u X < c} := by
  let e : Fin k ↪ Fin h := Fin.castLEEmb hkh
  let U := ContinuousLinearMap.adjoint (coordinateEmbedding e)
  have hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _ := by
    simpa only [U,ContinuousLinearMap.adjoint_adjoint] using coordinateEmbedding_adjoint_comp e
  have hUnorm : ‖U‖ ≤ 1 := by simpa [U] using coordinateEmbedding_norm_le_one e
  let E : Set (Fin n → Euclid k × Euclid k) := {X | scaledBilinearNuclear d u X < c}
  have hE : MeasurableSet E := (isOpen_lt (continuous_scaledBilinearNuclear (h:=k) d u) continuous_const).measurableSet
  have hs : {X : Fin n → Euclid h × Euclid h | scaledBilinearNuclear d u X < c} ⊆
      compressCanonicalRows U ⁻¹' E := by
    intro X hX
    exact (scaledBilinearNuclear_compress_le U hUnorm d u X).trans_lt hX
  exact (measureReal_mono hs).trans_eq
    ((compressCanonicalRows_preserving (n:=n) U hU).measureReal_preimage hE.nullMeasurableSet)

namespace PaperLogarithmicDepth

theorem actual_fixed_vector_tail_logarithmic_depth_dimension {n d h : ℕ} (K : ℝ) (hK : 1 ≤ K) (hfull : 2*(d/4) ≤ h)
    (hd24 : 24 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hfloor : (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ))
    (hbudget : (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ≤ (d:ℝ)/256)
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*((depth K:ℕ):ℝ)*Real.log (d:ℝ)))
    (hlate : 65536*((depth K:ℕ):ℝ) ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
        paperSparseSingularGood d n h ∩ atomRowsGood d n h) ≤
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
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz, coefficientMass] at hu
  have hamp : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hcap : ∀ i, |u i| ≤ ‖u‖ := fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  obtain ⟨N, groups, p, q, hN, hcover, hempty, hflat0, hreg, hchain, herr,
    hpq, hp, hq, hpost, hcapR, hlateS⟩ :=
    exists_constructed_cutoff_geometry u ‖u‖ hamp hcap T hT d hd hlog0 hfloor hbudget
  rw [hu, mul_one] at herr
  have hflat := actual_constructor_flatten_nodup u ‖u‖ groups N hflat0
  have hsp : supportCut (dyadicGroupSupport u ‖u‖ groups T) p ≤ sparseSupportSize d := by
    have hh : (supportCut (dyadicGroupSupport u ‖u‖ groups T) p : ℝ) ≤ (sparseSupportSize d:ℝ) := by
      rw [actual_dyadic_supportCut_cast]
      exact hp.2.1
    exact_mod_cast hh
  have hM0 := common_retained_tail_constants_flexible K J hK (by linarith) (by rfl) T hscale
  have hMpos : 0 < coefficientMass (retainedGroupVector u ‖u‖ groups T) := by
    have hh := retained_mass_ge_one_sub u ‖u‖ groups T (8*(1/2:ℝ)^T) hu herr
    change 8*(1/2:ℝ)^T ≤ 1/8 ∧ _ at hM0
    linarith [hM0.1]
  have hambient : (d:ℝ)/3 ≤ (h:ℝ) := by
    have heven : (d:ℝ)/3 ≤ ((2*(d/4):ℕ):ℝ) := by
      have hn : d ≤ 3*(2*(d/4)) := by omega
      have hr : (d:ℝ) ≤ 3*((2*(d/4):ℕ):ℝ) := by exact_mod_cast hn
      linarith
    exact heven.trans (Nat.cast_le.mpr hfull)
  have hE : 0 ≤ E := Real.exp_nonneg _
  by_cases hcapt : coefficientMass (retainedGroupVector u ‖u‖ groups T)/2 ≤
      ∑ r ∈ Finset.range q, dyadicGroupMass u ‖u‖ groups T r
  · have hsub := actual_fixed_captured_failure_subset_literal_sparse (h:=h) u hu ‖u‖ hamp.le groups T p q
      hreg hflat hpq hq.1 hsp K J hK hJ (by rfl) hscale herr hcapt
    have hprojected := actualCapturedProjectionBad_probability
      u ‖u‖ hamp.le groups T hT hreg hchain hflat p q hp hq
      (show 0 < d by omega) hambient hfloor hnum
    have hcross := actualExactCapturedCross_common_tail (h:=h) u ‖u‖ hamp.le groups T p q hT hreg hflat hchain
      hd hlog (fun r hpr hr => (hpost r hpr hr).1) hMpos
    have hprojCommon : (groups.length:ℝ)*Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log (d:ℝ))) ≤
        (n:ℝ)*E := by
      apply mul_le_mul
      · exact_mod_cast actual_group_count_le_ambient u ‖u‖ hamp.le groups T hreg hflat
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
  · have hlateEven := actual_original_late_fixed_smallball_flexible u hu ‖u‖ hamp groups K hK T hT hTcap hscale
      hreg hchain hflat hlate hsupp q hq herr (lt_of_not_ge hcapt)
    have hlateProb := (fixed_bilinear_bad_probability_mono hfull d u
      (multiscaleFixedConstant K*Real.sqrt d)).trans hlateEven
    calc
      _ ≤ (gaussianBilinearSampleLaw (Fin n) h h).real
          {X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} :=
        measureReal_mono (fun X hX => hX.1.1)
      _ ≤ Real.exp (-(d:ℝ)^2/(1048576*T)) := hlateProb
      _ ≤ E := late_tail_le_common d T hd.le hTr hlog
      _ ≤ (n+1:ℝ)*E := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hE]



theorem paper_full_half_fixed_vector_logarithmic_tail (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          paperSparseSingularGood d n (d/2) ∩ atomRowsGood d n (d/2)) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  let T := depth (max K 1)
  have hT : 0<T := depth_pos _ (le_max_right K 1)
  let C : ℝ := (2:ℝ)^67*T
  have hC : 0<C := by dsimp [C]; exact mul_pos (by positivity) (Nat.cast_pos.mpr hT)
  let c : ℝ := 1/(2*C)
  have hc : 0<c := by dsimp [c]; positivity
  have hlog : ∀ᶠ d : ℕ in atTop, 1 ≤ Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ d : ℕ in atTop, 48*C^3*(A+1) ≤ (d:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hall : ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 →
      ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          paperSparseSingularGood d n (d/2) ∩ atomRowsGood d n (d/2)) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
    filter_upwards [eventually_natural_cutoff_thresholds T hT,hlog,hlarge,eventually_ge_atTop 24]
      with d hcut hlogd hlargeD hd
    intro n hn u hu hs
    have hs' := hs.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Nat.cast_nonneg d))
    have htail := actual_fixed_vector_tail_logarithmic_depth_dimension (max K 1) (le_max_right K 1)
      (show 2*(d/4) ≤ d/2 by omega)
      hd hlogd hcut.2.2.1 hcut.2.2.2.1 hcut.2.2.2.2.1 hcut.2.2.2.2.2 u hu hs'
    have hconst : multiscaleFixedConstant (max K 1)=multiscaleFixedConstant K := by
      unfold multiscaleFixedConstant
      rw [max_eq_left (le_max_right K 1)]
    rw [hconst] at htail
    have hp := paper_logarithmic_prefactor hA.le hC
      (show (1:ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega)) hlogd hn hlargeD
    have hh := htail.trans hp
    apply hh.trans_eq
    congr 2
    dsimp [c]
    ring
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp hall
  exact ⟨c,hc,d₀,hd₀⟩

end PaperLogarithmicDepth
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.actual_captured_retained_lower_literal_sparse
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_full_half_fixed_vector_logarithmic_tail
