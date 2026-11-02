import ActualProbabilityReduction
import ActualGroupCount
import ActualCapturedProjectionProbability

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Fully assembled Section 7 estimate for one deterministic unit-l1 vector.
The decomposition, dichotomy, projected and sparse laws, constructed witnesses,
actual adapted cross event, late driver and omitted-tail absorption are proved
internally. Only explicit numerical starting-dimension conditions remain. -/
theorem actual_fixed_vector_tail {n d : ℕ} (K : ℝ) (hK : 1 ≤ K)
    (hd24 : 24 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hfloor : (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ))
    (hbudget : (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ≤ (d:ℝ)/256)
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*((40+4*⌈K⌉₊:ℕ):ℝ)*Real.log (d:ℝ)))
    (hlate : 65536*((40+4*⌈K⌉₊:ℕ):ℝ) ≤ d)
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
        sparseRowsGood (2*(d/4)) n (sparseSupportSize d) ∩ atomRowsGood d n (2*(d/4))) ≤
      (n+1:ℝ)*Real.exp (-(d:ℝ)^2/((2:ℝ)^67*((40+4*⌈K⌉₊:ℕ):ℝ)*Real.log (d:ℝ))) := by
  let T : ℕ := 40+4*⌈K⌉₊
  let J : ℝ := 17*(1+Real.log K)
  let E : ℝ := Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ)))
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hT : 0 < T := by dsimp [T]; omega
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
  have hM0 := common_retained_tail_constants K J hK (by linarith) (by rfl)
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
  · have hsub := actual_fixed_captured_failure_subset hd24 u hu 1 (by norm_num) groups T p q
      hreg hflat hpq hq.1 hsp K J hK hJ (by rfl) rfl herr hcapt
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
  · have hlateProb := actual_original_late_fixed_smallball u hu 1 (by norm_num) groups K hK T rfl
      hreg hchain hflat hlate hsupp q hq herr (lt_of_not_ge hcapt)
    calc
      _ ≤ (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
          {X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} :=
        measureReal_mono (fun X hX => hX.1.1)
      _ ≤ Real.exp (-(d:ℝ)^2/(1048576*T)) := hlateProb
      _ ≤ E := late_tail_le_common d T hd.le hTr hlog
      _ ≤ (n+1:ℝ)*E := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hE]

end GaussianEllipsoidCandidate
