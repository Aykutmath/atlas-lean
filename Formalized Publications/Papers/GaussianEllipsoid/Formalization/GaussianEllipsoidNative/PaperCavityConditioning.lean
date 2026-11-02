import PaperBilinearMGFBridges
import BMProductLogPartition
import UCProductConcentration
import UCActualFreeEnergy

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace GaussianConditionalBound
variable {Ω P X : Type*} [MeasurableSpace P] [MeasurableSpace X]

/-- Genuine signed conditional expectation for a bounded kernel depending on
past data and an independent current row. All integrability is discharged. -/
theorem condExp_independent_bounded_kernel
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m≤mΩ)
    (Z : Ω→P) (Xrow : Ω→X) (hZ : Measurable[m] Z) (hX : Measurable Xrow)
    (hind : Indep m (MeasurableSpace.comap Xrow inferInstance) μ)
    (f : P×X→ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ p, |f p|≤M) :
    μ[fun ω => f (Z ω,Xrow ω) | m] =ᵐ[μ]
      fun ω => ∫ x,f (Z ω,x) ∂μ.map Xrow := by
  have hZm : Measurable Z := hZ.mono hm le_rfl
  haveI : IsProbabilityMeasure (μ.map Xrow) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hfm : Measurable (fun ω => f (Z ω,Xrow ω)) := hf.comp (hZm.prodMk hX)
  have hfi : Integrable (fun ω => f (Z ω,Xrow ω)) μ :=
    GaussianEllipsoid.UCProductConcentration.integrable_of_abs_bound hfm (fun ω => hbound _)
  have hsec (z : P) : Integrable (fun x => f (z,x)) (μ.map Xrow) :=
    GaussianEllipsoid.UCProductConcentration.integrable_of_abs_bound
      (hf.comp (measurable_const.prodMk measurable_id)) (fun x => hbound _)
  have hfinite : (∫⁻ ω, ENNReal.ofReal (f (Z ω,Xrow ω)+M) ∂μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (2*M) ∂μ := lintegral_mono fun ω =>
        ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hbound (Z ω,Xrow ω))).2])
      _ = ENNReal.ofReal (2*M) := by simp
  have he := condExp_independent_nonnegative_kernel m μ hm Z Xrow hZ hX hind
    (fun p => f p+M) (hf.add_const M)
    (fun p => by linarith [(abs_le.mp (hbound p)).1]) hfinite
  have ha := condExp_add hfi (integrable_const M) m
  filter_upwards [he,ha] with ω heω haω
  simp only [Pi.add_apply,condExp_const hm M] at haω
  rw [integral_add (hsec (Z ω)) (integrable_const M)] at heω
  simp only [integral_const,probReal_univ,one_smul] at heω
  change μ[fun ω => f (Z ω,Xrow ω)+M | m] ω =
    μ[fun ω => f (Z ω,Xrow ω) | m] ω + M at haω
  linarith

#print axioms condExp_independent_bounded_kernel
end GaussianConditionalBound

open BMFiniteGibbsTest BMProductLogPartition
namespace GaussianEllipsoid.PaperCavityConditioning
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowDeletedDifference (D : Data κ) {n : ℕ}
    (u : Fin n → κ → ℝ) (x y : κ → ℝ) : ℝ :=
  (logPartition (otherRowsPrior D u) y-logPartition (otherRowsPrior D u) x)/
    (D.beta*(n+1:ℕ))

theorem rowDeletedDifference_eq (D : Data κ) {n : ℕ}
    (i : Fin (n+1)) (u : Fin n→κ→ℝ) (x y : κ→ℝ) :
    UCActualFreeEnergy.freeEnergy D (i.insertNth x u)-
      UCActualFreeEnergy.freeEnergy D (i.insertNth y u) = rowDeletedDifference D u x y := by
  unfold UCActualFreeEnergy.freeEnergy rowDeletedDifference
  rw [fullLogPartition_insertNth,fullLogPartition_insertNth]
  ring

theorem otherRows_logPartition_continuous (D : Data κ) (n : ℕ) :
    Continuous (fun z : (Fin n→κ→ℝ)×(κ→ℝ) => logPartition (otherRowsPrior D z.1) z.2) := by
  have he : (fun z : (Fin n→κ→ℝ)×(κ→ℝ) => logPartition (otherRowsPrior D z.1) z.2) =
      fun z => fullLogPartition D (Fin.cons z.2 z.1)-fullLogPartition D z.1 := by
    funext z
    have h := fullLogPartition_insertNth D (0 : Fin (n+1)) z.1 z.2
    simp only [Fin.insertNth_zero'] at h
    linarith
  rw [he]
  apply Continuous.sub _ ((fullLogPartition_continuous D n).comp continuous_fst)
  apply (fullLogPartition_continuous D (n+1)).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop

theorem rowDeletedDifference_continuous (D : Data κ) (n : ℕ) :
    Continuous (fun z : (Fin n→κ→ℝ)×((κ→ℝ)×(κ→ℝ)) =>
      rowDeletedDifference D z.1 z.2.1 z.2.2) := by
  unfold rowDeletedDifference
  exact (((otherRows_logPartition_continuous D n).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).sub
    ((otherRows_logPartition_continuous D n).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).div_const _

theorem rowDeletedDifference_measurable (D : Data κ) (n : ℕ) :
    Measurable (fun z : (Fin n→κ→ℝ)×((κ→ℝ)×(κ→ℝ)) =>
      rowDeletedDifference D z.1 z.2.1 z.2.2) :=
  (rowDeletedDifference_continuous D n).measurable

theorem rowDeletedDifference_bound (D : Data κ) {n : ℕ}
    (u : Fin n→κ→ℝ) (x y : κ→ℝ) :
    |rowDeletedDifference D u x y| ≤
      2*(D.beta*‖D.potential‖)/|D.beta*(n+1:ℕ)| := by
  unfold rowDeletedDifference
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  have hx := logPartition_norm_le (otherRowsPrior D u) x
  have hy := logPartition_norm_le (otherRowsPrior D u) y
  simp only [Real.norm_eq_abs,otherRowsPrior_beta,otherRowsPrior_potential] at hx hy
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2,
    (abs_le.mp hy).1,(abs_le.mp hy).2]

/-- Literal deleted-row conditional expectation under the actual independent
history/current-row product. Its kernel is the same random prior on both sides. -/
theorem row_deleted_conditional_expectation (D : Data κ) (n : ℕ)
    (μ : Measure (Fin n→κ→ℝ)) [IsProbabilityMeasure μ]
    (ν ξ : Measure (κ→ℝ)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (i : Fin (n+1)) :
    (μ.prod (ν.prod ξ))[fun z =>
      UCActualFreeEnergy.freeEnergy D (i.insertNth z.2.1 z.1)-
      UCActualFreeEnergy.freeEnergy D (i.insertNth z.2.2 z.1) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.prod (ν.prod ξ)]
      fun z => ∫ xy,rowDeletedDifference D z.1 xy.1 xy.2 ∂ν.prod ξ := by
  have hm : MeasurableSpace.comap Prod.fst inferInstance ≤
      (inferInstance : MeasurableSpace ((Fin n→κ→ℝ)×((κ→ℝ)×(κ→ℝ)))) := measurable_fst.comap_le
  have hZ : Measurable[MeasurableSpace.comap Prod.fst inferInstance] (Prod.fst : (Fin n→κ→ℝ)×((κ→ℝ)×(κ→ℝ))→_) :=
    measurable_iff_comap_le.mpr le_rfl
  have hi := (IndepFun_iff_Indep _ _ _).mp (indepFun_prod (μ := μ) (ν := ν.prod ξ) (X := id) (Y := id) measurable_id measurable_id)
  have hβ := D.beta_nonneg
  have he := GaussianConditionalBound.condExp_independent_bounded_kernel (MeasurableSpace.comap Prod.fst inferInstance)
    (μ.prod (ν.prod ξ)) hm Prod.fst Prod.snd hZ measurable_snd hi
    (fun z => rowDeletedDifference D z.1 z.2.1 z.2.2)
    (rowDeletedDifference_continuous D n).measurable
    (2*(D.beta*‖D.potential‖)/|D.beta*(n+1:ℕ)|) (by positivity)
    (fun z => rowDeletedDifference_bound D z.1 z.2.1 z.2.2)
  have hlaw : (μ.prod (ν.prod ξ)).map Prod.snd=ν.prod ξ := measurePreserving_snd.map_eq
  rw [hlaw] at he
  simpa only [rowDeletedDifference_eq] using he


set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The conditioning sigma-field remembers the full raw history, including
information beyond the candidate measurements. The current driver pair is
independent by the product law, not a supplied conditional-law assumption. -/
theorem row_deleted_driver_conditional_expectation
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Y]
    (D : Data κ) (n : ℕ)
    (μ : Measure H) [IsProbabilityMeasure μ]
    (ν : Measure X) (ξ : Measure Y) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (u : H→Fin n→κ→ℝ) (hu : Measurable u)
    (q : X→κ→ℝ) (hq : Measurable q) (g : Y→κ→ℝ) (hg : Measurable g)
    (i : Fin (n+1)) :
    MeasureTheory.condExp (E := ℝ)
      (MeasurableSpace.comap (Prod.fst : H×(X×Y)→H) inferInstance)
      (μ.prod (ν.prod ξ)) (fun z : H×(X×Y) =>
      UCActualFreeEnergy.freeEnergy (n := n+1) D (Fin.insertNth (α := fun _ : Fin (n+1) => κ→ℝ) i (q z.2.1) (u z.1))-
      UCActualFreeEnergy.freeEnergy (n := n+1) D (Fin.insertNth (α := fun _ : Fin (n+1) => κ→ℝ) i (g z.2.2) (u z.1))) =ᵐ[μ.prod (ν.prod ξ)]
      fun z : H×(X×Y) => ∫ xy : X×Y,rowDeletedDifference D (u z.1) (q xy.1) (g xy.2) ∂ν.prod ξ := by
  have hm : MeasurableSpace.comap (Prod.fst : H×(X×Y)→H) inferInstance ≤
      (inferInstance : MeasurableSpace (H×(X×Y))) := measurable_fst.comap_le
  have hZ : Measurable[MeasurableSpace.comap (Prod.fst : H×(X×Y)→H) inferInstance]
      (Prod.fst : H×(X×Y)→H) := measurable_iff_comap_le.mpr le_rfl
  have hi := (IndepFun_iff_Indep _ _ _).mp
    (indepFun_prod (μ := μ) (ν := ν.prod ξ) (X := id) (Y := id) measurable_id measurable_id)
  have hu' : Measurable (fun z : H×(X×Y) => u z.1) := hu.comp measurable_fst
  have hq' : Measurable (fun z : H×(X×Y) => q z.2.1) :=
    hq.comp ((measurable_snd : Measurable (Prod.snd : H×(X×Y)→X×Y)).fst)
  have hg' : Measurable (fun z : H×(X×Y) => g z.2.2) :=
    hg.comp ((measurable_snd : Measurable (Prod.snd : H×(X×Y)→X×Y)).snd)
  have hmap : Measurable (fun z : H×(X×Y) =>
      (u z.1,(q z.2.1,g z.2.2))) := hu'.prodMk (hq'.prodMk hg')
  have houter : Measurable (fun z : (Fin n→κ→ℝ)×((κ→ℝ)×(κ→ℝ)) =>
      rowDeletedDifference D z.1 z.2.1 z.2.2) :=
    rowDeletedDifference_measurable D n
  have hk := houter.comp hmap
  have hkernel : Measurable (fun z : H×(X×Y) =>
      rowDeletedDifference D (u z.1) (q z.2.1) (g z.2.2)) := by
    simpa only [Function.comp_def] using hk
  have hβ := D.beta_nonneg
  have he := GaussianConditionalBound.condExp_independent_bounded_kernel
    (MeasurableSpace.comap (Prod.fst : H×(X×Y)→H) inferInstance) (μ.prod (ν.prod ξ)) hm
    Prod.fst Prod.snd hZ measurable_snd hi
    (fun z => rowDeletedDifference D (u z.1) (q z.2.1) (g z.2.2)) hkernel
    (2*(D.beta*‖D.potential‖)/|D.beta*(n+1:ℕ)|) (by positivity)
    (fun z => rowDeletedDifference_bound D (u z.1) (q z.2.1) (g z.2.2))
  have hlaw : (μ.prod (ν.prod ξ)).map Prod.snd=ν.prod ξ := measurePreserving_snd.map_eq
  rw [hlaw] at he
  have hfun : (fun z : H×(X×Y) =>
      UCActualFreeEnergy.freeEnergy D (i.insertNth (q z.2.1) (u z.1))-
      UCActualFreeEnergy.freeEnergy D (i.insertNth (g z.2.2) (u z.1))) =
      (fun z => rowDeletedDifference D (u z.1) (q z.2.1) (g z.2.2)) := by
    funext z
    exact rowDeletedDifference_eq D i (u z.1) (q z.2.1) (g z.2.2)
  rw [hfun]
  exact he

#print axioms row_deleted_driver_conditional_expectation

theorem otherRowsPrior_weight_continuous (D : Data κ) (n : ℕ) (a : κ) :
    Continuous (fun u : Fin n→κ→ℝ => (otherRowsPrior D u).weight a) := by
  change Continuous (fun u : Fin n→κ→ℝ =>
    D.weight a*Real.exp (-D.beta*rowSum D u a)/fullPartition D u)
  apply Continuous.div _ (fullPartition_continuous D n) (fun u => (fullPartition_pos D u).ne')
  unfold rowSum
  fun_prop

theorem otherRowsPrior_uniform_formula (D : Data κ) {n : ℕ}
    (hweight : ∀ a,D.weight a=(Fintype.card κ:ℝ)⁻¹)
    (u : Fin n→κ→ℝ) (a : κ) :
    (otherRowsPrior D u).weight a =
      Real.exp (-D.beta*rowSum D u a)/(∑ b,Real.exp (-D.beta*rowSum D u b)) := by
  have hc : (Fintype.card κ:ℝ)≠0 := by
    have h : 0<Fintype.card κ := Fintype.card_pos_iff.mpr ⟨a⟩
    exact_mod_cast Nat.ne_of_gt h
  change (D.weight a*Real.exp (-D.beta*rowSum D u a))/fullPartition D u = _
  unfold fullPartition
  simp_rw [hweight]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (inv_ne_zero hc)

#print axioms otherRowsPrior_uniform_formula
#print axioms otherRowsPrior_weight_continuous
#print axioms row_deleted_conditional_expectation
end GaussianEllipsoid.PaperCavityConditioning
