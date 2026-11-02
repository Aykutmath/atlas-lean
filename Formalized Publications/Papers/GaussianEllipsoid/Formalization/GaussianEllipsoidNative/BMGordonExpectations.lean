import BMGordonGeometry
import BMGordonAuxiliaryMean

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
  GaussianTensorMoments BMGeometry BMSaddle
namespace BMGordon

variable {ι η : Type*} [Fintype ι] [Fintype η]

/-- Gaussian coordinate blocks split into their independent product law. -/
def splitBlocks : EuclideanSpace ℝ (ι ⊕ η) ≃ᵐ
    EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
  (((MeasurableEquiv.toLp 2 ((ι ⊕ η) → ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ))).trans
    (((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).symm.prodCongr
      ((MeasurableEquiv.toLp 2 (η → ℝ)).symm).symm)

theorem splitBlocks_preserving : MeasurePreserving (splitBlocks (ι := ι) (η := η))
    (euclideanGaussianLaw (ι ⊕ η))
    ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw η)) := by
  exact ((MeasurePreserving.symm ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm) BMQuadraticSpectral.coordinates_preserving).prod
    (MeasurePreserving.symm ((MeasurableEquiv.toLp 2 (η → ℝ)).symm) BMQuadraticSpectral.coordinates_preserving)).comp
    ((measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => gaussianReal 0 1)).comp
      BMQuadraticSpectral.coordinates_preserving)

def leftBlock (x : EuclideanSpace ℝ (ι ⊕ η)) : EuclideanSpace ℝ ι :=
  (splitBlocks x).1

def rightBlock (x : EuclideanSpace ℝ (ι ⊕ η)) : EuclideanSpace ℝ η :=
  (splitBlocks x).2

@[simp] theorem leftBlock_apply (x : EuclideanSpace ℝ (ι ⊕ η)) (i : ι) :
    leftBlock x i = x (.inl i) := rfl
@[simp] theorem rightBlock_apply (x : EuclideanSpace ℝ (ι ⊕ η)) (i : η) :
    rightBlock x i = x (.inr i) := rfl

theorem leftBlock_preserving : MeasurePreserving (leftBlock (ι := ι) (η := η))
    (euclideanGaussianLaw (ι ⊕ η)) (euclideanGaussianLaw ι) := by
  have h : MeasurePreserving Prod.fst
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw η)) (euclideanGaussianLaw ι) :=
    ⟨measurable_fst, by simp⟩
  exact h.comp splitBlocks_preserving

theorem rightBlock_preserving : MeasurePreserving (rightBlock (ι := ι) (η := η))
    (euclideanGaussianLaw (ι ⊕ η)) (euclideanGaussianLaw η) := by
  have h : MeasurePreserving Prod.snd
      ((euclideanGaussianLaw ι).prod (euclideanGaussianLaw η)) (euclideanGaussianLaw η) :=
    ⟨measurable_snd, by simp⟩
  exact h.comp splitBlocks_preserving

/-- Expectation transport requires only a measurable observable, not an injective projection. -/
theorem integral_comp_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {p : α → β} (hp : MeasurePreserving p μ ν)
    {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ x, f (p x) ∂μ) = ∫ y, f y ∂ν := by
  rw [← hp.map_eq] at hf ⊢
  exact (integral_map hp.measurable.aemeasurable hf).symm

def matrixBlock {n d : ℕ} (ω : Space n d) : Sample n d := leftBlock (leftBlock ω)
def scalarBlock {n d : ℕ} (ω : Space n d) : ℝ := (rightBlock (leftBlock ω)) ()
def widthBlock {n d : ℕ} (ω : Space n d) : EuclideanSpace ℝ (Fin d × Fin d) :=
  leftBlock (rightBlock ω)
def driftBlock {n d : ℕ} (ω : Space n d) : Euclid n := rightBlock (rightBlock ω)
def widthMatrix {n d : ℕ} (ω : Space n d) : HMat d :=
  (frobeniusEquivEuclidean d d).symm (widthBlock ω)

theorem matrixBlock_preserving (n d : ℕ) : MeasurePreserving (@matrixBlock n d)
    (law n d) (sampleLaw n d) := leftBlock_preserving.comp leftBlock_preserving

theorem widthBlock_preserving (n d : ℕ) : MeasurePreserving (@widthBlock n d)
    (law n d) (euclideanGaussianLaw (Fin d × Fin d)) :=
  leftBlock_preserving.comp rightBlock_preserving

theorem driftBlock_preserving (n d : ℕ) : MeasurePreserving (@driftBlock n d)
    (law n d) (euclideanGaussianLaw (Fin n)) :=
  rightBlock_preserving.comp rightBlock_preserving

theorem primary_eq_blocks {n d : ℕ} {κ : ℝ}
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) :
    primary p ω = ⟪matrixBlock ω,tensor p.1 p.2⟫_ℝ + scalarBlock ω := by
  change (∑ i : Index n d, ω i * primaryCoefficient p.1 p.2 i) = _
  simp only [Fintype.sum_sum_type,primaryCoefficient,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero]
  change (∑ i : EntryIndex n d, matrixBlock ω i * tensor p.1 p.2 i) +
    (∑ i : Unit, ω (.inl (.inr i))*1) +
    ((∑ i : Fin d × Fin d, ω (.inr (.inl i))*0)+(∑ i : Fin n, ω (.inr (.inr i))*0)) = _
  simp only [mul_one,mul_zero,Fintype.sum_unique,Finset.sum_const_zero,add_zero]
  change (∑ i : EntryIndex n d, matrixBlock ω i * tensor p.1 p.2 i) + scalarBlock ω = _
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem auxiliary_eq_blocks {n d : ℕ} {κ : ℝ}
    (p : UnitSample n × UnitCone d κ) (ω : Space n d) :
    auxiliary p ω = ⟪widthMatrix ω,(p.2 : HMat d)⟫_ℝ + ⟪(p.1 : Euclid n),driftBlock ω⟫_ℝ := by
  change (∑ i : Index n d, ω i * auxiliaryCoefficient p.1 p.2 i) = _
  simp only [Fintype.sum_sum_type,auxiliaryCoefficient,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
  change ((∑ i : EntryIndex n d, ω (.inl (.inl i))*0)+(∑ i : Unit, ω (.inl (.inr i))*0))+
    ((∑ i : Fin d × Fin d, widthBlock ω i*frobeniusEquivEuclidean d d p.2 i)+
    ∑ i : Fin n, driftBlock ω i*(p.1 : Euclid n) i) = _
  simp only [mul_zero,Finset.sum_const_zero,zero_add]
  change ⟪frobeniusEquivEuclidean d d p.2,widthBlock ω⟫_ℝ +
    ⟪(p.1 : Euclid n),driftBlock ω⟫_ℝ = _
  congr 1
  rw [← LinearIsometryEquiv.inner_map_map (frobeniusEquivEuclidean d d)]
  simp only [widthMatrix,LinearIsometryEquiv.apply_symm_apply]
  exact real_inner_comm _ _

/-- The deterministic payoff used in the affine Gordon comparison. -/
def drift {n d : ℕ} {κ : ℝ} (R : ℝ) (p : UnitSample n × UnitCone d κ) : ℝ :=
  -⟪(p.1 : Euclid n),ones n⟫_ℝ / R

/-- Literal compact min-max, independent of any comparison theorem. -/
def minMax {K L : Type*} (f : K × L → ℝ) : ℝ :=
  sInf ((fun k => sSup ((fun l => f (k,l)) '' Set.univ)) '' Set.univ)

def primaryValue (n d : ℕ) (κ R : ℝ) (ω : Space n d) : ℝ :=
  minMax (fun p : UnitSample n × UnitCone d κ => primary p ω + drift R p)

def auxiliaryValue (n d : ℕ) (κ R : ℝ) (ω : Space n d) : ℝ :=
  minMax (fun p : UnitSample n × UnitCone d κ => auxiliary p ω + drift R p)

/-- The Frobenius and operator cone presentations have exactly the same support. -/
theorem support_unitCone (d : ℕ) (κ : ℝ) (G : HMat d) :
    sSup ((fun S : UnitCone d κ => ⟪G,(S : HMat d)⟫_ℝ) '' Set.univ) =
      conditionedSupport d κ G := by
  unfold conditionedSupport
  congr 1
  ext z
  constructor
  · rintro ⟨S,_,rfl⟩
    refine ⟨frobeniusOperator S,⟨S.property.1,?_⟩,?_⟩
    · simpa only [operatorFrobenius_frobeniusOperator] using unitCone_norm S
    · simp only [operatorFrobenius_frobeniusOperator]
  · rintro ⟨S,hS,rfl⟩
    refine ⟨⟨operatorFrobenius S,⟨?_,?_⟩⟩,Set.mem_univ _,rfl⟩
    · change frobeniusOperator (operatorFrobenius S) ∈ conditionCone d κ
      simpa only [frobeniusOperator_operatorFrobenius] using hS.1
    · simpa only [Metric.mem_sphere,dist_zero_right] using hS.2

/-- Exact primary min-max: the independent scalar coordinate simply adds to the saddle value. -/
theorem primaryValue_eq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) (ω : Space n d) :
    primaryValue n d κ R ω = statistic n d κ R (matrixBlock ω) + scalarBlock ω := by
  have hrow (u : UnitSample n) :
      sSup ((fun S : UnitCone d κ => primary (u,S) ω + drift R (u,S)) '' Set.univ) =
        rowObjective n d κ R (matrixBlock ω) u + scalarBlock ω := by
    obtain ⟨S,hS,heq,hmax⟩ := rowObjective_maximum hd hκ R (matrixBlock ω) u
    let S' : UnitCone d κ := ⟨operatorFrobenius S,⟨by
      change frobeniusOperator (operatorFrobenius S) ∈ conditionCone d κ
      simpa only [frobeniusOperator_operatorFrobenius] using hS.1, by
      simpa only [Metric.mem_sphere,dist_zero_right] using hS.2⟩⟩
    apply IsGreatest.csSup_eq
    refine ⟨⟨S',Set.mem_univ _,?_⟩,?_⟩
    · dsimp only
      rw [primary_eq_blocks,drift,heq]
      change _ + _ + -_ / R = (_ - _ / R) + _
      ring
    · rintro z ⟨T,_,rfl⟩
      have hT : frobeniusOperator T ∈ conditionedUnit d κ :=
        ⟨T.property.1,by simpa only [operatorFrobenius_frobeniusOperator] using unitCone_norm T⟩
      have h := hmax _ hT
      simp only [operatorFrobenius_frobeniusOperator] at h
      dsimp only
      rw [primary_eq_blocks,drift]
      simp only [Prod.fst,Prod.snd,neg_div]
      linarith
  unfold primaryValue minMax
  simp_rw [hrow]
  obtain ⟨u,hu,heq,hmin⟩ := statistic_minimum hn hd hκ R (matrixBlock ω)
  let u' : UnitSample n := ⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨u',Set.mem_univ _,?_⟩,?_⟩
  · exact congrArg (fun z => z+scalarBlock ω) heq.symm
  · rintro z ⟨v,_,rfl⟩
    exact add_le_add_left (hmin v (unitSample_norm v)) _

/-- The minimum of a real linear form over the unit sphere is minus its norm. -/
theorem inner_unitSphere_minimum {n : ℕ} (hn : 0 < n) (h : Euclid n) :
    ∃ u : UnitSample n, ⟪(u : Euclid n),h⟫_ℝ = -‖h‖ ∧
      ∀ v : UnitSample n, -‖h‖ ≤ ⟪(v : Euclid n),h⟫_ℝ := by
  have hbound (v : UnitSample n) : -‖h‖ ≤ ⟪(v : Euclid n),h⟫_ℝ := by
    have hb := (abs_le.mp (norm_inner_le_norm (𝕜 := ℝ) (v : Euclid n) h)).1
    simpa only [Real.norm_eq_abs,unitSample_norm,one_mul] using hb
  by_cases hz : h = 0
  · obtain ⟨u⟩ := unitSample_nonempty hn
    exact ⟨u,by simp [hz],hbound⟩
  · have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
    let u : Euclid n := -(‖h‖⁻¹) • h
    have hu : ‖u‖ = 1 := by
      change ‖-‖h‖⁻¹ • h‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos (inv_pos.mpr hnorm),inv_mul_cancel₀ hnorm.ne']
    refine ⟨⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩,?_,hbound⟩
    change ⟪u,h⟫_ℝ = _
    change ⟪-‖h‖⁻¹ • h,h⟫_ℝ = -‖h‖
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
    <;> ring

/-- The auxiliary min-max separates into cone support minus a shifted Gaussian norm. -/
theorem auxiliaryValue_eq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) (ω : Space n d) :
    auxiliaryValue n d κ R ω = conditionedSupport d κ (widthMatrix ω) -
      ‖driftBlock ω - R⁻¹ • ones n‖ := by
  have hpay (u : UnitSample n) (S : UnitCone d κ) :
      auxiliary (u,S) ω + drift R (u,S) =
        ⟪widthMatrix ω,(S : HMat d)⟫_ℝ +
          ⟪(u : Euclid n),driftBlock ω-R⁻¹ • ones n⟫_ℝ := by
    rw [auxiliary_eq_blocks,drift,inner_sub_right,real_inner_smul_right]
    simp only [div_eq_mul_inv]
    ring
  have hrow (u : UnitSample n) :
      sSup ((fun S : UnitCone d κ => auxiliary (u,S) ω + drift R (u,S)) '' Set.univ) =
        conditionedSupport d κ (widthMatrix ω) +
          ⟪(u : Euclid n),driftBlock ω-R⁻¹ • ones n⟫_ℝ := by
    obtain ⟨S,hS,heq⟩ := conditionedSupport_maximum hd hκ (widthMatrix ω)
    let S' : UnitCone d κ := ⟨operatorFrobenius S,⟨by
      change frobeniusOperator (operatorFrobenius S) ∈ conditionCone d κ
      simpa only [frobeniusOperator_operatorFrobenius] using hS.1, by
      simpa only [Metric.mem_sphere,dist_zero_right] using hS.2⟩⟩
    apply IsGreatest.csSup_eq
    refine ⟨⟨S',Set.mem_univ _,?_⟩,?_⟩
    · dsimp only
      rw [hpay,heq]
    · rintro z ⟨T,_,rfl⟩
      dsimp only
      rw [hpay]
      apply add_le_add_left
      have hT : frobeniusOperator T ∈ conditionedUnit d κ :=
        ⟨T.property.1,by simpa only [operatorFrobenius_frobeniusOperator] using unitCone_norm T⟩
      simpa only [operatorFrobenius_frobeniusOperator] using le_conditionedSupport (widthMatrix ω) hT
  unfold auxiliaryValue minMax
  simp_rw [hrow]
  obtain ⟨u,hu,hmin⟩ := inner_unitSphere_minimum hn (driftBlock ω-R⁻¹ • ones n)
  apply IsLeast.csInf_eq
  refine ⟨⟨u,Set.mem_univ _,?_⟩,?_⟩
  · dsimp only
    rw [hu]
    ring
  · rintro z ⟨v,_,rfl⟩
    simpa only [sub_eq_add_neg] using add_le_add_right (hmin v) (conditionedSupport d κ (widthMatrix ω))


theorem scalarBlock_preserving (n d : ℕ) : MeasurePreserving (@scalarBlock n d)
    (law n d) (gaussianReal 0 1) := by
  have h : MeasurePreserving (fun x : Index n d → ℝ => x (.inl (.inr ())))
      (gaussianProductLaw (Index n d)) (gaussianReal 0 1) :=
    ⟨measurable_pi_apply _,gaussianProductLaw_coordinate _⟩
  exact h.comp BMQuadraticSpectral.coordinates_preserving

theorem scalarBlock_integrable (n d : ℕ) : Integrable (@scalarBlock n d) (law n d) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
    simpa only [pow_one] using standardGaussian_integrable_pow 1
  exact ((scalarBlock_preserving n d).integrable_comp hi.aestronglyMeasurable).mpr hi

theorem scalarBlock_mean (n d : ℕ) : (∫ ω, scalarBlock ω ∂law n d) = 0 := by
  calc
    _ = ∫ x : ℝ, x ∂gaussianReal 0 1 :=
      integral_comp_preserving (scalarBlock_preserving n d) continuous_id.aestronglyMeasurable
    _ = 0 := by simpa only [pow_one] using standardGaussian_moment_one

theorem conditionedSupport_euclidean_integrable {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d × Fin d) =>
      conditionedSupport d κ ((frobeniusEquivEuclidean d d).symm x))
      (euclideanGaussianLaw (Fin d × Fin d)) :=
  GaussianVariance.lipschitz_integrable (by
    simpa only [one_mul,Function.comp_def] using
      (conditionedSupport_lipschitz hd hκ).comp (frobeniusEquivEuclidean d d).symm.lipschitz)

theorem conditionedWidth_eq_euclidean (d : ℕ) (κ : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d × Fin d),
      conditionedSupport d κ ((frobeniusEquivEuclidean d d).symm x)
      ∂euclideanGaussianLaw (Fin d × Fin d)) = conditionedWidth d κ := by
  rw [conditionedWidth_eq_fullEntry]
  exact ((MeasurePreserving.symm ((MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).symm) BMQuadraticSpectral.coordinates_preserving).integral_comp'
    (fun x => conditionedSupport d κ ((frobeniusEquivEuclidean d d).symm x))).symm

theorem widthBlock_integrable {n d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    Integrable (fun ω : Space n d => conditionedSupport d κ (widthMatrix ω)) (law n d) :=
  ((widthBlock_preserving n d).integrable_comp
    (conditionedSupport_euclidean_integrable hd hκ).aestronglyMeasurable).mpr
      (conditionedSupport_euclidean_integrable hd hκ)

theorem widthBlock_mean {n d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    (∫ ω : Space n d, conditionedSupport d κ (widthMatrix ω) ∂law n d) =
      conditionedWidth d κ := by
  unfold widthMatrix
  rw [integral_comp_preserving (widthBlock_preserving n d)
    (conditionedSupport_euclidean_integrable hd hκ).aestronglyMeasurable]
  exact conditionedWidth_eq_euclidean d κ

theorem driftBlock_norm_integrable (n d : ℕ) (R : ℝ) :
    Integrable (fun ω : Space n d => ‖driftBlock ω-R⁻¹ • ones n‖) (law n d) :=
  ((driftBlock_preserving n d).integrable_comp
    (shifted_norm_lipschitz (R⁻¹ • ones n)).continuous.aestronglyMeasurable).mpr
      (GaussianVariance.lipschitz_integrable (shifted_norm_lipschitz (R⁻¹ • ones n)))

theorem driftBlock_norm_mean (n d : ℕ) (R : ℝ) :
    (∫ ω : Space n d, ‖driftBlock ω-R⁻¹ • ones n‖ ∂law n d) =
      ∫ h : Euclid n, ‖h-R⁻¹ • ones n‖ ∂euclideanGaussianLaw (Fin n) :=
  integral_comp_preserving (driftBlock_preserving n d)
    (shifted_norm_lipschitz (R⁻¹ • ones n)).continuous.aestronglyMeasurable

theorem primaryValue_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) : Integrable (primaryValue n d κ R) (law n d) := by
  have hi := ((matrixBlock_preserving n d).integrable_comp
    (statistic_integrable hn hd hκ R).aestronglyMeasurable).mpr
      (statistic_integrable hn hd hκ R)
  have h := hi.add (scalarBlock_integrable n d)
  convert! h using 1
  funext ω
  exact primaryValue_eq hn hd hκ R ω

theorem auxiliaryValue_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) : Integrable (auxiliaryValue n d κ R) (law n d) := by
  have h := (widthBlock_integrable (n := n) hd hκ).sub (driftBlock_norm_integrable n d R)
  convert! h using 1
  funext ω
  exact auxiliaryValue_eq hn hd hκ R ω

/-- Actual primary expected min-max equals the concrete BM saddle expectation. -/
theorem primaryValue_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ ω, primaryValue n d κ R ω ∂law n d) = statisticMean n d κ R := by
  simp_rw [primaryValue_eq hn hd hκ R]
  have hi := ((matrixBlock_preserving n d).integrable_comp
    (statistic_integrable hn hd hκ R).aestronglyMeasurable).mpr
      (statistic_integrable hn hd hκ R)
  have hadd := integral_add hi (scalarBlock_integrable n d)
  simp only [Function.comp_def] at hadd
  rw [hadd,scalarBlock_mean,add_zero]
  exact integral_comp_preserving (matrixBlock_preserving n d)
    (statistic_integrable hn hd hκ R).aestronglyMeasurable

/-- Actual auxiliary expected min-max is width minus the independent drift-norm mean. -/
theorem auxiliaryValue_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ}
    (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ ω, auxiliaryValue n d κ R ω ∂law n d) = conditionedWidth d κ -
      (∫ h : Euclid n, ‖h-R⁻¹ • ones n‖ ∂euclideanGaussianLaw (Fin n)) := by
  simp_rw [auxiliaryValue_eq hn hd hκ R]
  rw [integral_sub (widthBlock_integrable hd hκ) (driftBlock_norm_integrable n d R),
    widthBlock_mean hd hκ,driftBlock_norm_mean]

/-- This transport leaves only the genuine affine min-max comparison to be proved. -/
theorem expectedGordonComparison_of_values {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R : ℝ}
    (hκ : 1 ≤ κ)
    (hcompare : (∫ ω, auxiliaryValue n d κ R ω ∂law n d) ≤
      ∫ ω, primaryValue n d κ R ω ∂law n d) : ExpectedGordonComparison n d κ R := by
  rw [auxiliaryValue_mean hn hd hκ R,primaryValue_mean hn hd hκ R] at hcompare
  exact hcompare

end BMGordon
