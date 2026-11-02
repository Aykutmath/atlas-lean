import BMFiniteSoftMin
import GaussianUniformFractionalMoment
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Operator-net extension of the BM ground energy

All hypotheses below are deterministic and explicit. In the matrix application V
carries the operator norm, and `ell i` is the normalized trace-pairing row.
The continuum ground energy is an actual real `sInf`; the net energy is the
actual `Finset.inf'`. No attainment of the continuum infimum is assumed.
-/

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BMNetGroundExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual ground energy over a possibly infinite constraint set. -/
def ground (B : Set V) (E : V → ℝ) : ℝ := sInf (E '' B)

/-- Actual finite-net minimum. -/
def netGround (t : Finset V) (ht : t.Nonempty) (E : V → ℝ) : ℝ := t.inf' ht E

/-- A finite net contained in a constraint set approximates its true infimum.
This needs only a lower bound, not compactness or attainment. -/
theorem netGround_sub_ground_bounds
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty)
    (E : V → ℝ) (hbounded : BddBelow (E '' B))
    (hsub : ∀ y ∈ t, y ∈ B) {K η : ℝ} (hK : 0 ≤ K)
    (hnet : ∀ x ∈ B, ∃ y ∈ t, ‖x-y‖ ≤ η)
    (hLip : ∀ x ∈ B, ∀ y ∈ B, |E x-E y| ≤ K*‖x-y‖) :
    0 ≤ netGround t ht E-ground B E ∧
      netGround t ht E-ground B E ≤ K*η := by
  have hlo : ground B E ≤ netGround t ht E := by
    obtain ⟨y, hyt, hy⟩ := Finset.exists_mem_eq_inf' ht E
    rw [netGround, hy]
    exact csInf_le hbounded ⟨y, hsub y hyt, rfl⟩
  have hup : netGround t ht E-K*η ≤ ground B E := by
    apply le_csInf (hB.image E)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyt, hxy⟩ := hnet x hx
    have hmin : netGround t ht E ≤ E y := Finset.inf'_le E hyt
    have hdiff := hLip x hx y (hsub y hyt)
    have hdist : K*‖x-y‖ ≤ K*η := mul_le_mul_of_nonneg_left hxy hK
    have := neg_le_abs (E x-E y)
    linarith
  exact ⟨sub_nonneg.mpr hlo, by linarith⟩

theorem abs_netGround_sub_ground_le
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty)
    (E : V → ℝ) (hbounded : BddBelow (E '' B))
    (hsub : ∀ y ∈ t, y ∈ B) {K η : ℝ} (hK : 0 ≤ K)
    (hnet : ∀ x ∈ B, ∃ y ∈ t, ‖x-y‖ ≤ η)
    (hLip : ∀ x ∈ B, ∀ y ∈ B, |E x-E y| ≤ K*‖x-y‖) :
    |netGround t ht E-ground B E| ≤ K*η := by
  obtain ⟨hl,hu⟩ := netGround_sub_ground_bounds B hB t ht E hbounded hsub hK hnet hLip
  rwa [abs_of_nonneg hl]

/-- Equality with the finite-state minimum used in the soft-min argument. -/
theorem netGround_eq_finite_ground
    (t : Finset V) (ht : t.Nonempty) (E : V → ℝ) :
    letI : Nonempty {x // x ∈ t} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
    netGround t ht E = BMFiniteSoftMin.ground (fun x : {x // x ∈ t} => E x) := by
  letI : Nonempty {x // x ∈ t} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  change netGround t ht E = BMFiniteSoftMin.ground (fun x : {x // x ∈ t} => E x)
  apply le_antisymm
  · obtain ⟨x,hx⟩ := BMFiniteSoftMin.ground_attained (fun x : {x // x ∈ t} => E x)
    rw [hx]
    exact Finset.inf'_le E x.property
  · obtain ⟨x,hx,heq⟩ := Finset.exists_mem_eq_inf' ht E
    rw [netGround, heq]
    exact BMFiniteSoftMin.ground_le (fun x : {x // x ∈ t} => E x) ⟨x,hx⟩

variable {ι : Type*} [Fintype ι]

/-- BM's dimension-normalized empirical potential, with the actual row forms. -/
def energy (d : ℕ) (ell : ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ) (x : V) : ℝ :=
  (∑ i, φ (ell i x)) / (d : ℝ)^2

/-- A uniform empirical L1 estimate controls the operator-norm Lipschitz
constant of the actual empirical energy. -/
theorem energy_lipschitz
    (d : ℕ) (hd : 0 < d) (ell : ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ)
    {L C : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ a b, |φ a-φ b| ≤ L*|a-b|)
    (hL1 : ∀ H : V, (∑ i, |ell i H|) ≤ C*‖H‖) (x y : V) :
    |energy d ell φ x-energy d ell φ y| ≤ (L*C/(d : ℝ)^2)*‖x-y‖ := by
  have hd2 : 0 < (d : ℝ)^2 := by positivity
  unfold energy
  rw [← sub_div, abs_div, abs_of_pos hd2, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (φ (ell i x)-φ (ell i y))| / (d : ℝ)^2
        ≤ (∑ i, |φ (ell i x)-φ (ell i y)|) / (d : ℝ)^2 :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hd2.le
    _ ≤ (∑ i, L*|ell i (x-y)|) / (d : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ hd2.le
      apply Finset.sum_le_sum
      intro i hi
      simpa only [map_sub] using hφ (ell i x) (ell i y)
    _ = (L*(∑ i, |ell i (x-y)|)) / (d : ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ (L*(C*‖x-y‖)) / (d : ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL1 (x-y)) hL) hd2.le
    _ = _ := by ring

/-- The unit-operator-ball version of the L1 hypothesis implies the homogeneous
version used by `energy_lipschitz`. -/
theorem sum_abs_le_of_unit_ball
    (ell : ι → V →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ H : V, ‖H‖ ≤ 1 → (∑ i, |ell i H|) ≤ C) :
    ∀ H : V, (∑ i, |ell i H|) ≤ C*‖H‖ := by
  intro H
  by_cases hz : H = 0
  · simp [hz]
  have hn : 0 < ‖H‖ := norm_pos_iff.mpr hz
  have hu : ‖(‖H‖⁻¹ : ℝ) • H‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hh := hunit ((‖H‖⁻¹ : ℝ) • H) hu
  have he : (∑ i, |ell i ((‖H‖⁻¹ : ℝ) • H)|) = ‖H‖⁻¹*(∑ i, |ell i H|) := by
    simp only [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn), Finset.mul_sum]
  rw [he] at hh
  calc
    (∑ i, |ell i H|) = ‖H‖*(‖H‖⁻¹*(∑ i, |ell i H|)) := by field_simp
    _ ≤ ‖H‖*C := mul_le_mul_of_nonneg_left hh hn.le
    _ = _ := mul_comm _ _

/-- The concrete finite-net/continuum BM energy estimate with denominator d².
Nonnegativity of the potential supplies the lower bound for the real infimum. -/
theorem abs_net_energy_ground_le
    (d : ℕ) (hd : 0 < d) (ell : ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ)
    {L C η : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hφ : ∀ a b, |φ a-φ b| ≤ L*|a-b|) (hφnonneg : ∀ a, 0 ≤ φ a)
    (hL1 : ∀ H : V, (∑ i, |ell i H|) ≤ C*‖H‖)
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty)
    (hsub : ∀ y ∈ t, y ∈ B)
    (hnet : ∀ x ∈ B, ∃ y ∈ t, ‖x-y‖ ≤ η) :
    |netGround t ht (energy d ell φ)-ground B (energy d ell φ)| ≤
      L*C*η/(d : ℝ)^2 := by
  have hbounded : BddBelow ((energy d ell φ) '' B) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun i _ => hφnonneg _) (sq_nonneg _)
  have h := abs_netGround_sub_ground_le B hB t ht (energy d ell φ) hbounded hsub
    (div_nonneg (mul_nonneg hL hC) (sq_nonneg (d : ℝ))) hnet
    (fun x _ y _ => energy_lipschitz d hd ell φ hL hφ hL1 x y)
  convert h using 1 <;> ring

/-- Elementary fractional-moment to L1 bridge, valid for every exponent q≥1. -/
theorem sum_abs_le_card_add_moment
    (r : ι → ℝ) {q K : ℝ} (hq : 1 ≤ q)
    (hmoment : (∑ i, |r i|^q) ≤ K*(Fintype.card ι : ℝ)) :
    (∑ i, |r i|) ≤ (1+K)*(Fintype.card ι : ℝ) := by
  have hpoint (i : ι) : |r i| ≤ 1+|r i|^q := by
    by_cases hi : |r i| ≤ 1
    · linarith [Real.rpow_nonneg (abs_nonneg (r i)) q]
    · have := Real.self_le_rpow_of_one_le (le_of_not_ge hi) hq
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  nlinarith

/-- A uniform fractional-moment bound on the unit operator ball yields the L1
estimate required for the ground-energy extension. In particular use q=6/5. -/
theorem uniform_L1_of_fractional_moment
    (ell : ι → V →L[ℝ] ℝ) {q K : ℝ} (hq : 1 ≤ q) (hK : 0 ≤ K)
    (hmoment : ∀ H : V, ‖H‖ ≤ 1 →
      (∑ i, |ell i H|^q) ≤ K*(Fintype.card ι : ℝ)) :
    ∀ H : V, (∑ i, |ell i H|) ≤ ((1+K)*(Fintype.card ι : ℝ))*‖H‖ := by
  apply sum_abs_le_of_unit_ball ell (by positivity)
  intro H hH
  exact sum_abs_le_card_add_moment (fun i => ell i H) hq (hmoment H hH)

/-- Bounded row potentials give the exact dimension-normalized energy bound. -/
theorem abs_energy_le
    (d : ℕ) (ell : ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ) {M : ℝ}
    (hφ : ∀ a, |φ a| ≤ M) (x : V) :
    |energy d ell φ x| ≤ (Fintype.card ι : ℝ)*M/(d : ℝ)^2 := by
  unfold energy
  rw [abs_div, abs_of_nonneg (sq_nonneg (d : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    |∑ i, φ (ell i x)| ≤ ∑ i, |φ (ell i x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, M := Finset.sum_le_sum (fun i _ => hφ _)
    _ = _ := by simp

/-- Bounded energies have bounded true infima. -/
theorem abs_ground_le
    (B : Set V) (hB : B.Nonempty) (E : V → ℝ) {M : ℝ}
    (hbound : ∀ x ∈ B, |E x| ≤ M) : |ground B E| ≤ M := by
  have hlo : ∀ x ∈ B, -M ≤ E x := fun x hx => (abs_le.mp (hbound x hx)).1
  have hb : BddBelow (E '' B) := ⟨-M, by rintro _ ⟨x,hx,rfl⟩; exact hlo x hx⟩
  apply abs_le.mpr
  constructor
  · exact le_csInf (hB.image E) (by rintro _ ⟨x,hx,rfl⟩; exact hlo x hx)
  · obtain ⟨x,hx⟩ := hB
    exact (csInf_le hb ⟨x,hx,rfl⟩).trans (abs_le.mp (hbound x hx)).2

/-- Bounded energies also bound their finite-net minima. -/
theorem abs_netGround_le
    (t : Finset V) (ht : t.Nonempty) (E : V → ℝ) {M : ℝ}
    (hbound : ∀ x ∈ t, |E x| ≤ M) : |netGround t ht E| ≤ M := by
  obtain ⟨x,hx,heq⟩ := Finset.exists_mem_eq_inf' ht E
  rw [netGround, heq]
  exact hbound x hx

/-- The true infimum is equivalently a conditional infimum indexed by states. -/
theorem ground_eq_ciInf (B : Set V) (E : V → ℝ) :
    ground B E = ⨅ x : B, E x := by
  unfold ground iInf
  congr 1
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,x.property,rfl⟩

/-- On a finite set the true infimum equals the actual `Finset.inf'`. -/
theorem ground_finset_eq_netGround (t : Finset V) (ht : t.Nonempty) (E : V → ℝ) :
    ground (↑t : Set V) E = netGround t ht E := by
  have hb : BddBelow (E '' (↑t : Set V)) := by
    refine ⟨netGround t ht E, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact Finset.inf'_le E hx
  apply le_antisymm
  · obtain ⟨x,hx,heq⟩ := Finset.exists_mem_eq_inf' ht E
    rw [netGround,heq]
    exact csInf_le hb ⟨x,hx,rfl⟩
  · exact le_csInf (ht.to_set.image E) (by rintro _ ⟨x,hx,rfl⟩; exact Finset.inf'_le E hx)

section Integrability
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- Ground energy is measurable as an upper-semicontinuous infimum of continuous
sample-dependent energies. No compactness or countability of B is required. -/
theorem measurable_ground_of_continuous
    (B : Set V) (E : Ω → V → ℝ)
    (hcont : ∀ x ∈ B, Continuous (fun ω => E ω x))
    (hbelow : ∀ ω, BddBelow ((E ω) '' B)) :
    Measurable (fun ω => ground B (E ω)) := by
  have hbb (ω : Ω) : BddBelow (Set.range fun x : B => E ω x) := by
    convert hbelow ω using 1
    ext z
    simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_and_right, exists_prop]
  have hsc : UpperSemicontinuous (fun ω => ⨅ x : B, E ω x) :=
    upperSemicontinuous_ciInf hbb (fun x => (hcont x x.property).upperSemicontinuous)
  simpa only [ground_eq_ciInf] using hsc.measurable

/-- Bounded potential and sample-wise continuity close the actual continuum
integrability obligation under every finite measure. -/
theorem integrable_ground_of_continuous_bounded
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : Set V) (hB : B.Nonempty) (E : Ω → V → ℝ) {M : ℝ}
    (hcont : ∀ x ∈ B, Continuous (fun ω => E ω x))
    (hbound : ∀ ω, ∀ x ∈ B, |E ω x| ≤ M) :
    Integrable (fun ω => ground B (E ω)) μ := by
  have hb (ω : Ω) : BddBelow ((E ω) '' B) := by
    refine ⟨-M,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (abs_le.mp (hbound ω x hx)).1
  refine ⟨(measurable_ground_of_continuous B E hcont hb).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := M)
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using abs_ground_le B hB (E ω) (hbound ω))

/-- The same hypotheses close finite-net integrability. -/
theorem integrable_netGround_of_continuous_bounded
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (t : Finset V) (ht : t.Nonempty) (E : Ω → V → ℝ) {M : ℝ}
    (hcont : ∀ x ∈ t, Continuous (fun ω => E ω x))
    (hbound : ∀ ω, ∀ x ∈ t, |E ω x| ≤ M) :
    Integrable (fun ω => netGround t ht (E ω)) μ := by
  simpa only [ground_finset_eq_netGround t ht] using
    integrable_ground_of_continuous_bounded μ (↑t : Set V) ht.to_set E hcont hbound

/-- Empirical energies are continuous in the sampled row forms at each state. -/
theorem continuous_energy_in_rows
    (d : ℕ) (ell : Ω → ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hell : ∀ i x, Continuous (fun ω => ell ω i x)) (x : V) :
    Continuous (fun ω => energy d (ell ω) φ x) := by
  unfold energy
  exact (continuous_finset_sum _ (fun i _ => hφ.comp (hell i x))).div_const _

/-- A ready-to-use integrability theorem for the actual bounded empirical
potential, retaining no assumed integrability of its continuum ground energy. -/
theorem integrable_energy_ground
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) (ell : Ω → ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφcont : Continuous φ) {M : ℝ} (hφbound : ∀ u, |φ u| ≤ M)
    (hell : ∀ i x, Continuous (fun ω => ell ω i x))
    (B : Set V) (hB : B.Nonempty) :
    Integrable (fun ω => ground B (energy d (ell ω) φ)) μ := by
  exact integrable_ground_of_continuous_bounded μ B hB _
    (fun x _ => continuous_energy_in_rows d ell φ hφcont hell x)
    (fun ω x _ => abs_energy_le d (ell ω) φ hφbound x)

end Integrability

section Expectation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Exact bounded good-event extension, with a linear failure-probability cost.
The functions' integrability remains an explicit, checkable hypothesis. -/
theorem integral_abs_gap_le_good_add_bad
    (a b : Ω → ℝ) (ha : Integrable a μ) (hb : Integrable b μ)
    (bad : Set Ω) (hbad : MeasurableSet bad) {δ M : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ ω ∉ bad, |a ω-b ω| ≤ δ)
    (hbound : ∀ ω, |a ω-b ω| ≤ 2*M) :
    (∫ ω, |a ω-b ω| ∂μ) ≤ δ+2*M*μ.real bad := by
  have hi : Integrable (fun ω => δ+bad.indicator (fun _ => 2*M) ω) μ :=
    (integrable_const δ).add ((integrable_const (2*M)).indicator hbad)
  have hpoint (ω : Ω) : |a ω-b ω| ≤ δ+bad.indicator (fun _ => 2*M) ω := by
    by_cases hω : ω ∈ bad
    · simp only [Set.indicator_of_mem hω]
      linarith [hbound ω]
    · simpa only [Set.indicator_of_notMem hω, add_zero] using hgood ω hω
  have hm := integral_mono (ha.sub hb).abs hi hpoint
  rw [integral_add (integrable_const δ) ((integrable_const (2*M)).indicator hbad),
    integral_const, integral_indicator_const _ hbad] at hm
  simpa only [probReal_univ, one_smul, smul_eq_mul, one_mul, Pi.sub_apply, mul_comm (μ.real bad)] using hm

/-- Bounded good-event control directly bounds the difference of expectations. -/
theorem abs_integral_gap_le_good_add_bad
    (a b : Ω → ℝ) (ha : Integrable a μ) (hb : Integrable b μ)
    (bad : Set Ω) (hbad : MeasurableSet bad) {δ M : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ ω ∉ bad, |a ω-b ω| ≤ δ)
    (hbound : ∀ ω, |a ω-b ω| ≤ 2*M) :
    |(∫ ω, a ω ∂μ)-(∫ ω, b ω ∂μ)| ≤ δ+2*M*μ.real bad := by
  rw [← integral_sub ha hb]
  exact abs_integral_le_integral_abs.trans
    (integral_abs_gap_le_good_add_bad μ a b ha hb bad hbad hδ hgood hbound)

/-- The actual finite-net and continuum ground energies, integrated over any
probability law, differ by at most Kη plus twice the energy bound times failure
probability. No abstract convergence wrapper or assumed ground-state gap occurs. -/
theorem integral_abs_netGround_sub_ground_le
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty)
    (E : Ω → V → ℝ) {K η M : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hsub : ∀ y ∈ t, y ∈ B) (hnet : ∀ x ∈ B, ∃ y ∈ t, ‖x-y‖ ≤ η)
    (bad : Set Ω) (hbad : MeasurableSet bad)
    (hbound : ∀ ω, ∀ x ∈ B, |E ω x| ≤ M)
    (hLip : ∀ ω ∉ bad, ∀ x ∈ B, ∀ y ∈ B, |E ω x-E ω y| ≤ K*‖x-y‖)
    (hintNet : Integrable (fun ω => netGround t ht (E ω)) μ)
    (hintGround : Integrable (fun ω => ground B (E ω)) μ) :
    (∫ ω, |netGround t ht (E ω)-ground B (E ω)| ∂μ) ≤ K*η+2*M*μ.real bad := by
  apply integral_abs_gap_le_good_add_bad μ _ _ hintNet hintGround bad hbad (mul_nonneg hK hη)
  · intro ω hω
    have hb : BddBelow ((E ω) '' B) := by
      refine ⟨-M, ?_⟩
      rintro _ ⟨x,hx,rfl⟩
      exact (abs_le.mp (hbound ω x hx)).1
    exact abs_netGround_sub_ground_le B hB t ht (E ω) hb hsub hK hnet (hLip ω hω)
  · intro ω
    calc
      |netGround t ht (E ω)-ground B (E ω)| ≤
          |netGround t ht (E ω)|+|ground B (E ω)| := abs_sub _ _
      _ ≤ M+M := add_le_add (abs_netGround_le t ht (E ω) (fun x hx => hbound ω x (hsub x hx)))
        (abs_ground_le B hB (E ω) (hbound ω))
      _ = _ := by ring

/-- Complete expectation extension for any sample law of actual continuous
linear rows, including a GOE law. Bounded potential and row continuity discharge
both finite-net and continuum-ground integrability inside the theorem. -/
theorem integral_abs_net_energy_ground_le
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (d : ℕ) (hd : 0 < d) (ell : Ω → ι → V →L[ℝ] ℝ) (φ : ℝ → ℝ)
    {L C η M : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hφcont : Continuous φ) (hφ : ∀ u v, |φ u-φ v| ≤ L*|u-v|)
    (hφbound : ∀ u, |φ u| ≤ M)
    (hell : ∀ i x, Continuous (fun ω => ell ω i x))
    (B : Set V) (hB : B.Nonempty) (t : Finset V) (ht : t.Nonempty)
    (hsub : ∀ y ∈ t, y ∈ B) (hnet : ∀ x ∈ B, ∃ y ∈ t, ‖x-y‖ ≤ η)
    (bad : Set Ω) (hbad : MeasurableSet bad)
    (hL1 : ∀ ω ∉ bad, ∀ H : V, (∑ i, |ell ω i H|) ≤ C*‖H‖) :
    (∫ ω, |netGround t ht (energy d (ell ω) φ)-ground B (energy d (ell ω) φ)| ∂μ) ≤
      L*C*η/(d:ℝ)^2+2*((Fintype.card ι:ℝ)*M/(d:ℝ)^2)*μ.real bad := by
  have hiG := integrable_energy_ground μ d ell φ hφcont hφbound hell B hB
  have hiN := integrable_netGround_of_continuous_bounded μ t ht
    (fun ω => energy d (ell ω) φ)
    (fun x _ => continuous_energy_in_rows d ell φ hφcont hell x)
    (fun ω x _ => abs_energy_le d (ell ω) φ hφbound x)
  have h := integral_abs_netGround_sub_ground_le μ B hB t ht
    (fun ω => energy d (ell ω) φ)
    (div_nonneg (mul_nonneg hL hC) (sq_nonneg (d:ℝ))) hη hsub hnet bad hbad
    (fun ω x _ => abs_energy_le d (ell ω) φ hφbound x)
    (fun ω hω x _ y _ => energy_lipschitz d hd (ell ω) φ hL hφ (hL1 ω hω) x y)
    hiN hiG
  convert h using 1 <;> ring

end Expectation

section GaussianQuadraticApplication
open BMUniformMoment BMQuadraticSpectral GaussianMixedNormHelpers

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) := Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) := Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (gaussianSampleLaw d n) := by
  unfold gaussianSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (euclideanGaussianLaw (Fin d)) := fun _ => euclideanGaussianLaw_probability (Fin d)
  exact Measure.pi.instIsProbabilityMeasure (fun _ : Fin n => euclideanGaussianLaw (Fin d))

/-- The actual centered, d^(-1/2)-normalized quadratic measurement as a
continuous linear row on the symmetric-operator space with operator norm. -/
def quadraticRow {d : ℕ} (x : BMQuadraticSpectral.Euclid d) : SymOp d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := SymOp d) (F' := ℝ)
    { toFun := fun T => normalizedQuadratic T.val x
      map_add' := by
        intro T U
        simp [normalizedQuadratic, inner_add_right, add_div, add_sub_add_comm]
      map_smul' := by
        intro c T
        simp [normalizedQuadratic, inner_smul_right, mul_sub, mul_div_assoc]
        ring }

@[simp] theorem quadraticRow_apply {d : ℕ} (x : BMQuadraticSpectral.Euclid d) (T : SymOp d) :
    quadraticRow x T = normalizedQuadratic T.val x := rfl

/-- On the proved Gaussian fractional-moment event, the actual quadratic rows
have the required uniform homogeneous empirical L1 bound. -/
theorem quadratic_rows_uniform_L1 {d n : ℕ}
    (x : Fin n → BMQuadraticSpectral.Euclid d) {K : ℝ} (hK : 0 ≤ K)
    (hgood : ∀ T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d,
      T.toLinearMap.IsSymmetric → ‖T‖ ≤ 1 →
      (∑ i, |normalizedQuadratic T (x i)|^((6:ℝ)/5)) ≤ K*n) :
    ∀ H : SymOp d, (∑ i, |quadraticRow (x i) H|) ≤ ((1+K)*n)*‖H‖ := by
  have hm (H : SymOp d) (hH : ‖H‖ ≤ 1) :
      (∑ i, |quadraticRow (x i) H|^((6:ℝ)/5)) ≤ K*(Fintype.card (Fin n) : ℝ) := by
    simpa only [quadraticRow_apply, Fintype.card_fin] using hgood H.val H.property hH
  simpa only [Fintype.card_fin] using
    uniform_L1_of_fractional_moment (V := SymOp d) (ι := Fin n) (fun i => quadraticRow (x i)) (by norm_num : (1:ℝ) ≤ 6/5) hK hm

/-- Actual operator-net ground-state approximation on an exponentially likely
Gaussian-sample event. The constant is uniform over dimension, sample count,
constraint set, and finite net, in any fixed proportional n/d² window.
This is the centered rank-one (Ellipse) input to BM's expectation argument. -/
theorem exists_gaussian_net_ground_event
    (a A : ℝ) (ha : 0 < a) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ d n : ℕ, 0 < d → 0 < n →
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∃ good : Set (Fin n → BMQuadraticSpectral.Euclid d), MeasurableSet good ∧
        (gaussianSampleLaw d n).real goodᶜ ≤ Real.exp (-(n:ℝ)) ∧
        ∀ x ∈ good, ∀ φ : ℝ → ℝ, ∀ L : ℝ, 0 ≤ L →
          (∀ u v, |φ u-φ v| ≤ L*|u-v|) → (∀ u, 0 ≤ φ u) →
          ∀ B : Set (SymOp d), B.Nonempty →
          ∀ (t : Finset (SymOp d)) (ht : t.Nonempty), (∀ y ∈ t, y ∈ B) →
          ∀ η : ℝ, 0 ≤ η → (∀ T ∈ B, ∃ U ∈ t, ‖T-U‖ ≤ η) →
          |netGround t ht (energy (V := SymOp d) (ι := Fin n) d (fun i => quadraticRow (x i)) φ)-
            ground B (energy (V := SymOp d) (ι := Fin n) d (fun i => quadraticRow (x i)) φ)| ≤ L*C*η := by
  obtain ⟨K,hK,hEvent⟩ := exists_uniform_fractional_constant a A ha hA
  refine ⟨(1+K)*A, mul_pos (by linarith) (by linarith), ?_⟩
  intro d n hd hn hlow hhigh
  obtain ⟨good,hgood,hq,hbad⟩ := hEvent d n hd hn hlow hhigh
  refine ⟨good,hgood,hbad,?_⟩
  intro x hx φ L hL hφ hφnonneg B hB t ht hsub η hη hnet
  have hL1 := quadratic_rows_uniform_L1 x hK.le (hq x hx)
  have h := abs_net_energy_ground_le (V := SymOp d) (ι := Fin n) d hd (fun i => quadraticRow (x i)) φ hL
    (by positivity : 0 ≤ (1+K)*(n:ℝ)) hφ hφnonneg hL1 B hB t ht hsub hnet
  apply h.trans
  have hd2 : 0 < (d:ℝ)^2 := by positivity
  apply (div_le_iff₀ hd2).2
  have hm := mul_le_mul_of_nonneg_left hhigh (mul_nonneg (mul_nonneg hL (by linarith : 0 ≤ 1+K)) hη)
  nlinarith

/-- Every nonempty operator-bounded constraint set admits a genuine internal
finite net with the BM logarithmic entropy scaling d². -/
theorem exists_operator_net {d : ℕ} (B : Set (SymOp d)) (hB : B.Nonempty)
    {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) (hbound : ∀ T ∈ B, ‖T‖ ≤ R) :
    ∃ t : Finset (SymOp d), t.Nonempty ∧ (∀ T ∈ t, T ∈ B) ∧
      (∀ T ∈ B, ∃ U ∈ t, ‖T-U‖ ≤ η) ∧
      Real.log (t.card : ℝ) ≤ (d:ℝ)^2*Real.log (1+2*R/η) := by
  obtain ⟨t,ht,hcard,hnet,_⟩ := GaussianEllipsoid.exists_internal_net B hR hη hbound
  have htn : t.Nonempty := by
    obtain ⟨T,hT⟩ := hB
    obtain ⟨U,hU,_⟩ := hnet T hT
    exact ⟨U,hU⟩
  refine ⟨t,htn,ht,?_,?_⟩
  · intro T hT
    obtain ⟨U,hU,hdist⟩ := hnet T hT
    exact ⟨U,hU,by simpa only [dist_eq_norm] using hdist.le⟩
  · have hbase : 1 ≤ 1+2*R/η := by
      have : 0 ≤ 2*R/η := by positivity
      linarith
    have hc : (t.card:ℝ) ≤ (1+2*R/η)^(d*d) :=
      hcard.trans (pow_le_pow_right₀ hbase (symmetricOperators_finrank_le d))
    have hn : (0:ℝ) < t.card := by exact_mod_cast htn.card_pos
    have hl := Real.log_le_log hn hc
    rw [Real.log_pow] at hl
    simpa only [Nat.cast_mul, pow_two] using hl

/-- The conventional BM entropy form with K=1+2R and 0<η≤1. -/
theorem exists_operator_net_log_bound {d : ℕ} (B : Set (SymOp d)) (hB : B.Nonempty)
    {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbound : ∀ T ∈ B, ‖T‖ ≤ R) :
    ∃ t : Finset (SymOp d), t.Nonempty ∧ (∀ T ∈ t, T ∈ B) ∧
      (∀ T ∈ B, ∃ U ∈ t, ‖T-U‖ ≤ η) ∧
      Real.log (t.card : ℝ) ≤ (d:ℝ)^2*Real.log ((1+2*R)/η) := by
  obtain ⟨t,ht,hsub,hnet,hcard⟩ := exists_operator_net B hB hR hη hbound
  refine ⟨t,ht,hsub,hnet,hcard.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.log_le_log (by positivity)
  apply (le_div_iff₀ hη).2
  calc
    (1+2*R/η)*η = η+2*R := by field_simp
    _ ≤ 1+2*R := add_le_add_left hη1 _

/-- Every actual centered quadratic row is continuous in its Gaussian sample. -/
theorem continuous_quadraticRow_sample {d n : ℕ} (i : Fin n) (T : SymOp d) :
    Continuous (fun x : Fin n → BMQuadraticSpectral.Euclid d => quadraticRow (x i) T) := by
  simp only [quadraticRow_apply, normalizedQuadratic]
  fun_prop

/-- The actual continuum quadratic-sample ground energy is integrable for every
finite sample law and every bounded continuous potential, without assuming the
integrability of the infimum as a hypothesis. -/
theorem integrable_quadratic_energy_ground {d n : ℕ}
    (μ : Measure (Fin n → BMQuadraticSpectral.Euclid d)) [IsFiniteMeasure μ]
    (φ : ℝ → ℝ) (hφcont : Continuous φ) {M : ℝ} (hφbound : ∀ u, |φ u| ≤ M)
    (B : Set (SymOp d)) (hB : B.Nonempty) :
    Integrable (fun x => ground B
      (energy (V := SymOp d) (ι := Fin n) d (fun i => quadraticRow (x i)) φ)) μ := by
  exact integrable_energy_ground (V := SymOp d) (ι := Fin n) μ d
    (fun x i => quadraticRow (x i)) φ hφcont hφbound continuous_quadraticRow_sample B hB

set_option maxHeartbeats 300000 in
/-- Full expectation-level operator-net extension for the actual centered
rank-one Gaussian measurements. Failure costs only exp(−n); all integrability,
operator norms, finite minima and continuum infima are proved concretely. -/
theorem exists_gaussian_expected_net_ground_bound
    (a A : ℝ) (ha : 0 < a) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ d n : ℕ, 0 < d → 0 < n →
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ φ : ℝ → ℝ, ∀ L M : ℝ, 0 ≤ L → 0 ≤ M →
      Continuous φ → (∀ u v, |φ u-φ v| ≤ L*|u-v|) →
      (∀ u, 0 ≤ φ u) → (∀ u, |φ u| ≤ M) →
      ∀ B : Set (SymOp d), B.Nonempty →
      ∀ (t : Finset (SymOp d)) (ht : t.Nonempty), (∀ T ∈ t, T ∈ B) →
      ∀ η : ℝ, 0 ≤ η → (∀ T ∈ B, ∃ U ∈ t, ‖T-U‖ ≤ η) →
      (∫ x, |netGround t ht
          (energy (V := SymOp d) (ι := Fin n) d (fun i => quadraticRow (x i)) φ)-
        ground B (energy (V := SymOp d) (ι := Fin n) d (fun i => quadraticRow (x i)) φ)|
          ∂gaussianSampleLaw d n) ≤ L*C*η+2*A*M*Real.exp (-(n:ℝ)) := by
  obtain ⟨K,hK,hEvent⟩ := exists_uniform_fractional_constant a A ha hA
  refine ⟨(1+K)*A, mul_pos (by linarith) (by linarith),?_⟩
  intro d n hd hn hlow hhigh φ L M hL hM hφcont hφ hφnonneg hφbound B hB t ht hsub η hη hnet
  obtain ⟨good,hgood,hq,hbad⟩ := hEvent d n hd hn hlow hhigh
  have hL1 : ∀ x ∉ goodᶜ, ∀ H : SymOp d,
      (∑ i, |quadraticRow (x i) H|) ≤ ((1+K)*n)*‖H‖ := by
    intro x hx
    exact quadratic_rows_uniform_L1 x hK.le (hq x (by simpa using hx))
  have hmean := integral_abs_net_energy_ground_le (V := SymOp d) (ι := Fin n)
    (gaussianSampleLaw d n) d hd (fun x i => quadraticRow (x i)) φ hL
    (by positivity : 0 ≤ (1+K)*(n:ℝ)) hη hφcont hφ hφbound
    continuous_quadraticRow_sample B hB t ht hsub hnet goodᶜ hgood.compl hL1
  simp only [Fintype.card_fin] at hmean
  apply hmean.trans
  have hd2 : 0 < (d:ℝ)^2 := by positivity
  have hfirst : L*((1+K)*(n:ℝ))*η/(d:ℝ)^2 ≤ L*((1+K)*A)*η := by
    apply (div_le_iff₀ hd2).2
    have hm := mul_le_mul_of_nonneg_left hhigh
      (mul_nonneg (mul_nonneg hL (by linarith : 0 ≤ 1+K)) hη)
    nlinarith
  have hsecond : (n:ℝ)*M/(d:ℝ)^2 ≤ A*M := by
    apply (div_le_iff₀ hd2).2
    nlinarith [mul_le_mul_of_nonneg_right hhigh hM]
  have hpnonneg : 0 ≤ (gaussianSampleLaw d n).real goodᶜ := ENNReal.toReal_nonneg
  have hm1 := mul_le_mul_of_nonneg_right hsecond hpnonneg
  have hm2 := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ A*M)
  nlinarith

end GaussianQuadraticApplication

#print axioms integral_abs_net_energy_ground_le
#print axioms exists_gaussian_expected_net_ground_bound
#print axioms integrable_quadratic_energy_ground
#print axioms exists_operator_net
#print axioms exists_operator_net_log_bound
#print axioms integrable_energy_ground
#print axioms integrable_netGround_of_continuous_bounded
#print axioms exists_gaussian_net_ground_event
#print axioms quadratic_rows_uniform_L1
#print axioms integral_abs_netGround_sub_ground_le
#print axioms abs_integral_gap_le_good_add_bad
#print axioms uniform_L1_of_fractional_moment
#print axioms abs_net_energy_ground_le
#print axioms netGround_eq_finite_ground
#print axioms sum_abs_le_of_unit_ball

end BMNetGroundExtension
