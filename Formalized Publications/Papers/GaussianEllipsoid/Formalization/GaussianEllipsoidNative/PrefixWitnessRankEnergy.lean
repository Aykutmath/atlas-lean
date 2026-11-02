import ActualCapturedCross
import AdaptedPrefixWitness
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option maxHeartbeats 400000
open Module GaussianEllipsoid GaussianEllipsoidCandidate MeasureTheory
open scoped BigOperators
namespace GaussianEllipsoid

theorem prefixBlockWitness_right_prefix {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L t : ℕ} (hKL : K ≤ L) (hLt : L ≤ t) :
    prefixBlockWitness u X K L ∘L rightPrefixProjector X t = prefixBlockWitness u X K L := by
  have h := (prefixBlockWitness_properties u X hKL).2.1
  have he : rightIncrement X K L ∘L rightPrefixProjector X t = rightIncrement X K L := by
    change (prefixSpanProjector (fun i => (X i).1) L -
      prefixSpanProjector (fun i => (X i).1) K) ∘L
      prefixSpanProjector (fun i => (X i).1) t = _
    rw [ContinuousLinearMap.sub_comp, prefixSpanProjector_comp_of_le _ hLt,
      prefixSpanProjector_comp_of_le _ (hKL.trans hLt)]
    rfl
  calc
    _ = (leftIncrement X K L ∘L prefixBlockWitness u X K L ∘L rightIncrement X K L)
        ∘L rightPrefixProjector X t := by rw [h]
    _ = leftIncrement X K L ∘L prefixBlockWitness u X K L ∘L
        (rightIncrement X K L ∘L rightPrefixProjector X t) := by simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [he,h]

theorem completedPrefixWitness_right_prefix {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    completedPrefixWitness u lo hi X t ∘L rightPrefixProjector X t =
      completedPrefixWitness u lo hi X t := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [completedPrefixWitness,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : hi j ≤ t
  · simp only [if_pos hj]
    exact congrArg (fun W : Euclid q →L[ℝ] Euclid r => W z)
      (prefixBlockWitness_right_prefix u X (hlo j) hj)
  · simp only [if_neg hj,ContinuousLinearMap.zero_apply]

/-- Rank-sensitive energy of the actual measurable aggregate, before replacing
its supporting prefix by the ambient dimension. -/
theorem completedPrefixWitness_energy_le_prefix_rank {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    ‖operatorFrobenius (completedPrefixWitness u lo hi X t)‖^2 ≤
      (finrank ℝ (Submodule.span ℝ ((fun i => (X i).1) '' {i : Fin n | i.val < t})) : ℝ) := by
  have h := frobenius_supported_contraction_sq_le_rank
    (completedPrefixWitness u lo hi X t) (rightPrefixProjector X t)
    (norm_completedPrefixWitness_le_one u lo hi hlo hsep X t)
    (prefixSpanProjector_selfAdjoint _ t)
    (prefixSpanProjector_comp_of_le _ (le_refl t))
    (completedPrefixWitness_right_prefix u lo hi hlo X t)
  have hr : LinearMap.range (rightPrefixProjector X t).toLinearMap =
      Submodule.span ℝ ((fun i => (X i).1) '' {i : Fin n | i.val < t}) := by
    unfold rightPrefixProjector
    rw [prefixSpanProjector_eq]
    exact Submodule.range_starProjection _
  rwa [hr] at h
theorem prefix_span_finrank_le {n q : ℕ} (f : Fin n → Euclid q) (t : ℕ) :
    finrank ℝ (Submodule.span ℝ (f '' {i : Fin n | i.val < t})) ≤ t := by
  classical
  let g : {i : Fin n // i.val < t} → Euclid q := fun i => f i.val
  have heq : f '' {i : Fin n | i.val < t} = Set.range g := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
  rw [heq]
  have hcard : Fintype.card {i : Fin n // i.val < t} ≤ t := by
    have hi : Function.Injective (fun i : {i : Fin n // i.val < t} => (⟨i.val.val,i.property⟩ : Fin t)) := by
      intro i j hij
      apply Subtype.ext
      exact Fin.ext (congrArg (fun z : Fin t => z.val) hij)
    simpa using Fintype.card_le_of_injective _ hi
  calc
    _ ≤ (Set.range g).toFinset.card := finrank_span_le_card _
    _ = Fintype.card (Set.range g) := Set.toFinset_card _
    _ ≤ Fintype.card {i : Fin n // i.val < t} := Fintype.card_range_le g
    _ ≤ t := hcard

/-- Actual prefix length, rather than ambient row dimension, controls energy. -/
theorem completedPrefixWitness_energy_le_prefix_length {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u : Fin n → ℝ) (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (t : ℕ) :
    ‖operatorFrobenius (completedPrefixWitness u lo hi X t)‖^2 ≤ (t:ℝ) :=
  (completedPrefixWitness_energy_le_prefix_rank u lo hi hlo hsep X t).trans
    (by exact_mod_cast prefix_span_finrank_le (fun i => (X i).1) t)

/-- The Bernstein bound with the actual rank-sensitive variance sum. -/
theorem prefixWitnessCross_rank_weighted_lower_tail {ι : Type*} [Fintype ι]
    {N r q : ℕ} (u v : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j) (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hcoef : ∀ i, (v i)^2 ≤ b^2/2)
    (hvar : (∑ i, (v i)^2 * (i.val:ℝ)) ≤ V) :
    (gaussianBilinearSampleLaw (Fin N) q r).real {X | prefixWitnessCross u v lo hi X ≤ -x} ≤
      Real.exp (-(1/4 : ℝ) * min (x^2/V) (x/b)) := by
  have hcap : ∀ k, (extendCoefficient v k)^2 ≤ b^2/2 := by
    intro k
    unfold extendCoefficient
    split_ifs with hk
    · exact hcoef ⟨k,hk⟩
    · nlinarith [sq_nonneg b]
  have hv : (∑ k ∈ Finset.range N, (extendCoefficient v k)^2 * (k : ℝ)) ≤ V := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [extendCoefficient,Fin.isLt,dif_pos] using hvar
  have h := gaussianRowSum_lower_tail (adaptedPrefixWitness (r := r) (q := q) u lo hi)
    (measurable_adaptedPrefixWitness u lo hi)
    (norm_adaptedPrefixWitness_le_one u lo hi hlo hsep) (fun k => (k : ℝ))
    (extendCoefficient v) (fun k X => completedPrefixWitness_energy_le_prefix_length
      u lo hi hlo hsep (zeroExtendRows N X) k) N V b x hV hb hx hcap hv
  simpa only [← prefixWitnessCross_eq_rowSum u v lo hi hlo] using h
end GaussianEllipsoid
#print axioms GaussianEllipsoid.completedPrefixWitness_energy_le_prefix_rank


noncomputable section
set_option maxHeartbeats 600000
open Finset Module GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoidCandidate

theorem actual_group_energy_mul_scale {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ dyadicGroupSupport u amp groups T r, (u i)^2) * dyadicGroupScale u amp groups r ≤
      (32/3:ℝ)*(dyadicGroupMass u amp groups T r)^2 := by
  obtain ⟨t, tail, heq, hS, ha, hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, hcap, htail⟩ := hreg groups[r] (List.getElem_mem hr)
  have hh := (le_div_iff₀ hS).mp henergy
  simpa only [dyadicGroupScale, dyadicGroupMass, dyadicGroupSupport,
    List.getElem?_eq_getElem hr, Option.getD_some, heq, List.headD_cons, List.tail_cons] using hh

/-- The actual row-order index is bounded by the through-group support, which
is geometric in the current group's record size. -/
theorem actual_group_ordered_energy_le {n : ℕ} (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ dyadicGroupSupport u amp groups T r,
      (u i)^2 * ((actualDyadicSupportPermutation u amp ha groups T hreg hflat i).val:ℝ)) ≤
      (128/3:ℝ)*T*(dyadicGroupMass u amp groups T r)^2 := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  have htime : ∀ i ∈ dyadicGroupSupport u amp groups T r,
      ((e i).val:ℝ) ≤ 4*T*dyadicGroupScale u amp groups r := by
    intro i hi
    have hh := ((actualDyadicSupportPermutation_group u amp ha groups T hreg hflat r hr i).mp hi).2
    have hc : ((e i).val:ℝ) ≤ (supportCut (dyadicGroupSupport u amp groups T) (r+1):ℝ) := by
      exact_mod_cast hh.le
    rw [actual_dyadic_supportCut_cast] at hc
    exact hc.trans (actual_group_prefix_bounds u amp groups T hreg hchain r hr).2
  calc
    _ ≤ ∑ i ∈ dyadicGroupSupport u amp groups T r,
        (u i)^2*(4*T*dyadicGroupScale u amp groups r) :=
      sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (htime i hi) (sq_nonneg _))
    _ = (4*T)*((∑ i ∈ dyadicGroupSupport u amp groups T r,(u i)^2)*dyadicGroupScale u amp groups r) := by
      rw [← Finset.sum_mul]; ring
    _ ≤ (4*T)*((32/3:ℝ)*(dyadicGroupMass u amp groups T r)^2) :=
      mul_le_mul_of_nonneg_left (actual_group_energy_mul_scale u amp groups T hreg r hr) (by positivity)
    _ = _ := by ring

/-- Exact rank-weighted deterministic variance envelope. The logarithmic loss
from the ambient-rank estimate disappears at this step. -/
theorem actual_retained_rank_weighted_energy {n : ℕ} (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card)) :
    (∑ i, (retainedGroupVector u amp groups T i)^2 *
      ((actualDyadicSupportPermutation u amp ha groups T hreg hflat i).val:ℝ)) ≤
      (128/3:ℝ)*T*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  classical
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  have heq : (∑ i, (retainedGroupVector u amp groups T i)^2*((e i).val:ℝ)) =
      ∑ r ∈ range groups.length, ∑ i ∈ dyadicGroupSupport u amp groups T r,
        (u i)^2*((e i).val:ℝ) := by
    simp only [retainedGroupVector]
    simp_rw [ite_pow,zero_pow (by decide : 2 ≠ 0),ite_mul,zero_mul]
    rw [Finset.sum_ite_mem_eq,retainedGroupUnion_eq_indexed,indexedGroupUnion]
    convert! (Finset.sum_biUnion (f := fun i => (u i)^2*((e i).val:ℝ))
      (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)) using 1
    congr 1
    ext i
    simp only [Finset.mem_biUnion]
  rw [heq,actual_group_mass_sum u amp ha groups T hreg hflat]
  calc
    _ ≤ ∑ r ∈ range groups.length, (128/3:ℝ)*T*(dyadicGroupMass u amp groups T r)^2 :=
      sum_le_sum (fun r hr => actual_group_ordered_energy_le u amp ha groups T hreg hflat hchain r (mem_range.mp hr))
    _ = (128/3:ℝ)*T*(∑ r ∈ range groups.length,(dyadicGroupMass u amp groups T r)^2) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_sq_le_sq_sum_of_nonneg (fun r _ => sum_nonneg (fun i _ => abs_nonneg (u i)))) (by positivity)

/-- The actual predictable group variance has order M²/d, with no log d.
The witness is the constructed measurable orthogonal polar aggregate. -/
theorem actual_group_predictable_variance_le {ι : Type*} [Fintype ι] {n r q : ℕ}
    (u w : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (lo hi : ι → ℕ) (hlo : ∀ j,lo j ≤ hi j)
    (hsep : ∀ i j,i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (X : Fin n → Euclid q × Euclid r) (d : ℝ) (hd : 0 < d) :
    (∑ j ∈ range groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (completedPrefixWitness w lo hi X
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2 / d) ≤
      ((64/3:ℝ)*T/d)*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  have hterm (j : ℕ) (hj : j ∈ range groups.length) :
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2) *
        ‖operatorFrobenius (completedPrefixWitness w lo hi X
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2 / d ≤
      ((64/3:ℝ)*T/d)*(dyadicGroupMass u amp groups T j)^2 := by
    have henergy := completedPrefixWitness_energy_le_prefix_length w lo hi hlo hsep X
      (supportCut (dyadicGroupSupport u amp groups T) j)
    rw [actual_dyadic_supportCut_cast] at henergy
    have he := henergy.trans (actual_group_prefix_bounds u amp groups T hreg hchain j (mem_range.mp hj)).1
    have hprod := mul_le_mul_of_nonneg_left he
      (sum_nonneg (s := dyadicGroupSupport u amp groups T j) (fun i _ => sq_nonneg (u i)))
    have hQ := actual_group_energy_mul_scale u amp groups T hreg j (mem_range.mp hj)
    have hh := mul_le_mul_of_nonneg_left hQ (show (0:ℝ) ≤ 2*T by positivity)
    apply (div_le_iff₀ hd).mpr
    field_simp [hd.ne']
    nlinarith
  calc
    _ ≤ ∑ j ∈ range groups.length, ((64/3:ℝ)*T/d)*(dyadicGroupMass u amp groups T j)^2 :=
      sum_le_sum hterm
    _ = ((64/3:ℝ)*T/d)*(∑ j ∈ range groups.length,(dyadicGroupMass u amp groups T j)^2) := by
      rw [Finset.mul_sum]
    _ ≤ ((64/3:ℝ)*T/d)*(∑ j ∈ range groups.length,dyadicGroupMass u amp groups T j)^2 :=
      mul_le_mul_of_nonneg_left
        (sum_sq_le_sq_sum_of_nonneg (fun j _ => sum_nonneg (fun i _ => abs_nonneg (u i)))) (by positivity)
    _ = _ := by rw [← actual_group_mass_sum u amp ha groups T hreg hflat]
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.actual_retained_rank_weighted_energy

#print axioms GaussianEllipsoidCandidate.actual_group_predictable_variance_le
#print axioms GaussianEllipsoid.prefixWitnessCross_rank_weighted_lower_tail
#print axioms GaussianEllipsoid.completedPrefixWitness_energy_le_prefix_length
