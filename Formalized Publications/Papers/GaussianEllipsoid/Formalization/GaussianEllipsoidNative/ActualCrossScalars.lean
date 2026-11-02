import ActualLateFixedVector

noncomputable section
open Finset GaussianEllipsoid
namespace GaussianEllipsoidCandidate

/-- Every indexed retained support is in the global retained support. -/
theorem actual_group_subset_retained {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hr : r < groups.length) :
    dyadicGroupSupport u amp groups T r ⊆ retainedGroupUnion u amp groups T := by
  classical
  intro i hi
  unfold retainedGroupUnion
  apply mem_biUnion.mpr
  refine ⟨groups[r], List.mem_toFinset.mpr (List.getElem_mem hr), ?_⟩
  simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr, Option.getD_some] using hi

/-- The concrete retained mass is exactly its restricted original mass. -/
theorem retained_mass_eq_support_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) :
    coefficientMass (retainedGroupVector u amp groups T) =
      ∑ i ∈ retainedGroupUnion u amp groups T, |u i| := by
  classical
  simp only [coefficientMass, retainedGroupVector]
  simp_rw [apply_ite abs]
  simp

/-- A group's mass is bounded by the full retained mass. -/
theorem actual_group_mass_le_retained {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hr : r < groups.length) :
    dyadicGroupMass u amp groups T r ≤ coefficientMass (retainedGroupVector u amp groups T) := by
  rw [retained_mass_eq_support_sum]
  exact sum_le_sum_of_subset_of_nonneg (actual_group_subset_retained u amp groups T r hr)
    (fun i _ _ => abs_nonneg _)

/-- Concrete regularity yields the cap without introducing any random witness. -/
theorem actual_group_coefficient_mul_scale {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) (i : ι)
    (hi : i ∈ dyadicGroupSupport u amp groups T r) :
    |u i| * dyadicGroupScale u amp groups r ≤ 2*dyadicGroupMass u amp groups T r := by
  obtain ⟨t, tail, heq, hS, ha, hklo, hkhi, hmlo, hmhi, hQlo, hQhi,
    hm, hQ, hRlo, hRhi, henergy, hcap, htail⟩ := hreg groups[r] (List.getElem_mem hr)
  have hi' : i ∈ recordRetainedSupport u amp t tail T := by
    simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr, Option.getD_some,
      heq, List.headD_cons, List.tail_cons] using hi
  have hh := (hcap i hi').2.2
  have hh' := (le_div_iff₀ hS).mp hh
  simpa only [dyadicGroupScale, dyadicGroupMass, dyadicGroupSupport,
    List.getElem?_eq_getElem hr, Option.getD_some, heq, List.headD_cons, List.tail_cons] using hh'

/-- Every post-prefix actual coefficient is small in terms of the common
minimum scale and full retained mass. -/
theorem actual_group_coefficient_le_of_scale_lower {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) (i : ι)
    (hi : i ∈ dyadicGroupSupport u amp groups T r) (Smin : ℝ) (hSmin : 0 < Smin)
    (hS : Smin ≤ dyadicGroupScale u amp groups r) :
    |u i| ≤ 2*coefficientMass (retainedGroupVector u amp groups T)/Smin := by
  apply (le_div_iff₀ hSmin).mpr
  calc
    |u i| *Smin ≤ |u i| *dyadicGroupScale u amp groups r :=
      mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    _ ≤ 2*dyadicGroupMass u amp groups T r :=
      actual_group_coefficient_mul_scale u amp groups T hreg r hr i hi
    _ ≤ 2*coefficientMass (retainedGroupVector u amp groups T) :=
      mul_le_mul_of_nonneg_left (actual_group_mass_le_retained u amp groups T r hr) (by norm_num)

/-- The concrete retained support after the small-support prefix. -/
def postprefixSupport {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) : Finset ι := by
  classical
  exact (Ico p groups.length).biUnion (dyadicGroupSupport u amp groups T)

/-- The actual post-prefix coefficients, with the sparse prefix set to zero. -/
def postprefixCoefficients {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ postprefixSupport u amp groups T p then u i else 0

/-- Actual group cutoffs supply the whole tail's coefficient cap and energy.
The energy bound uses only l∞ times l1, avoiding extra rank bookkeeping. -/
theorem actual_postprefix_cap_energy {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (Smin : ℝ) (hSmin : 0 < Smin)
    (hS : ∀ r, p ≤ r → r < groups.length → Smin ≤ dyadicGroupScale u amp groups r) :
    (∀ i, |postprefixCoefficients u amp groups T p i| ≤
      2*coefficientMass (retainedGroupVector u amp groups T)/Smin) ∧
    (∑ i, (postprefixCoefficients u amp groups T p i)^2) ≤
      2*(coefficientMass (retainedGroupVector u amp groups T))^2/Smin := by
  classical
  let w := postprefixCoefficients u amp groups T p
  let M := coefficientMass (retainedGroupVector u amp groups T)
  have hM : 0 ≤ M := coefficientMass_nonneg _
  have hsub : postprefixSupport u amp groups T p ⊆ retainedGroupUnion u amp groups T := by
    intro i hi
    obtain ⟨r, hr, hir⟩ := mem_biUnion.mp hi
    exact actual_group_subset_retained u amp groups T r (mem_Ico.mp hr).2 hir
  have hcap : ∀ i, |w i| ≤ 2*M/Smin := by
    intro i
    by_cases hi : i ∈ postprefixSupport u amp groups T p
    · change |if i ∈ postprefixSupport u amp groups T p then u i else 0| ≤ _
      rw [if_pos hi]
      obtain ⟨r, hr, hir⟩ := mem_biUnion.mp hi
      exact actual_group_coefficient_le_of_scale_lower u amp groups T hreg r
        (mem_Ico.mp hr).2 i hir Smin hSmin (hS r (mem_Ico.mp hr).1 (mem_Ico.mp hr).2)
    · simp only [w, postprefixCoefficients, if_neg hi, abs_zero]
      positivity
  have hmass : coefficientMass w ≤ M := by
    have heq : coefficientMass w = ∑ i ∈ postprefixSupport u amp groups T p, |u i| := by
      dsimp [w, coefficientMass, postprefixCoefficients]
      simp_rw [apply_ite abs]
      simp
    rw [heq, show M = ∑ i ∈ retainedGroupUnion u amp groups T, |u i| from
      retained_mass_eq_support_sum u amp groups T]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg _)
  refine ⟨hcap, ?_⟩
  calc
    (∑ i, (w i)^2) = ∑ i, |w i| *|w i| := by simp [← sq, sq_abs]
    _ ≤ ∑ i, (2*M/Smin)*|w i| := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hcap i) (abs_nonneg _)
    _ = (2*M/Smin)*coefficientMass w := by rw [coefficientMass, mul_sum]
    _ ≤ (2*M/Smin)*M := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 2*M^2/Smin := by ring

end GaussianEllipsoidCandidate

namespace GaussianEllipsoidCandidate

/-- Substituting the proved post-prefix cutoff yields the concrete row cap
and total coefficient energy required by the ambient-rank martingale proof. -/
theorem actual_postprefix_log_cap_energy {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (d : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d)
    (hS : ∀ r, p ≤ r → r < groups.length →
      d/(65536*T*Real.log d) ≤ dyadicGroupScale u amp groups r) :
    (∀ i, |postprefixCoefficients u amp groups T p i| ≤
      (131072*T*Real.log d/d)*coefficientMass (retainedGroupVector u amp groups T)) ∧
    (∑ i, (postprefixCoefficients u amp groups T p i)^2) ≤
      (131072*T*Real.log d/d)*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hh := actual_postprefix_cap_energy u amp groups T p hreg
    (d/(65536*T*Real.log d)) (by positivity) hS
  constructor
  · intro i
    convert hh.1 i using 1 <;> field_simp <;> ring
  · convert hh.2 using 1 <;> field_simp <;> ring

/-- Exact simplification of the Chernoff exponent for the proved post-prefix
coefficient bounds. This supplies a numerical dimension-quadratic/log tail. -/
theorem actual_cross_chernoff_exponent (d T M : ℝ)
    (hd : 0 < d) (hT : 0 < T) (hM : 0 < M) (hlog : 0 < Real.log d) :
    let V := (2:ℝ)^17*T*Real.log d/d*M^2
    let b := (2:ℝ)^18*T*Real.log d/(d*Real.sqrt d)*M
    let x := (1/2:ℝ)^24*M*Real.sqrt d
    0 < V ∧ 0 < b ∧ 0 ≤ x ∧
      -(1/4:ℝ)*min (x^2/V) (x/b) = -d^2/((2:ℝ)^67*T*Real.log d) := by
  dsimp only
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  have hratio1 : ((1/2:ℝ)^24*M*Real.sqrt d)^2 /
      ((2:ℝ)^17*T*Real.log d/d*M^2) = d^2/((2:ℝ)^65*T*Real.log d) := by
    field_simp [hd.ne', hT.ne', hM.ne', hlog.ne']
    ring_nf
    rw [hsq] <;> ring
  have hratio2 : ((1/2:ℝ)^24*M*Real.sqrt d) /
      ((2:ℝ)^18*T*Real.log d/(d*Real.sqrt d)*M) = d^2/((2:ℝ)^42*T*Real.log d) := by
    field_simp [hd.ne', hT.ne', hM.ne', hlog.ne', hs.ne']
    ring_nf
    rw [hsq] <;> ring
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  rw [hratio1, hratio2, min_eq_left ?_]
  · norm_num
    ring
  · apply div_le_div_of_nonneg_left (sq_nonneg d) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)^42 ≤ 2^65) hT.le) hlog.le

end GaussianEllipsoidCandidate
