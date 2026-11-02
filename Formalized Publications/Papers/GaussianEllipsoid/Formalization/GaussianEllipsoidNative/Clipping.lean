import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Standalone deterministic helpers for Section 11 of the supplied paper.
These declarations do not assert `GaussianEllipsoid.MixedNormBound` and do not
replace any project definition. Their finite-vector quantities are written
explicitly so they can be transported after the project definitions are known.
-/
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
namespace GaussianMixedNormHelpers

/-- Scalar symmetric clipping. -/
def clip (t x : ℝ) : ℝ := max (-t) (min t x)

theorem clip_eq_of_abs_le {t x : ℝ} (h : |x| ≤ t) : clip t x = x := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  simp [clip, min_eq_right hhi, max_eq_right hlo]

theorem clip_abs {t x : ℝ} (ht : 0 ≤ t) : |clip t x| = min t |x| := by
  by_cases hlo : x < -t
  · have hx : x ≤ 0 := by linarith
    simp [clip, min_eq_right (by linarith : x ≤ t),
      max_eq_left (by linarith : x ≤ -t), abs_of_nonpos hx,
      min_eq_left (by linarith : t ≤ -x), abs_of_nonpos (neg_nonpos.mpr ht)]
  · by_cases hhi : t < x
    · have hx : 0 ≤ x := by linarith
      simp [clip, min_eq_left (le_of_lt hhi),
        max_eq_right (by linarith : -t ≤ t), abs_of_nonneg hx,
        abs_of_nonneg ht, min_eq_left (le_of_lt hhi)]
    · have ha : |x| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [clip_eq_of_abs_le ha, min_eq_right ha]

theorem abs_sub_clip {t x : ℝ} (ht : 0 ≤ t) :
    |x - clip t x| = |x| - |clip t x| := by
  by_cases hlo : x < -t
  · have hc : clip t x = -t := by
      simp [clip, min_eq_right (by linarith : x ≤ t), max_eq_left (le_of_lt hlo)]
    rw [hc, abs_of_nonpos (by linarith : x - -t ≤ 0),
      abs_of_nonpos (by linarith : x ≤ 0), abs_of_nonpos (neg_nonpos.mpr ht)]
    ring
  · by_cases hhi : t < x
    · have hc : clip t x = t := by
        simp [clip, min_eq_left (le_of_lt hhi), max_eq_right (by linarith : -t ≤ t)]
      rw [hc, abs_of_nonneg (by linarith : 0 ≤ x - t),
        abs_of_nonneg (by linarith : 0 ≤ x), abs_of_nonneg ht]
    · have ha : |x| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [clip_eq_of_abs_le ha]

theorem clip_mul_residual {t x : ℝ} (ht : 0 ≤ t) :
    clip t x * (x - clip t x) = t * |x - clip t x| := by
  by_cases hlo : x < -t
  · have hc : clip t x = -t := by
      simp [clip, min_eq_right (by linarith : x ≤ t), max_eq_left (le_of_lt hlo)]
    rw [hc, abs_of_nonpos (by linarith : x - -t ≤ 0)]
    ring
  · by_cases hhi : t < x
    · have hc : clip t x = t := by
        simp [clip, min_eq_left (le_of_lt hhi), max_eq_right (by linarith : -t ≤ t)]
      rw [hc, abs_of_nonneg (by linarith : 0 ≤ x - t)]
    · have ha : |x| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      simp [clip_eq_of_abs_le ha]

theorem residual_ne_zero_iff {t x : ℝ} (ht : 0 ≤ t) :
    x - clip t x ≠ 0 ↔ t < |x| := by
  constructor
  · intro h
    by_contra hn
    have ha := clip_eq_of_abs_le (le_of_not_gt hn)
    exact h (by simp [ha])
  · intro h he
    have hx : x = clip t x := sub_eq_zero.mp he
    have hb := clip_abs (x := x) ht
    rw [← hx] at hb
    rw [min_eq_left (le_of_lt h)] at hb
    linarith

variable {ι : Type*} [Fintype ι]

def l1 (y : ι → ℝ) : ℝ := ∑ i, |y i|
def energy (y : ι → ℝ) : ℝ := ∑ i, y i ^ 2
def l2 (y : ι → ℝ) : ℝ := Real.sqrt (energy y)
def clipped (t : ℝ) (y : ι → ℝ) : ι → ℝ := fun i => clip t (y i)
def remainder (t : ℝ) (y : ι → ℝ) : ι → ℝ := y - clipped t y

theorem energy_nonneg (y : ι → ℝ) : 0 ≤ energy y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem l1_nonneg (y : ι → ℝ) : 0 ≤ l1 y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem l2_nonneg (y : ι → ℝ) : 0 ≤ l2 y := Real.sqrt_nonneg _

theorem l2_sq (y : ι → ℝ) : l2 y ^ 2 = energy y :=
  Real.sq_sqrt (energy_nonneg y)

theorem clipping_mass_identity (y : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    l1 (remainder t y) + l1 (clipped t y) = l1 y := by
  unfold l1 remainder clipped
  simp only [Pi.sub_apply]
  simp_rw [abs_sub_clip ht]
  rw [Finset.sum_sub_distrib]
  ring

theorem clipping_pairing_identity (y : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, clipped t y i * remainder t y i) = t * l1 (remainder t y) := by
  unfold clipped remainder l1
  simp only [Pi.sub_apply, clipped]
  simp_rw [clip_mul_residual ht]
  rw [Finset.mul_sum]

theorem clipping_energy_support (y : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun i => t < |y i|)).card : ℝ) * t ^ 2
      ≤ energy (clipped t y) := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => t < |y i|), t ^ 2 := by simp
    _ = ∑ i ∈ Finset.univ.filter (fun i => t < |y i|), clipped t y i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : t < |y i| := (Finset.mem_filter.mp hi).2
      have hc : |clipped t y i| = t := by
        simpa [clipped, min_eq_left (le_of_lt hi')] using clip_abs (x := y i) ht
      nlinarith [sq_abs (clipped t y i)]
    _ ≤ ∑ i, clipped t y i ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact sq_nonneg _
    _ = _ := rfl

theorem pairing_le_l2 (p y : ι → ℝ) : (∑ i, p i * y i) ≤ l2 p * l2 y :=
  Real.sum_mul_le_sqrt_mul_sqrt Finset.univ p y

theorem pairing_le_l1 {a : ℝ} (ha : 0 ≤ a) (p y : ι → ℝ)
    (hp : ∀ i, |p i| ≤ a) : (∑ i, p i * y i) ≤ a * l1 y := by
  calc
    _ ≤ ∑ i, |p i| * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ ∑ i, a * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hp i) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- The actual infimal-convolution definition, on explicitly represented finite vectors. -/
def infimalCost (a b : ℝ) (y : ι → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ u v : ι → ℝ,
    y = u + v ∧ w = a * l1 u + b * l2 v}

theorem infimalCost_le_decomposition {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {y u v : ι → ℝ} (hy : y = u + v) :
    infimalCost a b y ≤ a * l1 u + b * l2 v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro w ⟨u', v', _, rfl⟩
    exact add_nonneg (mul_nonneg ha (l1_nonneg _)) (mul_nonneg hb (l2_nonneg _))
  · exact ⟨u, v, hy, rfl⟩

/-- A finite-dimensional dual certificate proves a decomposition attains the infimum. -/
theorem infimalCost_eq_of_certificate {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {y u v p : ι → ℝ} (hy : y = u + v)
    (hp_inf : ∀ i, |p i| ≤ a) (hp₂ : l2 p ≤ b)
    (hu : (∑ i, p i * u i) = a * l1 u)
    (hv : (∑ i, p i * v i) = b * l2 v) :
    infimalCost a b y = a * l1 u + b * l2 v := by
  apply le_antisymm (infimalCost_le_decomposition ha hb hy)
  apply le_csInf
  · exact ⟨a * l1 u + b * l2 v, u, v, hy, rfl⟩
  · rintro w ⟨u', v', hy', rfl⟩
    have hpy : (∑ i, p i * y i) = a * l1 u + b * l2 v := by
      rw [hy]
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu, hv]
    rw [← hpy, hy']
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    apply add_le_add (pairing_le_l1 ha p u' hp_inf)
    exact (pairing_le_l2 p v').trans
      (mul_le_mul_of_nonneg_right hp₂ (l2_nonneg _))


theorem l2_const_mul (c : ℝ) (y : ι → ℝ) :
    l2 (fun i => c * y i) = |c| * l2 y := by
  unfold l2 energy
  have he : (∑ i, (c * y i) ^ 2) = c ^ 2 * ∑ i, y i ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
  rw [he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- A positive self-consistent threshold gives an exact optimizer and a dual
certificate; this proves the clipping interface without subgradient machinery. -/
theorem clipping_attains_infimalCost {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (ht : 0 < t) (y : ι → ℝ)
    (hbalance : a * l2 (clipped t y) = b * t) :
    infimalCost a b y = a * l1 (remainder t y) + b * l2 (clipped t y) := by
  let v := clipped t y
  let u := remainder t y
  let p : ι → ℝ := fun i => (a / t) * v i
  have hy : y = u + v := by
    ext i
    simp [u, v, remainder]
  have hp_inf : ∀ i, |p i| ≤ a := by
    intro i
    have habs : |v i| ≤ t := by
      simpa [v, clipped, clip_abs (le_of_lt ht)] using min_le_left t |y i|
    calc |p i| = (a / t) * |v i| := by
            simp [p, abs_mul, abs_of_nonneg (le_of_lt (div_pos ha ht))]
      _ ≤ (a / t) * t := mul_le_mul_of_nonneg_left habs (le_of_lt (div_pos ha ht))
      _ = a := div_mul_cancel₀ _ (ne_of_gt ht)
  have hp₂ : l2 p = b := by
    rw [show p = fun i => (a / t) * v i from rfl, l2_const_mul,
      abs_of_nonneg (le_of_lt (div_pos ha ht))]
    change a / t * l2 (clipped t y) = b
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff (ne_of_gt ht)).2 hbalance
  have hu : (∑ i, p i * u i) = a * l1 u := by
    calc
      _ = (a / t) * ∑ i, v i * u i := by
        simp only [p, mul_assoc, Finset.mul_sum]
      _ = (a / t) * (t * l1 u) := by
        rw [clipping_pairing_identity y (le_of_lt ht)]
      _ = _ := by field_simp <;> ring
  have hv : (∑ i, p i * v i) = b * l2 v := by
    calc
      _ = (a / t) * energy v := by
        simp [p, energy, pow_two, Finset.mul_sum, mul_assoc]
      _ = (a / t) * l2 v ^ 2 := by rw [l2_sq]
      _ = b * l2 v := by
        have hb' : a * l2 v = b * t := hbalance
        field_simp
        nlinarith [congrArg (fun z : ℝ => z * l2 v) hb']
  exact infimalCost_eq_of_certificate (le_of_lt ha) hb hy hp_inf hp₂.le hu hv

/-- Every nonzero coordinate has a common positive finite lower bound. -/
theorem exists_positive_below_support (y : ι → ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, y i ≠ 0 → e ≤ |y i| := by
  classical
  let S := Finset.univ.filter (fun i => y i ≠ 0)
  by_cases hS : S.Nonempty
  · let R := S.image (fun i => |y i|)
    have hR : R.Nonempty := Finset.Nonempty.image hS _
    refine ⟨R.min' hR, ?_, ?_⟩
    · apply (Finset.lt_min'_iff R hR).mpr
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact abs_pos.mpr (Finset.mem_filter.mp hi).2
    · intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hi⟩, rfl⟩)
  · refine ⟨1, by norm_num, ?_⟩
    intro i hi
    exact (hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩).elim

/-- Continuous clipped energy, convenient for the threshold intermediate value step. -/
theorem continuous_clipped_energy (y : ι → ℝ) :
    Continuous (fun t : ℝ => energy (clipped t y)) := by
  unfold energy clipped clip
  fun_prop

/-- The exact clipping threshold exists whenever the support exceeds k > 0.
The equation is polynomial in the threshold, with no singularity at zero. -/
theorem exists_clipping_threshold (y : ι → ℝ) {k : ℝ} (hk : 0 < k)
    (hcard : k < ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ energy (clipped t y) = k * t ^ 2 := by
  classical
  obtain ⟨e, he, he_bound⟩ := exists_positive_below_support y
  let R := l2 y / Real.sqrt k + e
  have hroot : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hR : e ≤ R := by
    dsimp [R]
    linarith [div_nonneg (l2_nonneg y) hroot.le]
  have hRe : 0 < R := lt_of_lt_of_le he hR
  have hsmall : energy (clipped e y) =
      ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ) * e ^ 2 := by
    unfold energy
    have hc : ∀ i, clipped e y i ^ 2 = if y i ≠ 0 then e ^ 2 else 0 := by
      intro i
      by_cases hi : y i ≠ 0
      · have habs : |clipped e y i| = e := by
          rw [clipped, clip_abs (le_of_lt he), min_eq_left (he_bound i hi)]
        simp only [if_pos hi]
        nlinarith [sq_abs (clipped e y i)]
      · have hyi : y i = 0 := not_ne_iff.mp hi
        simp [clipped, hyi, clip_eq_of_abs_le (show |(0 : ℝ)| ≤ e by simpa using he.le)]
    simp_rw [hc]
    rw [← Finset.sum_filter]
    simp
  have hlarge : energy (clipped R y) ≤ k * R ^ 2 := by
    have henergy : energy (clipped R y) ≤ energy y := by
      apply Finset.sum_le_sum
      intro i _
      have hc : |clipped R y i| ≤ |y i| := by
        rw [clipped, clip_abs hRe.le]
        exact min_le_right _ _
      nlinarith [sq_abs (clipped R y i), sq_abs (y i), abs_nonneg (y i),
        abs_nonneg (clipped R y i)]
    have hmul : l2 y ≤ Real.sqrt k * R := by
      have hne := ne_of_gt hroot
      dsimp [R]
      rw [mul_add, mul_div_cancel₀ _ hne]
      linarith [mul_nonneg hroot.le he.le]
    have hs := Real.sq_sqrt hk.le
    have hl := l2_sq y
    have hsq : l2 y ^ 2 ≤ (Real.sqrt k * R) ^ 2 :=
      pow_le_pow_left₀ (l2_nonneg y) hmul 2
    rw [mul_pow, hs, hl] at hsq
    exact henergy.trans hsq
  let f := fun t : ℝ => energy (clipped t y) - k * t ^ 2
  have hf : Continuous f := (continuous_clipped_energy y).sub (by fun_prop)
  have hfe : 0 ≤ f e := by
    dsimp [f]
    rw [hsmall]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hcard.le (sq_nonneg e))
  have hfR : f R ≤ 0 := sub_nonpos.mpr hlarge
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hR hf.continuousOn ⟨hfR, hfe⟩
  exact ⟨t, lt_of_lt_of_le he ht.1, sub_eq_zero.mp hft⟩


/-- The sparse branch needs no threshold search. -/
theorem sparse_attains_infimalCost {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (y : ι → ℝ)
    (hsparse : a * Real.sqrt ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ) ≤ b) :
    infimalCost a b y = a * l1 y := by
  classical
  let p : ι → ℝ := fun i => if y i < 0 then -a else if y i = 0 then 0 else a
  have hp_inf : ∀ i, |p i| ≤ a := by
    intro i
    simp only [p]
    split_ifs <;> simp [abs_of_nonneg ha, ha]
  have hpy : ∀ i, p i * y i = a * |y i| := by
    intro i
    dsimp [p]
    split_ifs with hneg hzero
    · rw [abs_of_neg hneg]; ring
    · simp [hzero]
    · rw [abs_of_nonneg (le_of_not_gt hneg)]
  have hp_sq : ∀ i, p i ^ 2 = if y i ≠ 0 then a ^ 2 else 0 := by
    intro i
    by_cases hz : y i = 0
    · simp [p, hz]
    · by_cases hn : y i < 0 <;> simp [p, hz, hn]
  have hp_energy : energy p =
      ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ) * a ^ 2 := by
    unfold energy
    simp_rw [hp_sq]
    rw [← Finset.sum_filter]
    simp
  have hp₂ : l2 p ≤ b := by
    unfold l2
    rw [hp_energy, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
      abs_of_nonneg ha, mul_comm]
    exact hsparse
  have hu : (∑ i, p i * y i) = a * l1 y := by
    simp_rw [hpy]
    exact (Finset.mul_sum _ _ _).symm
  have hv : (∑ i, p i * (0 : ι → ℝ) i) = b * l2 (0 : ι → ℝ) := by
    simp [l2, energy]
  have h := infimalCost_eq_of_certificate ha hb (y := y) (u := y)
    (v := 0) (p := p) (by simp) hp_inf hp₂ hu hv
  simpa [l2, energy] using h


/-- Unconditional existence of a minimizing sparse/capped decomposition for
positive weights. This is the deterministic core of the paper's mixed norm. -/
theorem exists_optimal_sparse_capped_decomposition {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (y : ι → ℝ) :
    ∃ u v : ι → ℝ,
      y = u + v ∧
      infimalCost a b y = a * l1 u + b * l2 v ∧
      ((Finset.univ.filter (fun i => u i ≠ 0)).card : ℝ) ≤ (b / a) ^ 2 ∧
      (∀ i, |v i| ≤ (a / b) * l2 v) ∧
      (∀ i, v i * u i = (a / b) * l2 v * |u i|) := by
  classical
  let m : ℝ := (Finset.univ.filter (fun i => y i ≠ 0)).card
  by_cases hs : m ≤ (b / a) ^ 2
  · have hroot : Real.sqrt m ≤ b / a := by
      apply (Real.sqrt_le_iff).2
      exact ⟨(div_pos hb ha).le, hs⟩
    have hsp : a * Real.sqrt m ≤ b := by
      have h := mul_le_mul_of_nonneg_left hroot ha.le
      calc
        _ ≤ a * (b / a) := h
        _ = b := mul_div_cancel₀ _ (ne_of_gt ha)
    refine ⟨y, 0, by simp, ?_, hs, ?_, ?_⟩
    · simpa [l2, energy] using sparse_attains_infimalCost ha.le hb.le y hsp
    · intro i; simp [l2, energy]
    · intro i; simp [l2, energy]
  · have hk : 0 < (b / a) ^ 2 := sq_pos_of_pos (div_pos hb ha)
    obtain ⟨t, ht, henergy⟩ := exists_clipping_threshold y hk (lt_of_not_ge hs)
    let v := clipped t y
    let u := remainder t y
    have hbalance : a * l2 v = b * t := by
      have he : l2 v ^ 2 = (b / a) ^ 2 * t ^ 2 := (l2_sq v).trans henergy
      have hsq : (a * l2 v) ^ 2 = (b * t) ^ 2 := by
        rw [mul_pow, he, mul_pow]
        field_simp
      nlinarith [mul_pos hb ht, mul_nonneg ha.le (l2_nonneg v)]
    have ht_eq : t = (a / b) * l2 v := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (ne_of_gt hb)).2
      simpa [mul_comm] using hbalance.symm
    have hcard : ((Finset.univ.filter (fun i => u i ≠ 0)).card : ℝ) ≤ (b / a) ^ 2 := by
      have hset : Finset.univ.filter (fun i => u i ≠ 0) =
          Finset.univ.filter (fun i => t < |y i|) := by
        ext i
        simp [u, remainder, clipped, residual_ne_zero_iff ht.le]
      rw [hset]
      have hc := clipping_energy_support y ht.le
      rw [henergy] at hc
      exact (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp hc
    refine ⟨u, v, ?_, clipping_attains_infimalCost ha hb.le ht y hbalance,
      hcard, ?_, ?_⟩
    · ext i; simp [u, v, remainder]
    · intro i
      rw [← ht_eq]
      simpa [v, clipped, clip_abs ht.le] using min_le_left t |y i|
    · intro i
      rw [← ht_eq]
      exact clip_mul_residual ht.le

end GaussianMixedNormHelpers
