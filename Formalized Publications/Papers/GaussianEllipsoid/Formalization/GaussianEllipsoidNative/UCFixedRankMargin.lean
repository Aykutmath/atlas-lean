import UCFixedRankGeometry

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCFixedRankMargin
open UCConicPointTail UCFixedRankGeometry UCContinuityGeometry UCUniformContinuity

def margin : ℝ := pointMargin/2
def rate : ℝ := pointRate/4

theorem margin_pos : 0 < margin := half_pos pointMargin_pos
theorem rate_pos : 0 < rate := by unfold rate; positivity [pointRate_pos]

def mesh (a : ℝ) : ℝ := pointMargin/(4*continuityConstant a)
def base (a : ℝ) : ℝ := 1+8/mesh a

def badEvent (d n K : ℕ) : Set (Sample d n) :=
  {x | ∃ A : Square d, A.transpose=A ∧ A.rank≤K ∧ frobeniusNorm A=1 ∧
    conicMargin x A < margin}

theorem mesh_pos {a : ℝ} (ha : 0<a) : 0 < mesh a := by
  unfold mesh
  positivity [pointMargin_pos,continuityConstant_pos ha]

theorem base_pos {a : ℝ} (ha : 0<a) : 0 < base a := by
  unfold base
  positivity [mesh_pos ha]

/-- Uniform rank-K margin with its explicit intrinsic-dimensional entropy
cost. The margin itself is universal; rank appears only in net cardinality. -/
theorem fixedRank_entropy_tail {a : ℝ} (ha : 0<a) {d n : ℕ}
    (hd : 0<d) (hn : 2≤n) (haspect : a*(d:ℝ)^2≤n) (K : ℕ) :
    (gaussianSampleLaw d n).real (badEvent d n K) ≤
      Real.exp (-(n:ℝ)) + (base a)^(2*d*K)*Real.exp (-pointRate*(n:ℝ)) := by
  obtain ⟨s,hs,hcard,hnet⟩ := exists_rank_unit_net d K (mesh_pos ha)
  let E : Set (Sample d n) := {x | continuityConstant a < ‖empiricalOperator x‖}
  let B : SymFrob d → Set (Sample d n) := fun A => {x | conicMargin x (matrix A)<pointMargin}
  have hsub : badEvent d n K ⊆ E ∪ ⋃ A ∈ s, B A := by
    rintro x ⟨A,hA,hRank,hF,hbad⟩
    by_cases hC : continuityConstant a < ‖empiricalOperator x‖
    · exact Or.inl hC
    · have hC' : ‖empiricalOperator x‖ ≤ continuityConstant a := le_of_not_gt hC
      obtain ⟨D,hD,hAD⟩ := hnet (ofMatrix A hA)
        (by rw [matrix_ofMatrix]; exact hRank) ((norm_ofMatrix A hA).trans hF)
      have herr := conicMargin_abs_sub_le (show 0<n by omega) x A (matrix D) hA
        (matrix_transpose D) (continuityConstant a) hC'
      have hFD : frobeniusNorm (A-matrix D)<mesh a := by
        have he : matrix (ofMatrix A hA-D) = A-matrix D := by
          calc
            _ = matrix (ofMatrix A hA)-matrix D := rfl
            _ = _ := by rw [matrix_ofMatrix]
        rw [← he,matrix_frobeniusNorm]
        exact hAD
      have herror : 2*continuityConstant a*frobeniusNorm (A-matrix D)<pointMargin/2 := by
        have ht := mul_lt_mul_of_pos_left hFD
          (by positivity [continuityConstant_pos ha] : 0<2*continuityConstant a)
        apply ht.trans_eq
        unfold mesh
        field_simp [ne_of_gt (continuityConstant_pos ha)]
        <;> ring
      have hDm : conicMargin x (matrix D)<pointMargin := by
        have hh := (abs_le.mp herr).1
        unfold margin at hbad
        linarith
      exact Or.inr (Set.mem_iUnion_of_mem D (Set.mem_iUnion_of_mem hD hDm))
  have hE := empiricalOperator_tail ha hd (show 0<n by omega) haspect
  have hB (D : SymFrob d) (hD : D ∈ s) :
      (gaussianSampleLaw d n).real (B D) ≤ Real.exp (-pointRate*(n:ℝ)) :=
    conicMargin_lower_tail hd hn (matrix D) (matrix_transpose D)
      (by rw [matrix_frobeniusNorm,(hs D hD).2])
  calc
    _ ≤ (gaussianSampleLaw d n).real (E ∪ ⋃ A ∈ s, B A) := measureReal_mono hsub
    _ ≤ (gaussianSampleLaw d n).real E + (gaussianSampleLaw d n).real (⋃ A ∈ s, B A) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(n:ℝ)) + ∑ A ∈ s, (gaussianSampleLaw d n).real (B A) :=
      add_le_add hE (measureReal_biUnion_finset_le s B)
    _ ≤ Real.exp (-(n:ℝ)) + ∑ _A ∈ s, Real.exp (-pointRate*(n:ℝ)) :=
      add_le_add le_rfl (Finset.sum_le_sum fun A hA => hB A hA)
    _ = Real.exp (-(n:ℝ)) + (s.card:ℝ)*Real.exp (-pointRate*(n:ℝ)) := by simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))

/-- Exponential envelope for the intrinsic rank-K covering number. -/
theorem entropy_le_exp {a : ℝ} (ha : 0<a) (d K : ℕ) :
    (base a)^(2*d*K) ≤ Real.exp (2*(d:ℝ)*K*base a) := by
  have hb : base a ≤ Real.exp (base a) := by linarith [Real.add_one_le_exp (base a)]
  calc
    _ ≤ (Real.exp (base a))^(2*d*K) := pow_le_pow_left₀ (base_pos ha).le hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- A fully explicit finite-dimensional sufficient threshold. -/
theorem fixedRank_tail_of_large_dimension {a : ℝ} (ha : 0<a) (K d n : ℕ)
    (hd : 1≤d) (hentropy : 4*(K:ℝ)*base a ≤ pointRate*a*d)
    (hsize : 4 ≤ pointRate*a*(d:ℝ)^2) (haspect : a*(d:ℝ)^2≤n) :
    (gaussianSampleLaw d n).real (badEvent d n K) ≤ Real.exp (-rate*(n:ℝ)) := by
  have hrate : 0 < pointRate := pointRate_pos
  have hrate2 : pointRate ≤ 1 := by norm_num [pointRate]
  have hdR : (0:ℝ)≤d := Nat.cast_nonneg _
  have hnR : (0:ℝ)≤n := Nat.cast_nonneg _
  have hN : 4 ≤ pointRate*(n:ℝ) := hsize.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left haspect hrate.le)
  have hn : 2≤n := by
    have hh := mul_le_mul_of_nonneg_right hrate2 hnR
    norm_num at hh
    exact_mod_cast (show (2:ℝ)≤n by linarith)
  have hEnt : 2*(d:ℝ)*K*base a ≤ pointRate*(n:ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_right hentropy hdR
    have h' := mul_le_mul_of_nonneg_left haspect hrate.le
    nlinarith
  have h0 := fixedRank_entropy_tail ha (show 0<d by omega) hn haspect K
  have h1 : (base a)^(2*d*K)*Real.exp (-pointRate*(n:ℝ)) ≤
      Real.exp (-pointRate*(n:ℝ)/2) := by
    calc
      _ ≤ Real.exp (2*(d:ℝ)*K*base a)*Real.exp (-pointRate*(n:ℝ)) :=
        mul_le_mul_of_nonneg_right (entropy_le_exp ha d K) (Real.exp_nonneg _)
      _ = Real.exp (2*(d:ℝ)*K*base a-pointRate*(n:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(n:ℝ)) ≤ Real.exp (-pointRate*(n:ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h3 : 2 ≤ Real.exp (pointRate*(n:ℝ)/4) := by
    linarith [Real.add_one_le_exp (pointRate*(n:ℝ)/4)]
  calc
    _ ≤ 2*Real.exp (-pointRate*(n:ℝ)/2) := by linarith
    _ ≤ Real.exp (pointRate*(n:ℝ)/4)*Real.exp (-pointRate*(n:ℝ)/2) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; unfold rate; congr 1; ring

/-- Universal fixed-rank conic margin. For every fixed rank bound and every
positive sample aspect floor, the true Gaussian event has an exponential
in n tail in all sufficiently large dimensions. -/
theorem fixedRank_tail_eventually {a : ℝ} (ha : 0<a) (K : ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2≤n →
      (gaussianSampleLaw d n).real (badEvent d n K) ≤ Real.exp (-rate*(n:ℝ)) := by
  have hr : 0<pointRate*a := mul_pos pointRate_pos ha
  obtain ⟨N,hN⟩ := exists_nat_ge (max 1 (max (4*(K:ℝ)*base a/(pointRate*a)) (4/(pointRate*a))))
  filter_upwards [eventually_ge_atTop N] with d hd
  have hdR : (N:ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1:ℝ) ≤ d := (le_max_left _ _).trans (hN.trans hdR)
  have h2 : 4*(K:ℝ)*base a/(pointRate*a) ≤ d :=
    (le_max_of_le_right (le_max_left _ _)).trans (hN.trans hdR)
  have h3 : 4/(pointRate*a) ≤ d :=
    (le_max_of_le_right (le_max_right _ _)).trans (hN.trans hdR)
  intro n haspect
  apply fixedRank_tail_of_large_dimension ha K d n (by exact_mod_cast h1)
  · have hh := (div_le_iff₀ hr).mp h2
    nlinarith
  · have hh := (div_le_iff₀ hr).mp h3
    have hsq : (d:ℝ)≤(d:ℝ)^2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hsq hr.le
    nlinarith
  · exact haspect

/-- PSD specialization in the exact project's matrix, sample, and l1 types. -/
theorem fixedRank_psd_tail_eventually {a : ℝ} (ha : 0<a) (K : ℕ) :
    ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, a*(d:ℝ)^2≤n →
      (gaussianSampleLaw d n).real {x | ∃ A : Square d, A.PosSemidef ∧ A.rank≤K ∧
        frobeniusNorm A=1 ∧ (1/(n:ℝ))*l1Size (center (measurementQ x A))<margin} ≤
          Real.exp (-rate*(n:ℝ)) := by
  filter_upwards [fixedRank_tail_eventually ha K] with d hd
  intro n hn
  apply le_trans (measureReal_mono (μ := gaussianSampleLaw d n) ?_) (hd n hn)
  rintro x ⟨A,hA,hRank,hF,hbad⟩
  refine ⟨A,?_,hRank,hF,hbad⟩
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian

#print axioms fixedRank_psd_tail_eventually
end GaussianEllipsoid.UCFixedRankMargin
