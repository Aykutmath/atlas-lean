import UCConicPointTail
import UCUniformContinuity
import GaussianEllipsoid.Centering
import FrobeniusFactorCover

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GaussianEllipsoid.UCFixedRankGeometry
open UCContinuityGeometry UCUniformContinuity

/-- Internal low-rank unit nets retain the intrinsic O(Kd) exponent. -/
theorem exists_rank_unit_net (d K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (SymFrob d),
      (∀ A ∈ s, (matrix A).rank ≤ K ∧ ‖A‖ = 1) ∧
      (s.card:ℝ) ≤ (1+8/ε)^(2*d*K) ∧
      ∀ A : SymFrob d, (matrix A).rank ≤ K → ‖A‖=1 →
        ∃ B ∈ s, ‖A-B‖ < ε := by
  classical
  obtain ⟨s, hs, hcard, hnet⟩ := exists_square_lowRank_frobenius_cover d K
    (R := 1) (ε := ε/2) (by norm_num) (half_pos hε)
  let P : FrobeniusMatrix d d → Prop := fun c =>
    ∃ A : SymFrob d, (matrix A).rank ≤ K ∧ ‖A‖=1 ∧ ‖A.val-c‖<ε/2
  let t := s.filter P
  have ht (c : {c // c ∈ t}) : ∃ A : SymFrob d,
      (matrix A).rank ≤ K ∧ ‖A‖=1 ∧ ‖A.val-c.val‖<ε/2 :=
    (Finset.mem_filter.mp c.property).2
  choose f hf using ht
  let u := t.attach.image f
  refine ⟨u, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hA
    exact ⟨(hf c).1,(hf c).2.1⟩
  · calc
      (u.card:ℝ) ≤ (t.attach.card:ℝ) := by exact_mod_cast Finset.card_image_le
      _ = (t.card:ℝ) := by simp
      _ ≤ (s.card:ℝ) := by exact_mod_cast Finset.card_filter_le s P
      _ ≤ (1+4*(1:ℝ)/(ε/2))^(2*d*K) := hcard
      _ = _ := by congr 1; ring
  · intro A hRank hA
    obtain ⟨c,hc,hAc⟩ := hnet A.val hRank hA.le
    have hct : c ∈ t := Finset.mem_filter.mpr ⟨hc,A,hRank,hA,hAc⟩
    let ct : {c // c ∈ t} := ⟨c,hct⟩
    refine ⟨f ct, Finset.mem_image.mpr ⟨ct, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hfc := (hf ct).2.2
    calc
      ‖A-f ct‖ = ‖A.val-(f ct).val‖ := rfl
      _ ≤ ‖A.val-c‖+‖c-(f ct).val‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖A.val-c‖+‖(f ct).val-c‖ := by rw [norm_sub_rev c]
      _ < ε := by change ‖(f ct).val-c‖<ε/2 at hfc; linarith

theorem measurementQ_sub {d n : ℕ} (x : Sample d n) (A B : Square d) :
    measurementQ x (A-B) = measurementQ x A-measurementQ x B := by
  funext i
  simp only [measurementQ, quadratic_sub, Matrix.trace_sub, Pi.sub_apply]
  ring

theorem center_sub {n : ℕ} (u v : Vector n) : center (u-v) = center u-center v := by
  funext i
  simp only [center, mean, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  ring

/-- Centered empirical l1 is Lipschitz on the actual global continuity event. -/
theorem conicMargin_abs_sub_le {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A B : Square d) (hA : A.transpose=A) (hB : B.transpose=B)
    (C : ℝ) (hC : ‖empiricalOperator x‖ ≤ C) :
    |conicMargin x A-conicMargin x B| ≤ 2*C*frobeniusNorm (A-B) := by
  have hsym : (A-B).transpose=A-B := by simp [hA,hB]
  have hQ := (empirical_mean_le_operator x (A-B) hsym).trans
    (mul_le_mul_of_nonneg_right hC (frobeniusNorm_nonneg _))
  calc
    _ = (1/(n:ℝ))*|∑ i, (|center (measurementQ x A) i|-|center (measurementQ x B) i|)| := by
      rw [conicMargin, conicMargin, l1Size, l1Size, ← mul_sub,
        ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤1/(n:ℝ))]
    _ ≤ (1/(n:ℝ))*∑ i, |center (measurementQ x A) i-center (measurementQ x B) i| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => abs_abs_sub_abs_le _ _)
    _ = (1/(n:ℝ))*l1Size (center (measurementQ x (A-B))) := by
      rw [measurementQ_sub,center_sub]
      rfl
    _ ≤ (1/(n:ℝ))*(2*l1Size (measurementQ x (A-B))) :=
      mul_le_mul_of_nonneg_left (center_l1Size_le hn _) (by positivity)
    _ ≤ _ := by unfold l1Size; nlinarith

#print axioms exists_rank_unit_net
#print axioms conicMargin_abs_sub_le
end GaussianEllipsoid.UCFixedRankGeometry
