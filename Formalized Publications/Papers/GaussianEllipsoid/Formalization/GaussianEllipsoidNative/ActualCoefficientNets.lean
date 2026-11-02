import VolumetricNets
import GaussianSparseSupport
import MultiscaleNet

noncomputable section
open scoped BigOperators
open GaussianEllipsoid GaussianEllipsoid.SparseSupport
namespace GaussianEllipsoidCandidate

abbrev SupportL1 {n : ℕ} (I : Finset (Fin n)) := PiLp 1 (fun _ : I => ℝ)

def extendSupport {n : ℕ} (I : Finset (Fin n)) (x : SupportL1 I) : Fin n → ℝ :=
  fun i => if hi : i ∈ I then x ⟨i, hi⟩ else 0

@[simp] theorem extendSupport_apply_mem {n : ℕ} (I : Finset (Fin n))
    (x : SupportL1 I) (i : Fin n) (hi : i ∈ I) : extendSupport I x i = x ⟨i, hi⟩ := by
  simp [extendSupport, hi]

@[simp] theorem extendSupport_apply_not_mem {n : ℕ} (I : Finset (Fin n))
    (x : SupportL1 I) (i : Fin n) (hi : i ∉ I) : extendSupport I x i = 0 := by
  simp [extendSupport, hi]

theorem coefficientMass_extendSupport {n : ℕ} (I : Finset (Fin n)) (x : SupportL1 I) :
    coefficientMass (extendSupport I x) = ‖x‖ := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_self (one_ne_zero : (1:ℝ) ≠ 0), Real.norm_eq_abs]
  unfold coefficientMass
  calc
    (∑ i, |extendSupport I x i|) = ∑ i ∈ I, |extendSupport I x i| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      simp [extendSupport, hi]
    _ = ∑ i : I, |extendSupport I x i| := Finset.sum_subtype I (fun _ => Iff.rfl) _
    _ = _ := by apply Finset.sum_congr rfl; intro i _; simp

 theorem coefficientMass_extendSupport_sub {n : ℕ} (I : Finset (Fin n)) (x y : SupportL1 I) :
    coefficientMass (extendSupport I x - extendSupport I y) = ‖x-y‖ := by
  have he : extendSupport I x - extendSupport I y = extendSupport I (x-y) := by
    funext i
    by_cases hi : i ∈ I <;> simp [extendSupport, hi, Pi.sub_apply]
  rw [he, coefficientMass_extendSupport]

theorem supportL1_finrank {n : ℕ} (I : Finset (Fin n)) :
    Module.finrank ℝ (SupportL1 I) = I.card := by
  rw [(WithLp.linearEquiv 1 ℝ (I → ℝ)).finrank_eq]
  simp

/-- An actual internal l1-sphere net on one prescribed support. -/
theorem exists_supported_coefficient_net {n : ℕ} (I : Finset (Fin n))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : Finset (Fin n → ℝ),
      (∀ v ∈ N, coefficientMass v = 1 ∧ ∀ i, i ∉ I → v i = 0) ∧
      (N.card : ℝ) ≤ (1 + 2/δ)^I.card ∧
      ∀ u : Fin n → ℝ, coefficientMass u = 1 → (∀ i, i ∉ I → u i = 0) →
        ∃ v ∈ N, coefficientMass (u-v) < δ := by
  classical
  obtain ⟨s, hs, hc, hn, _⟩ := GaussianEllipsoid.exists_internal_net
    {x : SupportL1 I | ‖x‖ = 1} (R := 1) (ε := δ) (by norm_num) hδ
    (fun _ hx => le_of_eq hx)
  refine ⟨s.image (extendSupport I), ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(coefficientMass_extendSupport I x).trans (hs x hx),
      fun i hi => extendSupport_apply_not_mem I x i hi⟩
  · have him : ((s.image (extendSupport I)).card : ℝ) ≤ s.card := by
      exact_mod_cast Finset.card_image_le (s := s) (f := extendSupport I)
    exact him.trans (by simpa [supportL1_finrank] using hc)
  · intro u hu huI
    let x : SupportL1 I := (WithLp.equiv 1 (I → ℝ)).symm (fun i => u i)
    have he : extendSupport I x = u := by
      funext i
      by_cases hi : i ∈ I
      · simp [extendSupport, hi, x]
      · simp [extendSupport, hi, huI i hi]
    have hx : ‖x‖ = 1 := by rw [← coefficientMass_extendSupport, he, hu]
    obtain ⟨y, hy, hxy⟩ := hn x hx
    refine ⟨extendSupport I y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [← he, coefficientMass_extendSupport_sub]
    simpa only [dist_eq_norm] using hxy

/-- A genuine finite deterministic l1 net simultaneously covering every support
of size at most m; centers themselves have unit mass and such a support. -/
theorem exists_sparse_coefficient_net (n m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : Finset (Fin n → ℝ),
      (∀ v ∈ N, coefficientMass v = 1 ∧
        (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ m) ∧
      (N.card : ℝ) ≤ ((1+2/δ)*(n+1))^m ∧
      ∀ u : Fin n → ℝ, coefficientMass u = 1 →
        (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ m →
        ∃ v ∈ N, coefficientMass (u-v) < δ := by
  classical
  choose net hnet hcard hcover using fun I : Finset (Fin n) =>
    exists_supported_coefficient_net I δ hδ
  let N := (smallSupports n m).biUnion net
  refine ⟨N, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hv
    refine ⟨(hnet I v hvI).1, ?_⟩
    apply (Finset.card_le_card (show Finset.univ.filter (fun i => v i ≠ 0) ⊆ I from ?_)).trans
      ((mem_smallSupports I).mp hI)
    intro i hi
    by_contra hiI
    exact (Finset.mem_filter.mp hi).2 ((hnet I v hvI).2 i hiI)
  · have hb : 1 ≤ 1+2/δ := by linarith [div_pos (by norm_num : (0:ℝ)<2) hδ]
    calc
      (N.card : ℝ) ≤ ∑ I ∈ smallSupports n m, ((net I).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := smallSupports n m) (t := net))
      _ ≤ ∑ _I ∈ smallSupports n m, (1+2/δ)^m := by
        apply Finset.sum_le_sum
        intro I hI
        exact (hcard I).trans (pow_le_pow_right₀ hb ((mem_smallSupports I).mp hI))
      _ = ((smallSupports n m).card : ℝ) * (1+2/δ)^m := by simp
      _ ≤ (n+1 : ℝ)^m * (1+2/δ)^m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast smallSupports_card_le n m
      _ = _ := by rw [← mul_pow]; congr 1; ring
  · intro u hu hs
    let I := Finset.univ.filter (fun i => u i ≠ 0)
    have hI : I ∈ smallSupports n m := (mem_smallSupports I).mpr hs
    obtain ⟨v, hv, hd⟩ := hcover I u hu (by
      intro i hi
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi)
    exact ⟨v, Finset.mem_biUnion.mpr ⟨I, hI, hv⟩, hd⟩

end GaussianEllipsoidCandidate
