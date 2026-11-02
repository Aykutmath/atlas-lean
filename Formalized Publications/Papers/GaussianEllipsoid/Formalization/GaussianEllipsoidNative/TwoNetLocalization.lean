import CoefficientNets
import NuclearNormBounds
import FiniteSupportCount
import Mathlib.MeasureTheory.Measure.Real

noncomputable section
open MeasureTheory GaussianEllipsoid
open scoped BigOperators

namespace GaussianEllipsoid.Localized

/-- The normalized bad event on one deterministic support. Coefficients may
be selected after observing the sample. -/
def supportBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (I : Finset (Fin n)) (R β B d τ : ℝ) : Set Ω :=
  {ω | ∃ u ∈ headClass I R, ∃ v ∈ tailClass Iᶜ β B d,
    spectralNuclearNorm (T ω (extend I u + extend Iᶜ v)) < τ}

/-- A pathwise nuclear continuity event. It is only intersected with bad events;
no Gaussian conditioning is performed on this event. -/
def nuclearContinuity {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r) (D : ℝ) : Set Ω :=
  {ω | ∀ x, spectralNuclearNorm (T ω x) ≤ D * ‖x‖}

/-- Replacing both coefficients by their deterministic net centers costs at
most the sum of the two continuity errors. -/
theorem two_net_pathwise {n r : ℕ} (T : Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    {D δ τ : ℝ} (hD : 0 ≤ D)
    (hT : ∀ x, spectralNuclearNorm (T x) ≤ D * ‖x‖)
    (u v u₀ v₀ : Coeff n)
    (hu : ‖u - u₀‖ < δ) (hv : ‖v - v₀‖ < δ)
    (hbad : spectralNuclearNorm (T (u+v)) < τ) :
    spectralNuclearNorm (T (u₀+v₀)) < τ + 2 * D * δ := by
  have hid : T (u₀+v₀) = T (u+v) + (T (u₀-u) + T (v₀-v)) := by
    rw [← map_add, ← map_add]
    congr 1
    abel
  have hu' : spectralNuclearNorm (T (u₀-u)) ≤ D*δ := by
    apply (hT _).trans
    apply mul_le_mul_of_nonneg_left _ hD
    simpa only [norm_sub_rev] using hu.le
  have hv' : spectralNuclearNorm (T (v₀-v)) ≤ D*δ := by
    apply (hT _).trans
    apply mul_le_mul_of_nonneg_left _ hD
    simpa only [norm_sub_rev] using hv.le
  rw [hid]
  have h₁ := spectralNuclear_add_le (T (u+v)) (T (u₀-u) + T (v₀-v))
  have h₂ := spectralNuclear_add_le (T (u₀-u)) (T (v₀-v))
  linarith

/-- Actual outer-measure finite union bound for one support and two internal
coefficient nets. The fixed-pair probability premise is discharged by the
actual Gaussian theorem in the final wrapper. -/
theorem support_two_net_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (I : Finset (Fin n)) {R β B d D δ τ p : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hpair : ∀ u ∈ headClass I R, ∀ v ∈ tailClass Iᶜ β B d,
      μ.real {ω | spectralNuclearNorm (T ω (extend I u + extend Iᶜ v)) <
        τ + 2*D*δ} ≤ p) :
    μ.real (supportBad T I R β B d τ ∩ nuclearContinuity T D) ≤
      (1 + 2*R/δ)^I.card * (1 + 2*B/δ)^(n-I.card) * p := by
  classical
  obtain ⟨C, hC, hCcard, hCnet⟩ := exists_head_net I hR hδ
  obtain ⟨V, hV, hVcard, hVnet⟩ := exists_tail_net Iᶜ (β := β) (d := d) hB hδ
  let A := fun (uv : SupportCoeff I × SupportCoeff Iᶜ) =>
    {ω | spectralNuclearNorm (T ω (extend I uv.1 + extend Iᶜ uv.2)) < τ+2*D*δ}
  have hsub : supportBad T I R β B d τ ∩ nuclearContinuity T D ⊆
      ⋃ uv ∈ C.product V, A uv := by
    rintro ω ⟨⟨u, hu, v, hv, hbad⟩, hω⟩
    obtain ⟨u₀, hu₀, hdistu⟩ := hCnet u hu
    obtain ⟨v₀, hv₀, hdistv⟩ := hVnet v hv
    refine Set.mem_iUnion.mpr ⟨(u₀,v₀), Set.mem_iUnion.mpr
      ⟨Finset.mem_product.mpr ⟨hu₀,hv₀⟩, ?_⟩⟩
    exact two_net_pathwise (T ω) hD hω _ _ _ _ hdistu hdistv hbad
  calc
    _ ≤ μ.real (⋃ uv ∈ C.product V, A uv) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ uv ∈ C.product V, μ.real (A uv) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ uv ∈ C.product V, p := by
      apply Finset.sum_le_sum
      intro uv huv
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
      exact hpair uv.1 (hC _ hu) uv.2 (hV _ hv)
    _ = (C.card:ℝ) * V.card * p := by simp [Finset.card_product, Nat.cast_mul, mul_assoc]
    _ ≤ _ := by
      have hvcard : (V.card:ℝ) ≤ (1+2*B/δ)^(n-I.card) := by
        simpa only [Finset.card_compl, Fintype.card_fin] using hVcard
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hCcard hvcard (by positivity) (by positivity)) hp

/-- The full normalized existential bad event, including data-selected supports. -/
def uniformBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (m : ℕ) (R β B d τ : ℝ) : Set Ω :=
  {ω | ∃ I : Finset (Fin n), I.card ≤ m ∧ ω ∈ supportBad T I R β B d τ}

/-- Full finite-dimensional two-net union bound. Nets are constructed before
observing the sample, and the continuity event is only used pathwise. -/
theorem uniform_two_net_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (m : ℕ) {R β B d D δ τ p : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hpair : ∀ I : Finset (Fin n), I.card ≤ m →
      ∀ u ∈ headClass I R, ∀ v ∈ tailClass Iᶜ β B d,
      μ.real {ω | spectralNuclearNorm (T ω (extend I u + extend Iᶜ v)) <
        τ + 2*D*δ} ≤ p) :
    μ.real (uniformBad T m R β B d τ ∩ nuclearContinuity T D) ≤
      p * (n+1:ℕ)^m * (1+2*R/δ)^m * (1+2*B/δ)^n := by
  classical
  let S := (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card ≤ m)
  let H := (1+2*R/δ)^m
  let V := (1+2*B/δ)^n
  have hHbase : 1 ≤ 1+2*R/δ := le_add_of_nonneg_right (by positivity)
  have hVbase : 1 ≤ 1+2*B/δ := le_add_of_nonneg_right (by positivity)
  have hsub : uniformBad T m R β B d τ ∩ nuclearContinuity T D ⊆
      ⋃ I ∈ S, (supportBad T I R β B d τ ∩ nuclearContinuity T D) := by
    rintro ω ⟨⟨I,hI,hω⟩,hc⟩
    refine Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨?_,hω,hc⟩⟩
    simp only [S, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ I,hI⟩
  have hcount : (S.card:ℝ) ≤ (n+1:ℕ)^m := by
    exact_mod_cast (show S.card ≤ (n+1)^m by
      simpa only [Finset.card_univ,Fintype.card_fin] using
        card_small_supports_le (Finset.univ : Finset (Fin n)) m)
  have hpoint (I) (hI : I ∈ S) :
      μ.real (supportBad T I R β B d τ ∩ nuclearContinuity T D) ≤ H*V*p := by
    have hIm : I.card ≤ m := (Finset.mem_filter.mp hI).2
    have hh := support_two_net_probability μ T I hR hB hD hδ hp (hpair I hIm)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hp
    exact mul_le_mul (pow_le_pow_right₀ hHbase hIm)
      (pow_le_pow_right₀ hVbase (Nat.sub_le _ _))
      (by positivity) (by dsimp [H]; positivity)
  calc
    _ ≤ μ.real (⋃ I ∈ S, (supportBad T I R β B d τ ∩ nuclearContinuity T D)) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ I ∈ S, μ.real (supportBad T I R β B d τ ∩ nuclearContinuity T D) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ I ∈ S, H*V*p := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*(H*V*p) := by simp
    _ ≤ ((n+1:ℕ)^m:ℝ)*(H*V*p) :=
      mul_le_mul_of_nonneg_right hcount (by dsimp [H,V]; positivity)
    _ = _ := by dsimp [H,V]; ring

/-- Frobenius operator control implies the pathwise nuclear continuity needed
by the two-net argument, with exactly L*d when r≤d. -/
theorem frobenius_control_nuclear {n r : ℕ} (T : Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    {L d : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d) (hrd : (r:ℝ) ≤ d)
    (hT : ∀ x, ‖T x‖ ≤ L * Real.sqrt d * ‖x‖) :
    ∀ x, spectralNuclearNorm (T x) ≤ (L*d)*‖x‖ := by
  intro x
  calc
    spectralNuclearNorm (T x) ≤ Real.sqrt (r:ℝ)*‖T x‖ :=
      spectralNuclear_le_sqrt_dim_mul_frobenius _
    _ ≤ Real.sqrt d*(L*Real.sqrt d*‖x‖) :=
      mul_le_mul (Real.sqrt_le_sqrt hrd) (hT x) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = (L*d)*‖x‖ := by
      calc
        _ = (L*(Real.sqrt d)^2)*‖x‖ := by ring
        _ = _ := by rw [Real.sq_sqrt hd]

end GaussianEllipsoid.Localized

#print axioms GaussianEllipsoid.Localized.uniform_two_net_probability
#print axioms GaussianEllipsoid.Localized.frobenius_control_nuclear
