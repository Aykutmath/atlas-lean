import PaperFullHalfRetained
import PaperAtomEvent
import PaperOriginalLogDepth

noncomputable section
open Finset MeasureTheory Filter GaussianMixedNormHelpers GaussianEllipsoid GaussianTensorMoments
open GaussianEllipsoid.SparseSupport
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

theorem actual_fixed_failure_subset_product_atom {n d h : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (groups : List (List ℕ))
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K))
    (T : ℕ) (hscale : (8*(1/2:ℝ)^T)*K^2 ≤ (1/2:ℝ)^37)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T) :
    {X : Fin n → Euclid h × Euclid h |
      scaledBilinearNuclear d u X < multiscaleFixedConstant K * Real.sqrt d} ∩ paperPairAtomEvent 1 d n h ⊆
    {X | scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
      ((1/2:ℝ)^24/(Real.sqrt K*J))*Real.sqrt d*
        coefficientMass (retainedGroupVector u amp groups T)} := by
  let V := retainedGroupVector u amp groups T
  let M := coefficientMass V
  let ε := 8*(1/2:ℝ)^T
  let c := (1/2:ℝ)^24/(Real.sqrt K*J)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hc : 0 < c := by dsimp [c]; positivity
  have hconstants := common_retained_tail_constants_flexible K J hK hJ hJup T hscale
  have hfinal : multiscaleFixedConstant K ≤ c*(1-ε)-2*ε := by
    unfold multiscaleFixedConstant
    rw [max_eq_left hK]
    exact hconstants.2.2.2.2
  have hM : 1-ε ≤ M := retained_mass_ge_one_sub u amp groups T ε hu herr
  rintro X ⟨hbad, hatom⟩
  have herror : scaledBilinearNuclear d (u-V) X ≤ Real.sqrt d*ε :=
    (show scaledBilinearNuclear d (u-V) X ≤ Real.sqrt d*coefficientMass (u-V) by
      simpa only [one_mul,coefficientMass] using paperPairAtomEvent_all_coefficients hatom (u-V)).trans
      (mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _))
  have htri := scaledBilinearNuclear_sub_le (d:=d) u V X
  have hscale : multiscaleFixedConstant K*Real.sqrt d + Real.sqrt d*ε ≤ c*Real.sqrt d*M := by
    have h1 := mul_le_mul_of_nonneg_right hfinal (Real.sqrt_nonneg (d:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hM hc.le
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (d:ℝ))
    nlinarith [mul_nonneg hε (Real.sqrt_nonneg (d:ℝ))]
  exact lt_of_le_of_lt htri ((add_lt_add_of_lt_of_le hbad herror).trans_le hscale)


/-- Literal product E_atom, rather than the stronger individual-norm event. -/
theorem paper_literal_atom_fixed_vector_logarithmic_tail (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,(n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ u : Fin n → ℝ,coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
          paperSparseSingularGood d n (d/2) ∩ paperPairAtomEvent 1 d n (d/2)) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_source_retained_logarithmic_tail A (max K 1) hA (le_max_right K 1)
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn u hu hs
  have hs' := hs.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (Nat.cast_nonneg d))
  obtain ⟨N,groups,hN,hcover,hempty,hflat,hreg,hchain,herr,hprob⟩ := hd₀ d hd n hn u hu hs'
  let J : ℝ := 17*(1+Real.log (max K 1))
  have hJ : 0 < J := by dsimp [J]; linarith [Real.log_nonneg (le_max_right K 1)]
  have hsub := actual_fixed_failure_subset_product_atom (d:=d) (h:=d/2) u hu ‖u‖ groups (max K 1) J
    (le_max_right K 1) hJ (by rfl) (depth (max K 1))
    (retention_error_scaled_logarithmic (max K 1) (le_max_right K 1)) herr
  have hconst : multiscaleFixedConstant (max K 1)=multiscaleFixedConstant K := by
    unfold multiscaleFixedConstant
    rw [max_eq_left (le_max_right K 1)]
  rw [hconst] at hsub
  apply (measureReal_mono (show
    ({X | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
      paperSparseSingularGood d n (d/2) ∩ paperPairAtomEvent 1 d n (d/2)) ⊆
    ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups (depth (max K 1))) X <
      (1/2:ℝ)^24/(Real.sqrt (max K 1)*J)*Real.sqrt d*
        coefficientMass (retainedGroupVector u ‖u‖ groups (depth (max K 1)))} ∩
      paperSparseSingularGood d n (d/2)) from ?_)).trans hprob
  rintro X ⟨⟨hbad,hsp⟩,hatom⟩
  exact ⟨hsub ⟨hbad,hatom⟩,hsp⟩

theorem paper_original_product_atom_event_probability (d n : ℕ) (u : Fin n → ℝ) (c : ℝ) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) < c ∧
        paperOriginalRows d n X∈paperSparseSingularGood d n (d/2) ∧ X∈paperAtomEvent 1 d n} =
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩
        paperPairAtomEvent 1 d n (d/2)) := by
  have hE : MeasurableSet ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩
      paperPairAtomEvent 1 d n (d/2)) :=
    ((isOpen_lt (continuous_scaledBilinearNuclear d u) continuous_const).measurableSet.inter
      (paperSparseSingularGood_isClosed d n (d/2)).measurableSet).inter (paperPairAtomEvent_measurable 1 d n (d/2))
  have he : {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) < c ∧
      paperOriginalRows d n X∈paperSparseSingularGood d n (d/2) ∧ X∈paperAtomEvent 1 d n} =
      paperOriginalRows d n ⁻¹' ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩
        paperPairAtomEvent 1 d n (d/2)) := by
    ext X
    simp only [Set.mem_setOf_eq,Set.mem_preimage,Set.mem_inter_iff,paper_original_nuclear_eq,and_assoc]
    rfl
  rw [he]
  exact (paperOriginalRows_preserving d n).measureReal_preimage hE.nullMeasurableSet

theorem paper_original_literal_atom_fixed_vector_tail (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,(n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ u : Fin n → ℝ,coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
        {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) <
          multiscaleFixedConstant K*Real.sqrt d ∧
          paperOriginalRows d n X∈paperSparseSingularGood d n (d/2) ∧ X∈paperAtomEvent 1 d n} ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_literal_atom_fixed_vector_logarithmic_tail A K hA
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn u hu hs
  rw [paper_original_product_atom_event_probability]
  exact hd₀ d hd n hn u hu hs

end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.actual_fixed_failure_subset_product_atom
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_literal_atom_fixed_vector_logarithmic_tail
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_original_literal_atom_fixed_vector_tail

namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth
/-- Good event for the deterministic coefficient net used in the source union. -/
def paperCoefficientNetGood {n : ℕ} (d h : ℕ) (S : Finset (Fin n → ℝ)) (c : ℝ) :
    Set (Fin n → Euclid h × Euclid h) :=
  {X | ∀ u∈S,c*Real.sqrt d ≤ scaledBilinearNuclear d u X}

/-- Exact guarded finite-net union on the source product atom event. -/
theorem paper_product_atom_net_union (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,(n:ℝ) ≤ A*(d:ℝ)^2 →
      ∀ S : Finset (Fin n → ℝ),
      (∀ u∈S,coefficientMass u=1 ∧ ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d) →
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ((paperCoefficientNetGood d (d/2) S (multiscaleFixedConstant K))ᶜ ∩
          paperSparseSingularGood d n (d/2) ∩ paperPairAtomEvent 1 d n (d/2)) ≤
        (S.card:ℝ)*(Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d)) := by
  classical
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_literal_atom_fixed_vector_logarithmic_tail A K hA
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn S hS
  let E := fun u : Fin n → ℝ =>
    {X : Fin n → Euclid (d/2) × Euclid (d/2) | scaledBilinearNuclear d u X < multiscaleFixedConstant K*Real.sqrt d} ∩
      paperSparseSingularGood d n (d/2) ∩ paperPairAtomEvent 1 d n (d/2)
  have hsub : (paperCoefficientNetGood d (d/2) S (multiscaleFixedConstant K))ᶜ ∩
      paperSparseSingularGood d n (d/2) ∩ paperPairAtomEvent 1 d n (d/2) ⊆ ⋃ u∈S,E u := by
    intro X hX
    have hb : ¬∀ u∈S,multiscaleFixedConstant K*Real.sqrt d ≤ scaledBilinearNuclear d u X := hX.1.1
    push_neg at hb
    obtain ⟨u,hu,hbad⟩ := hb
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,⟨⟨hbad,hX.1.2⟩,hX.2⟩⟩⟩
  calc
    _ ≤ _ := measureReal_mono (μ:=gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)) hsub (measure_ne_top _ _)
    _ ≤ ∑ u∈S,(gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real (E u) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _u∈S,Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) :=
      sum_le_sum (fun u hu => hd₀ d hd n hn u (hS u hu).1 (hS u hu).2)
    _ = _ := by simp

/-- Entropy conversion to the literal source exponential display. -/
theorem paper_net_entropy_exponent (d c C N : ℝ) (hd : 1 ≤ d) (hlog : 1 ≤ Real.log d)
    (hN : 0 ≤ N) (hcard : N ≤ Real.exp (C*d*Real.log d)) :
    N*(Real.log d*Real.exp (-c*d^2/Real.log d)) ≤
      Real.exp (-c*d^2/Real.log d+(C+1)*d*Real.log d) := by
  have hd0 : 0 < d := by linarith
  have hlog0 : 0 ≤ Real.log d := by linarith
  have hle : Real.log d ≤ Real.exp (d*Real.log d) := by
    have hl := Real.log_le_sub_one_of_pos hd0
    have he := Real.add_one_le_exp (d*Real.log d)
    nlinarith [mul_le_mul_of_nonneg_left hlog hd0.le]
  calc
    _ ≤ Real.exp (C*d*Real.log d)*(Real.exp (d*Real.log d)*Real.exp (-c*d^2/Real.log d)) :=
      mul_le_mul hcard (mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

/-- Exact product-event Lipschitz loss between an arbitrary vector and its net
point. No individual left/right norm bound is assumed. -/
theorem paper_product_atom_net_extension {n d h : ℕ}
    (u u₀ : Fin n → ℝ) (CA c delta : ℝ) (hCA : 0 ≤ CA)
    (X : Fin n → Euclid h × Euclid h) (hatom : X∈paperPairAtomEvent CA d n h)
    (hclose : coefficientMass (u-u₀) ≤ delta)
    (hnet : c*Real.sqrt d ≤ scaledBilinearNuclear d u₀ X) (hdelta : CA*delta ≤ c/4) :
    (3/4:ℝ)*c*Real.sqrt d ≤ scaledBilinearNuclear d u X := by
  have herr := (paperPairAtomEvent_all_coefficients hatom (u-u₀)).trans
    (mul_le_mul_of_nonneg_left hclose (show 0 ≤ CA*Real.sqrt d by positivity))
  have htri := scaledBilinearNuclear_sub_le (d:=d) u u₀ X
  have hdelt := mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg (d:ℝ))
  nlinarith

/-- Pointwise whole-class extension from the source deterministic net on the
literal product atom event. The quarter-loss is explicit. -/
theorem paper_product_atom_uniform_extension {n d h : ℕ}
    (S : Finset (Fin n → ℝ)) (CA c delta K : ℝ) (hCA : 0 ≤ CA)
    (hcover : ∀ u : Fin n → ℝ,coefficientMass u=1 →
      ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d → ∃ u₀∈S,coefficientMass (u-u₀) ≤ delta)
    (hdelta : CA*delta ≤ c/4)
    (X : Fin n → Euclid h × Euclid h) (hnet : X∈paperCoefficientNetGood d h S c)
    (hatom : X∈paperPairAtomEvent CA d n h) :
    ∀ u : Fin n → ℝ,coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      (3/4:ℝ)*c*Real.sqrt d ≤ scaledBilinearNuclear d u X := by
  intro u hu hs
  obtain ⟨u₀,hu₀,hclose⟩ := hcover u hu hs
  exact paper_product_atom_net_extension u u₀ CA c delta hCA X hatom hclose (hnet u₀ hu₀) hdelta
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_product_atom_net_union
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_net_entropy_exponent
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_product_atom_uniform_extension

namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth
/-- The source's literal delta=c/(4 C_A) choice. -/
theorem paper_product_atom_uniform_extension_radius {n d h : ℕ}
    (S : Finset (Fin n → ℝ)) (CA c K : ℝ) (hCA : 0 < CA)
    (hcover : ∀ u : Fin n → ℝ,coefficientMass u=1 →
      ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
        ∃ u₀∈S,coefficientMass (u-u₀) ≤ c/(4*CA))
    (X : Fin n → Euclid h × Euclid h) (hnet : X∈paperCoefficientNetGood d h S c)
    (hatom : X∈paperPairAtomEvent CA d n h) :
    ∀ u : Fin n → ℝ,coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      (3/4:ℝ)*c*Real.sqrt d ≤ scaledBilinearNuclear d u X := by
  apply paper_product_atom_uniform_extension S CA c (c/(4*CA)) K hCA.le hcover ?_ X hnet hatom
  have he : CA*(c/(4*CA))=c/4 := by field_simp [hCA.ne'] <;> ring
  exact he.le
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_product_atom_uniform_extension_radius

namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth
/-- The source deterministic-net good event is Borel. -/
theorem paperCoefficientNetGood_measurable {n : ℕ} (d h : ℕ)
    (S : Finset (Fin n → ℝ)) (c : ℝ) :
    MeasurableSet (paperCoefficientNetGood d h S c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [paperCoefficientNetGood]
  | @insert u S hu ih =>
    have he : paperCoefficientNetGood d h (insert u S) c =
        {X | c*Real.sqrt d ≤ scaledBilinearNuclear d u X} ∩
          paperCoefficientNetGood d h S c := by
      ext X
      simp [paperCoefficientNetGood]
    rw [he]
    exact (isClosed_le continuous_const (continuous_scaledBilinearNuclear d u)).measurableSet.inter ih

/-- The manuscript's final one-half constant follows from the explicit
quarter-loss extension on exactly the same product event. -/
theorem paper_product_atom_uniform_half_radius {n d h : ℕ}
    (S : Finset (Fin n → ℝ)) (CA c K : ℝ) (hCA : 0 < CA) (hc : 0 ≤ c)
    (hcover : ∀ u : Fin n → ℝ,coefficientMass u=1 →
      ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
        ∃ u₀∈S,coefficientMass (u-u₀) ≤ c/(4*CA))
    (X : Fin n → Euclid h × Euclid h) (hnet : X∈paperCoefficientNetGood d h S c)
    (hatom : X∈paperPairAtomEvent CA d n h) :
    ∀ u : Fin n → ℝ,coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      (c/2)*Real.sqrt d ≤ scaledBilinearNuclear d u X := by
  intro u hu hs
  have hh := paper_product_atom_uniform_extension_radius S CA c K hCA hcover X hnet hatom u hu hs
  nlinarith [mul_nonneg hc (Real.sqrt_nonneg (d:ℝ))]
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paperCoefficientNetGood_measurable
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_product_atom_uniform_half_radius
