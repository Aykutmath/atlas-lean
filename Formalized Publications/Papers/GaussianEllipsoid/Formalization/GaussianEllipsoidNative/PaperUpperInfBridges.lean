import PaperDiffuseUniform
import PaperUpperAdapters
import Mathlib.Data.EReal.Basic

noncomputable section
open MeasureTheory Filter Module
open scoped Topology BigOperators
namespace GaussianEllipsoid.PaperUpperInfBridges

/-- Extended-real infimum implements the paper's convention inf empty = infinity. -/
def diffuseInf (d n : ℕ) (τ B : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : Sample d n) : EReal :=
  sInf {t : EReal | ∃ A : Square d, A.PosSemidef ∧ frobeniusNorm A=1 ∧
    matrixOpNorm A ≤ τ ∧ ∃ v : EuclideanSpace ℝ (Fin n), v ∈ L ∧
    (∑ i, |v i|) ≤ B*n ∧ t=((1/(n:ℝ))*∑ i, |measurementQ x A i-v i| : ℝ)}

theorem diffuseInf_lt_iff (d n : ℕ) (τ B c : ℝ)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : Sample d n) :
    diffuseInf d n τ B L x < (c:EReal) ↔
      x ∈ PaperDiffuseActualBound.diffuseBad d n τ B c L := by
  rw [diffuseInf, sInf_lt_iff]
  constructor
  · rintro ⟨t,⟨A,hA,hF,hOp,v,hv,hVB,rfl⟩,hlt⟩
    exact ⟨A,⟨hA,hF,hOp⟩,v,hv,hVB,EReal.coe_lt_coe_iff.mp hlt⟩
  · rintro ⟨A,⟨hA,hF,hOp⟩,v,hv,hVB,hlt⟩
    exact ⟨_,⟨A,hA,hF,hOp,v,hv,hVB,rfl⟩,EReal.coe_lt_coe_iff.mpr hlt⟩

/-- Exact paper Sections 13 and 15 diffuse theorem, including growing nuisance
rank, l1 radius, strict infimum event and uniform dimension cutoff. -/
theorem paper_diffuse_theorem (ε B C₁ : ℝ) (hε : 0 < ε) (hB : 0 < B) (hC₁ : 0 < C₁) :
    ∃ τ c c' : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 < c ∧ 0 < c' ∧
      ∀ᶠ p : ℕ in atTop, ∀ n : ℕ,
      ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
        (1/4+ε)*(p:ℝ)^2 ≤ (n:ℝ)-(finrank ℝ L:ℝ) →
        (n:ℝ) ≤ C₁*(p:ℝ)^2 →
        (gaussianSampleLaw p n).real {x | diffuseInf p n τ B L x < (c:EReal)} ≤
          Real.exp (-c'*(p:ℝ)^2) := by
  let a := 1/4+ε
  let b := max a C₁
  obtain ⟨τ,c,c',hτ,hτ1,hc,hc',h⟩ :=
    PaperDiffuseUniform.uniform_diffuse_bound a b B (by dsimp [a]; linarith)
      (le_max_left _ _) hB.le
  refine ⟨τ,c,c',hτ,hτ1,hc,hc',?_⟩
  filter_upwards [h] with p hp
  intro n L heffective hnhi
  have hbound : (n:ℝ) ≤ b*(p:ℝ)^2 := hnhi.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg (p:ℝ)))
  have hevent : {x | diffuseInf p n τ B L x < (c:EReal)} =
      PaperDiffuseActualBound.diffuseBad p n τ B c L := by
    ext x
    exact diffuseInf_lt_iff p n τ B c L x
  rw [hevent]
  exact hp n hbound L heffective

/-- All-symmetric fixed-rank margin infimum, including an empty rank-zero class. -/
def fixedRankInf (d n K : ℕ) (x : Sample d n) : EReal :=
  sInf {t : EReal | ∃ A : Square d, A.transpose=A ∧ A.rank ≤ K ∧
    frobeniusNorm A=1 ∧ t=((1/(n:ℝ))*l1Size (center (measurementQ x A)) : ℝ)}

theorem fixedRankInf_lt_iff (d n K : ℕ) (c : ℝ) (x : Sample d n) :
    fixedRankInf d n K x < (c:EReal) ↔ ∃ A : Square d,
      A.transpose=A ∧ A.rank ≤ K ∧ frobeniusNorm A=1 ∧
      (1/(n:ℝ))*l1Size (center (measurementQ x A)) < c := by
  rw [fixedRankInf, sInf_lt_iff]
  constructor
  · rintro ⟨t,⟨A,hA,hK,hF,rfl⟩,hlt⟩
    exact ⟨A,hA,hK,hF,EReal.coe_lt_coe_iff.mp hlt⟩
  · rintro ⟨A,hA,hK,hF,hlt⟩
    exact ⟨_,⟨A,hA,hK,hF,rfl⟩,EReal.coe_lt_coe_iff.mpr hlt⟩

/-- Exact paper fixed-rank exceptional event expressed using its infimum. -/
theorem paper_fixedRank_theorem :
    ∃ cStar : ℝ, 0 < cStar ∧ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ K : ℕ,
    ∃ cK : ℝ, 0 < cK ∧ ∀ᶠ d : ℕ in atTop, ∀ n : ℕ,
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ b*(d:ℝ)^2 →
      (gaussianSampleLaw d n).real {x | fixedRankInf d n K x < (cStar:EReal)} ≤
        Real.exp (-cK*(d:ℝ)^2) := by
  obtain ⟨cStar,hc,h⟩ := PaperUpperAdapters.paper_fixedRank_symmetric
  refine ⟨cStar,hc,?_⟩
  intro a b ha hab K
  obtain ⟨cK,hcK,hK⟩ := h a b ha hab K
  refine ⟨cK,hcK,?_⟩
  filter_upwards [hK] with d hd
  intro n hnlo hnhi
  have hevent : {x | fixedRankInf d n K x < (cStar:EReal)} =
      {x | ∃ A : Square d, A.transpose=A ∧ A.rank ≤ K ∧ frobeniusNorm A=1 ∧
        (1/(n:ℝ))*l1Size (center (measurementQ x A)) < cStar} := by
    ext x
    exact fixedRankInf_lt_iff d n K cStar x
  rw [hevent]
  exact hd n hnlo hnhi

/-- The paper's literal two alternative decompositions with its explicit K. -/
theorem paper_spectral_alternatives {τ δ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (d : ℕ) (A : Square d) (hA : A.PosSemidef) (hF : frobeniusNorm A=1) :
    (∃ H R : Square d, A=H+R ∧ H.PosSemidef ∧ R.PosSemidef ∧ H*R=0 ∧
      H.rank ≤ PaperUpperAdapters.paperPeelingBudget τ δ ∧ frobeniusNorm R ≤ δ) ∨
    (∃ H D : Square d, ∃ ρ : ℝ, A=H+ρ • D ∧ H.PosSemidef ∧ D.PosSemidef ∧ H*D=0 ∧
      H.rank ≤ PaperUpperAdapters.paperPeelingBudget τ δ ∧ δ < ρ ∧
      frobeniusNorm D=1 ∧ matrixOpNorm D ≤ τ) := by
  obtain ⟨H,R,hH,hR,hdec,hHR,hK,hstop⟩ :=
    PaperUpperAdapters.paper_spectral_peeling hτ hτ1 hδ hδ1 d A hA hF
  rcases hstop with hsmall | ⟨ρ,D,hρ,hRD,hD,hHD,hDF,hDOp⟩
  · exact Or.inl ⟨H,R,hdec,hH,hR,hHR,hK,hsmall⟩
  · exact Or.inr ⟨H,D,ρ,by rw [hRD] at hdec; exact hdec,hH,hD,hHD,hK,hρ,hDF,hDOp⟩

#print axioms paper_spectral_alternatives
#print axioms paper_fixedRank_theorem
#print axioms paper_diffuse_theorem
#print axioms fixedRankInf_lt_iff
end GaussianEllipsoid.PaperUpperInfBridges
