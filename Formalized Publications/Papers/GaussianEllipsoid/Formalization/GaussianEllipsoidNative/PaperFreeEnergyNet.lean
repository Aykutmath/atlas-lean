import PaperExactEntropy
import GaussianEllipsoid.FreeEnergy

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid.PaperExactEntropy
open FiniteFreeEnergy

/-- Instantiate the actual joint matrix/nuisance nets and their proved entropy
budget in the manuscript's finite free-energy approximation. The energy may be
any real function, hence includes the displayed sum of losses on each dataset.
Nonemptiness is explicit because the displayed normalized finite partition
function and finite minimum require it. -/
theorem paper_net_freeEnergy_approximation (d n : ℕ) (hn : 0 < n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (a τ r B s β θ : ℝ) (ha : 0 < a) (hr : 0 < r) (hr1 : r ≤ 1)
    (hB : 0 ≤ B) (hs : 0 < s) (hsB : s ≤ B)
    (haspect : a*(d:ℝ)^2 ≤ n) (hβ : 0 < β) (hθ : 0 < θ)
    (hchoice : 16*((1/a)*Real.log (3/r)+Real.log (1+2*B/s))/θ ≤ β)
    (hD : (UCDiffuseNets.diffuseClass d τ).Nonempty) :
    ∃ ND : Finset (UCContinuityGeometry.SymFrob d),
    ∃ NL : Finset (EuclideanSpace ℝ (Fin n)),
      ND.Nonempty ∧ NL.Nonempty ∧
      (∀ A ∈ ND, A ∈ UCDiffuseNets.diffuseClass d τ) ∧
      (∀ A ∈ UCDiffuseNets.diffuseClass d τ, ∃ D ∈ ND, ‖A-D‖ < r) ∧
      (∀ v ∈ NL, v ∈ L ∧ (∑ i, |v i|) ≤ B*n) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), v ∈ L → (∑ i, |v i|) ≤ B*n →
        ∃ w ∈ NL, (∑ i, |v i-w i|) < s*n) ∧
      ∃ hNE : Nonempty (↥ND × ↥NL), letI := hNE;
      ∀ H : (↥ND × ↥NL) → ℝ,
        candidateMin H / n ≤ freeEnergy β n H ∧
        freeEnergy β n H ≤ candidateMin H / n + θ/16 := by
  classical
  obtain ⟨ND,NL,hND,hDcover,hsep,hNL,hLcover,hentropy⟩ :=
    paper_joint_nets d n hn L a τ r B s ha hr hr1 hB hs hsB haspect
  obtain ⟨A,hA⟩ := hD
  obtain ⟨D,hD,_⟩ := hDcover A hA
  have hzero : (∑ i : Fin n, |(0 : EuclideanSpace ℝ (Fin n)) i|) ≤ B*n := by simp; positivity
  obtain ⟨w,hw,_⟩ := hLcover 0 L.zero_mem hzero
  have hNDne : ND.Nonempty := ⟨D,hD⟩
  have hNLne : NL.Nonempty := ⟨w,hw⟩
  letI : Nonempty ↥ND := ⟨⟨D,hD⟩⟩
  letI : Nonempty ↥NL := ⟨⟨w,hw⟩⟩
  refine ⟨ND,NL,hNDne,hNLne,hND,hDcover,hNL,hLcover,?_⟩
  refine ⟨inferInstance,?_⟩
  intro H
  apply freeEnergy_theta_error β θ _ n hβ hθ hn H _ hchoice
  simpa only [Fintype.card_prod,Fintype.card_coe] using hentropy
end GaussianEllipsoid.PaperExactEntropy
#print axioms GaussianEllipsoid.PaperExactEntropy.paper_net_freeEnergy_approximation
