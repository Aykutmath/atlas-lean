import PaperLocalizedMeasurability

noncomputable section
open MeasureTheory Finset GaussianEllipsoid GaussianEllipsoid.SmallBall
namespace GaussianEllipsoid.Localized

def paperLocalizedWindowBad {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c d θ c₀ C₀ : ℝ) : Set Ω :=
  {ω | ∃ q : ℝ, c₀/Real.sqrt d ≤ q ∧ q ≤ C₀ ∧
    ∃ I : Finset (Fin n), (I.card:ℝ) ≤ K*d ∧ ∃ U V : Coeff n,
      (∀ i ∉ I, U i = 0) ∧ (∀ i ∈ I, V i = 0) ∧
      (∑ i, |U i|) ≤ A*q*Real.sqrt d ∧ β*q ≤ ‖V‖ ∧ ‖V‖ ≤ B*q ∧
      Real.sqrt d*‖(fun i : Fin n => V i)‖ ≤ θ*‖V‖ ∧
      spectralNuclearNorm (T ω (U+V)) < c*q*d}

theorem paperLocalizedWindowBad_subset {Ω : Type*} {n r : ℕ}
    (T : Ω → Coeff n →ₗ[ℝ] FrobeniusMatrix r r)
    (A β B K c θ C₀ : ℝ) {d c₀ : ℝ} (hd : 0 < d) (hc₀ : 0 < c₀) :
    paperLocalizedWindowBad T A β B K c d θ c₀ C₀ ⊆ paperLocalizedBad T A β B K c d θ := by
  rintro ω ⟨q,hql,_,I,hI,U,V,hU,hV,hA,hβ,hB,hcap,hbad⟩
  exact ⟨q,(div_pos hc₀ (Real.sqrt_pos.mpr hd)).trans_le hql,I,hI,U,V,hU,hV,hA,hβ,hB,hcap,hbad⟩

theorem isOpen_paperLocalizedWindowBad (d : ℝ) (r n : ℕ) (A β B K c θ c₀ C₀ : ℝ) :
    IsOpen (paperLocalizedWindowBad (localizedOperator d r n) A β B K c d θ c₀ C₀) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨q,hql,hqu,I,hI,U,V,hU,hV,hA,hβ,hB,hcap,hbad⟩
  have hopen : IsOpen {p : BilinearSample r n |
      spectralNuclearNorm (localizedOperator d r n p (U+V)) < c*q*d} :=
    isOpen_lt ((continuous_spectralNuclear r r).comp
      (continuous_localizedOperator_eval d r n (U+V))) continuous_const
  apply Filter.mem_of_superset (hopen.mem_nhds hbad)
  intro p' hp'
  exact ⟨q,hql,hqu,I,hI,U,V,hU,hV,hA,hβ,hB,hcap,hp'⟩

/-- Exact paper small-coordinate restatement, including its stated q window. -/
theorem paper_small_coordinate_window
    {α θ A B β K L c₀ C₀ : ℝ} (hα : α < 1/4)
    (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (hA : 0 < A) (hB : 0 < B) (hβ : 0 < β) (hK : 0 < K) (hL : 0 < L)
    (hc₀ : 0 < c₀) (_hC₀ : 0 < C₀) :
    ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀ ≤ d → (n:ℝ) ≤ α*(d:ℝ)^2 →
      (bilinearGaussianSampleLaw (d/2) n).real
        (paperLocalizedWindowBad (localizedOperator d (d/2) n) A β B K c d θ c₀ C₀ ∩
          frobeniusContinuity (localizedOperator d (d/2) n) L d) ≤
        Real.exp (-γ*(d:ℝ)^2) := by
  obtain ⟨c,γ,hc,hγ,d₀,hbound⟩ := paper_localized_uniform_smallball hα hθ0 hθ hA hB hβ hK hL
  refine ⟨c,γ,hc,hγ,max 1 d₀,?_⟩
  intro d n hd hn
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsub : (paperLocalizedWindowBad (localizedOperator d (d/2) n) A β B K c d θ c₀ C₀ ∩
      frobeniusContinuity (localizedOperator d (d/2) n) L d : Set (BilinearSample (d/2) n)) ⊆
      paperLocalizedBad (localizedOperator d (d/2) n) A β B K c d θ ∩
        frobeniusContinuity (localizedOperator d (d/2) n) L d := by
    intro p hp
    exact ⟨paperLocalizedWindowBad_subset _ A β B K c θ C₀ hd0 hc₀ hp.1,hp.2⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (hbound d n ((le_max_right _ _).trans hd) hn)

end GaussianEllipsoid.Localized
#print axioms GaussianEllipsoid.Localized.paper_small_coordinate_window
