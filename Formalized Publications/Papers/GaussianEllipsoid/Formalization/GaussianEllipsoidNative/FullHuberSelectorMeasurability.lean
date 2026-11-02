import GaussianEllipsoid.SelectorMeasurable

noncomputable section
open scoped Matrix Matrix.Norms.Frobenius Topology Filter ENNReal
open Filter
namespace GaussianEllipsoid

/-- Joint continuity of the full Huber-plus-ridge objective. -/
theorem fullHuberObjective_continuous_joint {d n : ℕ} :
    Continuous fun p : Sample d n × Square d => huberObjective p.1 p.2 := by
  have hres : ∀ i : Fin n,
      Continuous fun p : Sample d n × Square d => residual p.1 p.2 i := by
    intro i
    have hx : Continuous (fun p : Sample d n × Square d => p.1 i) :=
      (continuous_apply i).comp continuous_fst
    exact ((hx.dotProduct (continuous_snd.matrix_mulVec hx)).sub
      continuous_const).div_const _
  have hc : Continuous (fun p : Sample d n × Square d =>
      ∑ i : Fin n, huber (residual p.1 p.2 i)) :=
    continuous_finsetSum _ (fun i _ => huber_continuous.comp (hres i))
  unfold huberObjective empiricalHuber empiricalAverage
  exact (hc.div_const _).add (ridgePenalty_continuous.comp continuous_snd)

/-- Every full minimizer selector is continuous in positive dimension.
This is the same compact unique-minimizer argument as the deleted selector. -/
theorem fullHuberSelector_continuous_pos {d n : Nat} (hd : 1 ≤ d)
    {lo hi : Real} {Sstar : Sample d n → Square d}
    (hSstar : ∀ x, IsHuberMinimizer lo hi x (Sstar x)) :
    Continuous Sstar := by
  rw [continuous_iff_continuousAt]
  intro x0
  show Tendsto Sstar (nhds x0) (nhds (Sstar x0))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hmem : ∀ k, Sstar (ns k) ∈ spectralBox d lo hi :=
    fun k => (hSstar (ns k)).1
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_lim⟩ :=
    IsCompact.tendsto_subseq (isCompact_spectralBox d lo hi) hmem
  have hnsφ : Tendsto (ns ∘ φ) atTop (nhds x0) :=
    hns.comp hφ_mono.tendsto_atTop
  have h2 : Tendsto (fun k => Sstar (ns (φ k))) atTop (nhds a) := by
    simpa [Function.comp_def] using hφ_lim
  have hjoint : Tendsto (fun k => ((ns ∘ φ) k, Sstar (ns (φ k)))) atTop
      (nhds (x0, a)) := by
    have h := hnsφ.prodMk_nhds h2
    simpa using h
  have hF := fullHuberObjective_continuous_joint (d := d) (n := n)
  have hlim1 : Tendsto
      (fun k => huberObjective ((ns ∘ φ) k) (Sstar (ns (φ k))))
      atTop (nhds (huberObjective x0 a)) := by
    have h := (hF.tendsto (x0, a)).comp hjoint
    simpa [Function.comp_def] using h
  have ha_min : IsHuberMinimizer lo hi x0 a := by
    refine ⟨ha_mem, fun T hT => ?_⟩
    have hcT : Continuous (fun _ : Sample d n => T) := continuous_const
    have hTx : Continuous
        (fun x : Sample d n => huberObjective x T) := by
      have h := hF.comp (continuous_id.prodMk hcT)
      simpa [Function.comp_def] using h
    have hlimT : Tendsto (fun k => huberObjective ((ns ∘ φ) k) T)
        atTop (nhds (huberObjective x0 T)) := by
      have h := (hTx.tendsto x0).comp hnsφ
      simpa [Function.comp_def] using h
    have hopt : ∀ k, huberObjective ((ns ∘ φ) k) (Sstar (ns (φ k)))
        ≤ huberObjective ((ns ∘ φ) k) T :=
      fun k => (hSstar ((ns ∘ φ) k)).2 T hT
    exact le_of_tendsto_of_tendsto hlim1 hlimT (Eventually.of_forall hopt)
  have heq : a = Sstar x0 := huberMinimizer_unique hd ha_min (hSstar x0)
  refine ⟨φ, ?_⟩
  have hfin := hφ_lim
  rw [heq] at hfin
  simpa [Function.comp_def] using hfin

/-- Every full Huber selector is continuous, including zero dimension and
an empty sample. No extra measurable-selection premise is assumed. -/
theorem fullHuberSelector_continuous {d n : ℕ} {lo hi : ℝ}
    {Sstar : Sample d n → Square d}
    (hSstar : ∀ x, IsHuberMinimizer lo hi x (Sstar x)) : Continuous Sstar := by
  by_cases hd : 1 ≤ d
  · exact fullHuberSelector_continuous_pos hd hSstar
  · have hd0 : d = 0 := by omega
    subst d
    have heq : Sstar = fun _ => (0 : Square 0) := by
      funext x
      ext i j
      exact Fin.elim0 i
    rw [heq]
    exact continuous_const

/-- The full selector asserted in Section 4 exists and is measurable. -/
theorem fullHuberSelector_exists_measurable (d n : ℕ) (lo hi : ℝ)
    (hlo : 0 < lo) (hle : lo ≤ hi) :
    ∃ Sstar : Sample d n → Square d, Measurable Sstar ∧
      ∀ x, IsHuberMinimizer lo hi x (Sstar x) := by
  choose Sstar hSstar using huberMinimizerExists_theorem d n lo hi hlo hle
  exact ⟨Sstar, (fullHuberSelector_continuous hSstar).measurable, hSstar⟩

#print axioms fullHuberSelector_continuous
#print axioms fullHuberSelector_exists_measurable
end GaussianEllipsoid
