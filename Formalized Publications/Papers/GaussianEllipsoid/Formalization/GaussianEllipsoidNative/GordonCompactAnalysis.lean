import GaussianLinearMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Standalone reuse of the purely analytic compact-passage lemmas in the
user-supplied GordonCompact.lean (SHA256 8f305bcacc60340f005e3ef1af2ee7bd85a8cc1fd083b74efd20a446d7a7c97d).
Only imports/namespace and explicit finite min/max definitions are supplied
here. No centered/affine Gaussian comparison is assumed or asserted.
The source's actual probability comparison still awaits its current imports;
these deterministic and dominated-convergence proofs can be checked now. -/
noncomputable section
open MeasureTheory Filter Topology
namespace BMGordonCompact

def finMin {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

def finMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- The mesh `1/(m+1)` tends to zero (Archimedean). -/
theorem mesh_tendsto_zero :
    ∀ δ > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M → (1 : ℝ) / ((m : ℝ) + 1) < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun m hm => ?_⟩
  have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : (1 : ℝ) / δ < (m : ℝ) := lt_of_lt_of_le hN hNm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  first | rw [one_div_lt hm1 hδ] | rw [one_div_lt _ _ hm1 hδ]
  linarith

/-- Finite `1/(m+1)`-nets exist on a nonempty compact metric space. -/
theorem exists_finset_net (K : Type*) [MetricSpace K] [CompactSpace K]
    [Nonempty K] (m : ℕ) :
    ∃ t : Finset K,
      t.Nonempty ∧ ∀ x : K, ∃ c ∈ t, dist c x < 1 / ((m : ℝ) + 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hm1
  have hcover : (Set.univ : Set K) ⊆ ⋃ c, Metric.ball c (1 / ((m : ℝ) + 1)) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self hr⟩
  obtain ⟨t, ht⟩ := by
    first
      | exact isCompact_univ.elim_finite_subcover
          (fun c => Metric.ball c (1 / ((m : ℝ) + 1)))
          (fun c => Metric.isOpen_ball) hcover
      | exact isCompact_univ.elim_finite_subcover
          (fun c => Metric.ball c (1 / ((m : ℝ) + 1)))
          hcover (fun c => Metric.isOpen_ball)
      | exact isCompact_univ.elim_finite_subcover
          (fun c => Metric.isOpen_ball) hcover
      | exact isCompact_univ.elim_finite_subcover
          hcover (fun c => Metric.isOpen_ball)
  refine ⟨t, ?_, fun x => ?_⟩
  · obtain ⟨k0⟩ := (inferInstance : Nonempty K)
    have hx0 := ht (Set.mem_univ k0)
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx0
    obtain ⟨hc2, _⟩ := Set.mem_iUnion.mp hc
    have hct : c ∈ t := by simpa using hc2
    exact ⟨c, hct⟩
  · have hx := ht (Set.mem_univ x)
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hc2, hball⟩ := Set.mem_iUnion.mp hc
    have hct : c ∈ t := by simpa using hc2
    refine ⟨c, hct, ?_⟩
    rw [dist_comm]
    first | exact mem_ball.mp hball | exact Metric.mem_ball.mp hball

/-- Pathwise convergence of net min-max values to `sInf`/`sSup`
(the unfolded `compactMinMax`) for a continuous path on compact metric
`K × L`, along any net sequence of mesh `→ 0`. -/
theorem netMinMax_tendsto_sInf_sSup
    {K L : Type*} [MetricSpace K] [MetricSpace L]
    [CompactSpace K] [CompactSpace L] [Nonempty K] [Nonempty L]
    (g : K × L → ℝ)
    (ιK ιL : ℕ → Type*) [∀ m, Fintype (ιK m)] [∀ m, Nonempty (ιK m)]
    [∀ m, Fintype (ιL m)] [∀ m, Nonempty (ιL m)]
    (eK : ∀ m, ιK m → K) (eL : ∀ m, ιL m → L)
    (hKcov : ∀ m, ∀ x : K, ∃ i, dist (eK m i) x ≤ 1 / ((m : ℝ) + 1))
    (hLcov : ∀ m, ∀ x : L, ∃ j, dist (eL m j) x ≤ 1 / ((m : ℝ) + 1))
    (hcont : Continuous g) :
    Tendsto (fun m => finMin (fun i => finMax (fun j => g (eK m i, eL m j))))
      atTop
      (𝓝 (sInf ((fun k => sSup ((fun l => g (k, l)) '' Set.univ)) '' Set.univ))) := by
  obtain ⟨k0⟩ := (inferInstance : Nonempty K)
  obtain ⟨l0⟩ := (inferInstance : Nonempty L)
  have hneK : (Set.univ : Set K).Nonempty := ⟨k0, Set.mem_univ k0⟩
  have hneL : (Set.univ : Set L).Nonempty := ⟨l0, Set.mem_univ l0⟩
  have hunivK : IsCompact (Set.univ : Set K) := isCompact_univ
  have hunivL : IsCompact (Set.univ : Set L) := isCompact_univ
  have hunivKL : IsCompact (Set.univ : Set (K × L)) := isCompact_univ
  set S : Set ℝ := (fun k => sSup ((fun l => g (k, l)) '' Set.univ)) '' Set.univ
    with hSdef
  have hGcompact : IsCompact (g '' Set.univ) := hunivKL.image hcont
  have hGbddA : BddAbove (g '' Set.univ) := by
    first | exact hGcompact.bddAbove | exact hGcompact.isBounded.bddAbove
  have hGbddB : BddBelow (g '' Set.univ) := by
    first | exact hGcompact.bddBelow | exact hGcompact.isBounded.bddBelow
  have hrow : ∀ k : K, IsCompact ((fun l => g (k, l)) '' Set.univ) := by
    intro k
    exact hunivL.image
      (hcont.comp (Continuous.prodMk continuous_const continuous_id))
  have hrowne : ∀ k : K, ((fun l => g (k, l)) '' Set.univ).Nonempty :=
    fun k => hneL.image _
  have hrowbddA : ∀ k : K, BddAbove ((fun l => g (k, l)) '' Set.univ) := by
    intro k
    first | exact (hrow k).bddAbove | exact (hrow k).isBounded.bddAbove
  have hSne : S.Nonempty := hneK.image _
  have hSbddB : BddBelow S := by
    refine ⟨sInf (g '' Set.univ), mem_lowerBounds.mpr ?_⟩
    intro b hb
    rw [hSdef] at hb
    obtain ⟨k, _, rfl⟩ := hb
    have h1 : sInf (g '' Set.univ) ≤ g (k, l0) := by
      apply csInf_le
      first | exact hGbddB | exact ⟨(k, l0), Set.mem_univ _, rfl⟩
      first | exact hGbddB | exact ⟨(k, l0), Set.mem_univ _, rfl⟩
    have h2 : g (k, l0) ≤ sSup ((fun l => g (k, l)) '' Set.univ) := by
      apply le_csSup
      first | exact hrowbddA k | exact ⟨l0, Set.mem_univ l0, rfl⟩
      first | exact hrowbddA k | exact ⟨l0, Set.mem_univ l0, rfl⟩
    exact h1.trans h2
  have hUC : UniformContinuousOn g Set.univ :=
    hunivKL.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδpos, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
  obtain ⟨M1, hM1⟩ := mesh_tendsto_zero δ hδpos
  obtain ⟨M2, hM2⟩ := mesh_tendsto_zero δ hδpos
  refine ⟨max M1 M2, fun m hm => ?_⟩
  have hm1 : m ≥ M1 := le_trans (le_max_left M1 M2) hm
  have hm2 : m ≥ M2 := le_trans (le_max_right M1 M2) hm
  have hmeshK : (1 : ℝ) / ((m : ℝ) + 1) < δ := hM1 m hm1
  have hmeshL : (1 : ℝ) / ((m : ℝ) + 1) < δ := hM2 m hm2
  show dist (finMin (fun i => finMax (fun j => g (eK m i, eL m j)))) (sInf S) < ε
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- Lower bound: every net row value is at least `sInf S - ε/2`.
    have hrow2 : ∀ i,
        sSup ((fun l => g (eK m i, l)) '' Set.univ)
          ≤ finMax (fun j => g (eK m i, eL m j)) + ε / 2 := by
      intro i
      first | refine csSup_le (hrowne _) ?_ | refine csSup_le (hrowne _)
      rintro b ⟨l, _, rfl⟩
      show g (eK m i, l) ≤ finMax (fun j => g (eK m i, eL m j)) + ε / 2
      obtain ⟨j, hj⟩ := hLcov m l
      have hdist : dist (eL m j) l < δ := lt_of_le_of_lt hj hmeshL
      have hd : dist (eK m i, eL m j) (eK m i, l) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact hdist
      have hmod2 := hmod _ (Set.mem_univ _) _ (Set.mem_univ _) hd
      rw [Real.dist_eq, abs_lt] at hmod2
      have hle : g (eK m i, eL m j) ≤ finMax (fun j => g (eK m i, eL m j)) := by
        unfold finMax
        first
          | exact Finset.le_sup' _ (fun j => g (eK m i, eL m j)) (Finset.mem_univ j)
          | exact Finset.le_sup' (fun j => g (eK m i, eL m j)) _ (Finset.mem_univ j)
          | exact Finset.le_sup' _ (fun j => g (eK m i, eL m j)) _ (Finset.mem_univ j)
          | exact Finset.le_sup' _ _ (fun j => g (eK m i, eL m j)) (Finset.mem_univ j)
          | exact Finset.le_sup' (fun j => g (eK m i, eL m j)) (Finset.mem_univ j)
      linarith [hmod2.1, hmod2.2, hle]
    have hMle : ∀ i, sInf S ≤ sSup ((fun l => g (eK m i, l)) '' Set.univ) := by
      intro i
      have hmem : sSup ((fun l => g (eK m i, l)) '' Set.univ) ∈ S := by
        rw [hSdef]
        exact ⟨eK m i, Set.mem_univ _, rfl⟩
      apply csInf_le
      first | exact hSbddB | exact hmem
      first | exact hSbddB | exact hmem
    have hfin : sInf S - ε / 2
        ≤ finMin (fun i => finMax (fun j => g (eK m i, eL m j))) := by
      unfold finMin
      refine Finset.le_inf' ?_ (fun i => finMax (fun j => g (eK m i, eL m j))) ?_
      intro i _
      show sInf S - ε / 2 ≤ finMax (fun j => g (eK m i, eL m j))
      have h1 := hrow2 i
      have h2 := hMle i
      linarith
    linarith [hfin, hε]
  · -- Upper bound: the net value is below `sInf S + ε`.
    have hex : ∃ k,
        sSup ((fun l => g (k, l)) '' Set.univ) < sInf S + ε / 2 := by
      by_contra hcon
      have hcon' : ∀ k,
          sInf S + ε / 2 ≤ sSup ((fun l => g (k, l)) '' Set.univ) :=
        fun k => le_of_not_gt (fun h => hcon ⟨k, h⟩)
      have hle : sInf S + ε / 2 ≤ sInf S := by
        first | refine le_csInf hSne ?_ | refine le_csInf hSne
        intro b hb
        rw [hSdef] at hb
        obtain ⟨k, _, rfl⟩ := hb
        exact hcon' k
      linarith [hε]
    obtain ⟨k0, hk0⟩ := hex
    obtain ⟨i, hi⟩ := hKcov m k0
    have hdist : dist (eK m i) k0 < δ := lt_of_le_of_lt hi hmeshK
    have hle1 : finMin (fun i => finMax (fun j => g (eK m i, eL m j)))
        ≤ finMax (fun j => g (eK m i, eL m j)) := by
      unfold finMin
      first
        | exact Finset.inf'_le _ (Finset.mem_univ i)
        | exact Finset.inf'_le (Finset.mem_univ i)
    have hle2 : finMax (fun j => g (eK m i, eL m j))
        ≤ sSup ((fun l => g (k0, l)) '' Set.univ) + ε / 2 := by
      unfold finMax
      refine Finset.sup'_le ?_ (fun j => g (eK m i, eL m j)) ?_
      intro j _
      show g (eK m i, eL m j) ≤ sSup ((fun l => g (k0, l)) '' Set.univ) + ε / 2
      have hd : dist (eK m i, eL m j) (k0, eL m j) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact hdist
      have hmod2 := hmod _ (Set.mem_univ _) _ (Set.mem_univ _) hd
      rw [Real.dist_eq, abs_lt] at hmod2
      have hle : g (k0, eL m j) ≤ sSup ((fun l => g (k0, l)) '' Set.univ) := by
        apply le_csSup
        first | exact hrowbddA k0 | exact ⟨eL m j, Set.mem_univ _, rfl⟩
        first | exact hrowbddA k0 | exact ⟨eL m j, Set.mem_univ _, rfl⟩
      linarith [hmod2.1, hmod2.2, hle]
    linarith [hle1, hle2, hk0]

/-- Domination shape: a net min-max value is bounded by the sum of
absolute marginal values over the net. -/
theorem abs_netMinMax_le_sum {K L : Type*} (g : K × L → ℝ)
    (ιK ιL : Type*) [Fintype ιK] [Nonempty ιK] [Fintype ιL] [Nonempty ιL]
    (eK : ιK → K) (eL : ιL → L) :
    |finMin (fun i => finMax (fun j => g (eK i, eL j)))|
      ≤ ∑ i, ∑ j, |g (eK i, eL j)| := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ιK)
  obtain ⟨j0⟩ := (inferInstance : Nonempty ιL)
  rw [abs_le]
  constructor
  · unfold finMin
    refine Finset.le_inf' ?_ (fun i => finMax (fun j => g (eK i, eL j))) ?_
    intro i _
    show -(∑ i, ∑ j, |g (eK i, eL j)|) ≤ finMax (fun j => g (eK i, eL j))
    have h1 : g (eK i, eL j0) ≤ finMax (fun j => g (eK i, eL j)) := by
      unfold finMax
      first
        | exact Finset.le_sup' _ (fun j => g (eK i, eL j)) (Finset.mem_univ j0)
        | exact Finset.le_sup' (fun j => g (eK i, eL j)) _ (Finset.mem_univ j0)
        | exact Finset.le_sup' _ (fun j => g (eK i, eL j)) _ (Finset.mem_univ j0)
        | exact Finset.le_sup' _ _ (fun j => g (eK i, eL j)) (Finset.mem_univ j0)
        | exact Finset.le_sup' (fun j => g (eK i, eL j)) (Finset.mem_univ j0)
    have h2 : -|g (eK i, eL j0)| ≤ g (eK i, eL j0) := by apply neg_abs_le
    have h3 : |g (eK i, eL j0)| ≤ ∑ j, |g (eK i, eL j)| := by
      first
        | exact Finset.single_le_sum (Finset.mem_univ j0)
            (fun j _ => show (0 : ℝ) ≤ |g (eK i, eL j)| from by apply abs_nonneg)
        | exact Finset.single_le_sum
            (fun j _ => show (0 : ℝ) ≤ |g (eK i, eL j)| from by apply abs_nonneg)
            (Finset.mem_univ j0)
    have h4nn1 : ∀ i ∈ (Finset.univ : Finset ιK),
        (0 : ℝ) ≤ ∑ j, |g (eK i, eL j)| := by
      intro i _
      apply Finset.sum_nonneg
      intro j _
      apply abs_nonneg
    have h4 : (∑ j, |g (eK i, eL j)|) ≤ ∑ i, ∑ j, |g (eK i, eL j)| :=
      Finset.single_le_sum h4nn1 (Finset.mem_univ i)
    linarith
  · have h1 : finMin (fun i => finMax (fun j => g (eK i, eL j)))
        ≤ finMax (fun j => g (eK i0, eL j)) := by
      unfold finMin
      first
        | exact Finset.inf'_le _ (Finset.mem_univ i0)
        | exact Finset.inf'_le (Finset.mem_univ i0)
    have h2 : finMax (fun j => g (eK i0, eL j))
        ≤ ∑ j, |g (eK i0, eL j)| := by
      unfold finMax
      refine Finset.sup'_le ?_ (fun j => g (eK i0, eL j)) ?_
      intro j _
      show g (eK i0, eL j) ≤ ∑ j, |g (eK i0, eL j)|
      have ha : g (eK i0, eL j) ≤ |g (eK i0, eL j)| := by apply le_abs_self
      have hb : |g (eK i0, eL j)| ≤ ∑ j, |g (eK i0, eL j)| := by
        first
          | exact Finset.single_le_sum (Finset.mem_univ j)
              (fun j _ => show (0 : ℝ) ≤ |g (eK i0, eL j)| from by apply abs_nonneg)
          | exact Finset.single_le_sum
              (fun j _ => show (0 : ℝ) ≤ |g (eK i0, eL j)| from by apply abs_nonneg)
              (Finset.mem_univ j)
      linarith
    have h4nn2 : ∀ i ∈ (Finset.univ : Finset ιK),
        (0 : ℝ) ≤ ∑ j, |g (eK i, eL j)| := by
      intro i _
      apply Finset.sum_nonneg
      intro j _
      apply abs_nonneg
    have h3 : (∑ j, |g (eK i0, eL j)|) ≤ ∑ i, ∑ j, |g (eK i, eL j)| :=
      Finset.single_le_sum h4nn2 (Finset.mem_univ i0)
    linarith [h1, h2, h3]

/-- Dominated-convergence passage for net min-max expectations. -/
theorem integral_tendsto_of_dominated {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {bound : Ω → ℝ}
    (hbound : Integrable bound P)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ bound ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  first
    | exact tendsto_integral_of_dominated_convergence bound hmeas hbound hdom hlim
    | exact tendsto_integral_of_dominated_convergence bound hmeas hbound hlim hdom


end BMGordonCompact
