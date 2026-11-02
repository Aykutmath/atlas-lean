/-
Discharge of the deleted-selector measurability premise (paper Section 4):
deleted Huber minimizers can be chosen measurably and locally (depending
only on the observations other than the held-out one).

No Berge maximum theorem is needed: the feasible set (spectral box) is
constant and compact, the objective jointly continuous, and the minimizer
unique by ridge strict convexity, so a cluster-point argument gives
selector continuity, hence measurability; locality follows from uniqueness.
Mathematical source: paper.tex, Section 4.
-/
import GaussianEllipsoid.HuberDischarge

open scoped Matrix Matrix.Norms.Frobenius Topology Filter ENNReal
open Filter

noncomputable section

namespace GaussianEllipsoid

/-- First-countability of square matrices by defeq to the pi type
(direct `inferInstance` fails since no instance head matches `Matrix`,
but the `Matrix` topology IS the pi topology). -/
instance square_firstCountable (d : Nat) : FirstCountableTopology (Square d) :=
  inferInstanceAs (FirstCountableTopology (Fin d → Fin d → ℝ))

/-- The deleted objective is strictly midpoint-convex in positive
dimension when `1 < n` (the Huber sum is midpoint-convex, the ridge is
strictly so). Mirrors `huberObjective_strict_midpoint`. -/
theorem deletedHuberObjective_strict_midpoint {d n : Nat} (hd : 1 ≤ d)
    (hn : 1 < n) (x : Sample d n) (j : Fin n)
    {S T : Square d} (hne : S ≠ T) :
    deletedHuberObjective x j ((1/2 : ℝ) • (S + T))
      < (deletedHuberObjective x j S + deletedHuberObjective x j T) / 2 := by
  have hdiv : ∀ (f : Fin n → ℝ),
      ∑ i ∈ Finset.univ.erase j, f i / 2
        = (∑ i ∈ Finset.univ.erase j, f i) / 2 := by
    intro f
    calc ∑ i ∈ Finset.univ.erase j, f i / 2
        = ∑ i ∈ Finset.univ.erase j, f i * (1/2 : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i ∈ Finset.univ.erase j, f i) * (1/2 : ℝ) :=
          (Finset.sum_mul _ _ _).symm
      _ = (∑ i ∈ Finset.univ.erase j, f i) / 2 := by ring
  have hHub : (∑ i ∈ Finset.univ.erase j,
          huber (residual x ((1/2 : ℝ) • (S + T)) i)) / ((n : ℝ) - 1)
      ≤ ((∑ i ∈ Finset.univ.erase j, huber (residual x S i)) / ((n : ℝ) - 1)
        + (∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / ((n : ℝ) - 1)) / 2 := by
    have hcoord : ∀ i ∈ Finset.univ.erase j,
        huber (residual x ((1/2 : ℝ) • (S + T)) i)
          ≤ (huber (residual x S i) + huber (residual x T i)) / 2 := by
      intro i _
      rw [residual_mid hd x S T i]
      exact huber_midpoint
    have hle : ∑ i ∈ Finset.univ.erase j,
            huber (residual x ((1/2 : ℝ) • (S + T)) i)
        ≤ ∑ i ∈ Finset.univ.erase j,
            (huber (residual x S i) + huber (residual x T i)) / 2 :=
      Finset.sum_le_sum hcoord
    have heq : ∑ i ∈ Finset.univ.erase j,
            (huber (residual x S i) + huber (residual x T i)) / 2
        = (∑ i ∈ Finset.univ.erase j, huber (residual x S i)
          + ∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / 2 := by
      calc ∑ i ∈ Finset.univ.erase j,
              (huber (residual x S i) + huber (residual x T i)) / 2
          = ∑ i ∈ Finset.univ.erase j,
              (huber (residual x S i) / 2
                + huber (residual x T i) / 2) := by
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i ∈ Finset.univ.erase j, huber (residual x S i) / 2
            + ∑ i ∈ Finset.univ.erase j, huber (residual x T i) / 2 :=
              Finset.sum_add_distrib
        _ = (∑ i ∈ Finset.univ.erase j, huber (residual x S i)) / 2
            + (∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / 2 := by
              rw [hdiv, hdiv]
        _ = (∑ i ∈ Finset.univ.erase j, huber (residual x S i)
            + ∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / 2 := by
              rw [add_div]
    have hle2 : ∑ i ∈ Finset.univ.erase j,
            huber (residual x ((1/2 : ℝ) • (S + T)) i)
        ≤ (∑ i ∈ Finset.univ.erase j, huber (residual x S i)
          + ∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / 2 := by
      linarith [hle, heq]
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have h1n : (1 : ℝ) < n := by exact_mod_cast hn
      linarith
    have hn1ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
    have hrw : (((∑ i ∈ Finset.univ.erase j, huber (residual x S i)) / ((n : ℝ) - 1)
          + (∑ i ∈ Finset.univ.erase j, huber (residual x T i)) / ((n : ℝ) - 1))) / 2
          = (((∑ i ∈ Finset.univ.erase j, huber (residual x S i))
            + (∑ i ∈ Finset.univ.erase j, huber (residual x T i))) / 2) / ((n : ℝ) - 1) := by
      field_simp
    rw [hrw]
    exact div_le_div_of_nonneg_right hle2 hn1.le
  have hRidge := ridge_strict_midpoint hd hne
  unfold deletedHuberObjective
  linarith [hHub, hRidge]

/-- Deleted minimizers in the spectral box are unique. Mirrors
`huberMinimizer_unique`. Together with `deletedHuberMinimizerExists`,
each `(x, j)` determines exactly one deleted selector value. -/
theorem deletedHuberMinimizer_unique {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    {lo hi : Real} {x : Sample d n} {j : Fin n} {S T : Square d}
    (hS : IsDeletedMinimizer lo hi x j S)
    (hT : IsDeletedMinimizer lo hi x j T) :
    S = T := by
  by_contra hne
  have hmid := deletedHuberObjective_strict_midpoint hd hn x j hne
  have hbox := spectralBox_convex_mid hS.1 hT.1
  have h1 := hS.2 _ hbox
  have h2 := hT.2 _ hbox
  linarith

/-- Joint continuity of `quadratic` (local copy used by the deleted
objective; see also the package `continuous_quadratic`). -/
theorem quadratic_joint_continuous {d : Nat} :
    Continuous fun p : Square d × Vector d => quadratic p.1 p.2 := by
  unfold quadratic
  exact Continuous.dotProduct continuous_snd
    (Continuous.matrix_mulVec continuous_fst continuous_snd)

/-- The deleted objective is jointly continuous in `(x, S)`. The
package only had continuity in `S` (`deletedHuberObjective_continuous`);
joint continuity is the input the argmin-continuity argument needs. -/
theorem deletedHuberObjective_continuous_joint {d n : Nat} (j : Fin n) :
    Continuous fun p : Sample d n × Square d =>
      deletedHuberObjective p.1 j p.2 := by
  have hres : ∀ i : Fin n,
      Continuous fun p : Sample d n × Square d => residual p.1 p.2 i := by
    intro i
    have heq : (fun p : Sample d n × Square d => residual p.1 p.2 i)
        = fun p => (quadratic p.2 (p.1 i) - (d : ℝ)) / Real.sqrt (d : ℝ) := by
      funext p
      rfl
    rw [heq]
    have hproj : Continuous fun p : Sample d n × Square d => p.1 i :=
      Continuous.comp
        (show Continuous fun x : Sample d n => x i from continuous_apply i)
        continuous_fst
    exact ((Continuous.comp quadratic_joint_continuous
      (Continuous.prodMk continuous_snd hproj)).sub
      continuous_const).div_const _
  have huber_part : Continuous fun p : Sample d n × Square d =>
      (∑ i ∈ Finset.univ.erase j, huber (residual p.1 p.2 i))
        / ((n : ℝ) - 1) := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun i _ =>
      huber_continuous.comp (hres i)
  have heq : (fun p : Sample d n × Square d => deletedHuberObjective p.1 j p.2)
      = fun p => (∑ i ∈ Finset.univ.erase j, huber (residual p.1 p.2 i))
        / ((n : ℝ) - 1) + ridgePenalty d p.2 := by
    funext p
    rfl
  rw [heq]
  exact huber_part.add (ridgePenalty_continuous.comp continuous_snd)

/-- The deleted objective depends only on the observations other than j. -/
theorem deletedHuberObjective_locality {d n : Nat} {x y : Sample d n} {j : Fin n}
    (h : ∀ i, i ≠ j → x i = y i) (S : Square d) :
    deletedHuberObjective x j S = deletedHuberObjective y j S := by
  unfold deletedHuberObjective
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ j := (Finset.mem_erase.mp hi).1
  have hxy : x i = y i := h i hne
  unfold residual
  rw [hxy]

/-- The deleted-minimizer predicate coincides for samples agreeing off j. -/
theorem isDeletedMinimizer_congr_of_agree {d n : Nat} {lo hi : Real}
    {x y : Sample d n} {j : Fin n}
    (h : ∀ i, i ≠ j → x i = y i) (S : Square d) :
    IsDeletedMinimizer lo hi x j S ↔ IsDeletedMinimizer lo hi y j S := by
  unfold IsDeletedMinimizer
  constructor
  · intro hSx
    refine ⟨hSx.1, fun T hT => ?_⟩
    have e1 := deletedHuberObjective_locality h S
    have e2 := deletedHuberObjective_locality h T
    rw [← e1, ← e2]
    exact hSx.2 T hT
  · intro hSy
    refine ⟨hSy.1, fun T hT => ?_⟩
    have e1 := deletedHuberObjective_locality h S
    have e2 := deletedHuberObjective_locality h T
    rw [e1, e2]
    exact hSy.2 T hT

/-- Any deleted-selector function is continuous (main case `1 ≤ d`, `1 < n`).
Cluster-point argument on the compact spectral box: every subsequence of
selector values has a further subsequence converging to a minimizer at the
limit sample, which by uniqueness is the selector value; then
`tendsto_of_subseq_tendsto` upgrades to full continuity. No Berge theorem
or measurable selection is needed. -/
theorem deletedSelector_continuous {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    {lo hi : Real} {j : Fin n} {Sdel : Sample d n → Square d}
    (hSdel : ∀ x, IsDeletedMinimizer lo hi x j (Sdel x)) :
    Continuous Sdel := by
  rw [continuous_iff_continuousAt]
  intro x0
  show Tendsto Sdel (nhds x0) (nhds (Sdel x0))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hmem : ∀ k, Sdel (ns k) ∈ spectralBox d lo hi :=
    fun k => (hSdel (ns k)).1
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_lim⟩ :=
    IsCompact.tendsto_subseq (isCompact_spectralBox d lo hi) hmem
  have hnsφ : Tendsto (ns ∘ φ) atTop (nhds x0) :=
    hns.comp hφ_mono.tendsto_atTop
  have h2 : Tendsto (fun k => Sdel (ns (φ k))) atTop (nhds a) := by
    simpa [Function.comp_def] using hφ_lim
  have hjoint : Tendsto (fun k => ((ns ∘ φ) k, Sdel (ns (φ k)))) atTop
      (nhds (x0, a)) := by
    have h := hnsφ.prodMk_nhds h2
    simpa using h
  have hF := deletedHuberObjective_continuous_joint (d := d) (n := n) j
  have hlim1 : Tendsto
      (fun k => deletedHuberObjective ((ns ∘ φ) k) j (Sdel (ns (φ k))))
      atTop (nhds (deletedHuberObjective x0 j a)) := by
    have h := (hF.tendsto (x0, a)).comp hjoint
    simpa [Function.comp_def] using h
  have ha_min : IsDeletedMinimizer lo hi x0 j a := by
    refine ⟨ha_mem, fun T hT => ?_⟩
    have hcT : Continuous (fun _ : Sample d n => T) := continuous_const
    have hTx : Continuous
        (fun x : Sample d n => deletedHuberObjective x j T) := by
      have h := hF.comp (continuous_id.prodMk hcT)
      simpa [Function.comp_def] using h
    have hlimT : Tendsto (fun k => deletedHuberObjective ((ns ∘ φ) k) j T)
        atTop (nhds (deletedHuberObjective x0 j T)) := by
      have h := (hTx.tendsto x0).comp hnsφ
      simpa [Function.comp_def] using h
    have hopt : ∀ k, deletedHuberObjective ((ns ∘ φ) k) j (Sdel (ns (φ k)))
        ≤ deletedHuberObjective ((ns ∘ φ) k) j T :=
      fun k => (hSdel ((ns ∘ φ) k)).2 T hT
    exact le_of_tendsto_of_tendsto hlim1 hlimT (Eventually.of_forall hopt)
  have heq : a = Sdel x0 := deletedHuberMinimizer_unique hd hn ha_min (hSdel x0)
  refine ⟨φ, ?_⟩
  have hfin := hφ_lim
  rw [heq] at hfin
  simpa [Function.comp_def] using hfin

/-- Measurable deleted selectors exist with locality (main case `1 ≤ d`,
`1 < n`). Matches the `deletedSelectorMeasurable` binder shape
(BelowObjects.lean) under the main-case hypotheses. -/
theorem deletedSelectorMeasurable_main {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    (lo hi : Real) (_hlo : 0 < lo) (hle : lo ≤ hi) (j : Fin n) :
    ∃ Sdel : Sample d n → Square d,
      Measurable Sdel
      ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x))
      ∧ ∀ x y : Sample d n, (∀ i, i ≠ j → x i = y i) → Sdel x = Sdel y := by
  have hex : ∀ x : Sample d n, ∃ S, IsDeletedMinimizer lo hi x j S :=
    fun x => deletedHuberMinimizerExists hle x j
  choose Sdel hSdel using hex
  have hcont : Continuous Sdel := deletedSelector_continuous hd hn hSdel
  refine ⟨Sdel, hcont.measurable, hSdel, fun x y hxy => ?_⟩
  have hSx : IsDeletedMinimizer lo hi y j (Sdel x) :=
    (isDeletedMinimizer_congr_of_agree hxy (Sdel x)).mp (hSdel x)
  exact deletedHuberMinimizer_unique hd hn hSx (hSdel y)

/-- Deleted selectors in dimension zero: the sample and matrix types are
subsingletons, so a constant selector works. -/
theorem deletedSelectorMeasurable_d0 {n : Nat}
    (lo hi : Real) (hle : lo ≤ hi) (j : Fin n) :
    ∃ Sdel : Sample 0 n → Square 0,
      Measurable Sdel
      ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x))
      ∧ ∀ x y : Sample 0 n, (∀ i, i ≠ j → x i = y i) → Sdel x = Sdel y := by
  obtain ⟨S0, hS0⟩ :=
    deletedHuberMinimizerExists (d := 0) hle (fun _ _ => (0 : ℝ)) j
  refine ⟨fun _ => S0, measurable_const, fun x => ?_, fun x y _ => rfl⟩
  have hxy : ∀ i, i ≠ j → (fun _ _ => (0 : ℝ)) i = x i :=
    fun i _ => Subsingleton.elim _ _
  exact (isDeletedMinimizer_congr_of_agree (d := 0) (n := n) hxy S0).mp hS0

/-- For a single observation the deleted sum is empty, so the deleted
objective equals the ridge penalty. -/
theorem deletedHuberObjective_n1 {d : Nat} (x : Sample d 1) (j : Fin 1)
    (S : Square d) :
    deletedHuberObjective x j S = ridgePenalty d S := by
  have hsum0 : ∀ f : Fin 1 → ℝ,
      ∑ i ∈ Finset.univ.erase j, f i = 0 := by
    intro f
    apply Finset.sum_eq_zero
    intro i hi
    exact absurd (Subsingleton.elim i j) (Finset.mem_erase.mp hi).1
  unfold deletedHuberObjective
  rw [hsum0, zero_div, zero_add]

/-- Deleted selectors for a single observation: the objective is
x-independent (ridge only), so the unique minimizer is constant in x. -/
theorem deletedSelectorMeasurable_n1 {d : Nat} (hd : 1 ≤ d)
    (lo hi : Real) (_hlo : 0 < lo) (hle : lo ≤ hi) (j : Fin 1) :
    ∃ Sdel : Sample d 1 → Square d,
      Measurable Sdel
      ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x))
      ∧ ∀ x y : Sample d 1, (∀ i, i ≠ j → x i = y i) → Sdel x = Sdel y := by
  have hstrict : ∀ (x : Sample d 1) {S T : Square d}, S ≠ T →
      deletedHuberObjective x j ((1/2 : ℝ) • (S + T))
        < (deletedHuberObjective x j S + deletedHuberObjective x j T) / 2 := by
    intro x S T hne
    rw [deletedHuberObjective_n1, deletedHuberObjective_n1,
      deletedHuberObjective_n1]
    exact ridge_strict_midpoint hd hne
  have huniq : ∀ {x : Sample d 1} {S T : Square d},
      IsDeletedMinimizer lo hi x j S → IsDeletedMinimizer lo hi x j T →
      S = T := by
    intro x S T hS hT
    by_contra hne
    have hmid := hstrict x hne
    have hbox := spectralBox_convex_mid hS.1 hT.1
    have h1 := hS.2 _ hbox
    have h2 := hT.2 _ hbox
    linarith
  have hex : ∀ x : Sample d 1, ∃ S, IsDeletedMinimizer lo hi x j S :=
    fun x => deletedHuberMinimizerExists hle x j
  choose Sdel hSdel using hex
  have hconst : ∀ x y : Sample d 1, Sdel x = Sdel y := by
    intro x y
    have hxy : ∀ i, i ≠ j → x i = y i :=
      fun i hne => absurd (Subsingleton.elim i j) hne
    have hSx : IsDeletedMinimizer lo hi y j (Sdel x) :=
      (isDeletedMinimizer_congr_of_agree hxy (Sdel x)).mp (hSdel x)
    exact huniq hSx (hSdel y)
  have hcont : Continuous Sdel := by
    have heq : Sdel = fun _ => Sdel (fun _ _ => (0 : ℝ)) :=
      funext fun x => hconst x _
    rw [heq]
    exact continuous_const
  refine ⟨Sdel, hcont.measurable, hSdel, fun x y _ => hconst x y⟩

/-- Deleted selectors can be chosen measurably and locally: exact
`deletedSelectorMeasurable`. Main case (`1 ≤ d`, `1 < n`) by uniqueness +
joint continuity + cluster-point argmin continuity; `n = 0` vacuous;
`d = 0` by subsingleton; `n = 1` by ridge-only constancy. -/
theorem deletedSelectorMeasurable_theorem : deletedSelectorMeasurable := by
  intro d n lo hi hlo hle j
  by_cases hd : 1 ≤ d
  · by_cases hn : 1 < n
    · exact deletedSelectorMeasurable_main hd hn lo hi hlo hle j
    · by_cases hn0 : n = 0
      · subst hn0
        have h := j.2
        omega
      · have hn1 : n = 1 := by omega
        subst hn1
        exact deletedSelectorMeasurable_n1 hd lo hi hlo hle j
  · have hd0 : d = 0 := by omega
    subst hd0
    by_cases hn0 : n = 0
    · subst hn0
      have h := j.2
      omega
    · exact deletedSelectorMeasurable_d0 lo hi hle j

end GaussianEllipsoid
