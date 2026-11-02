/-
Below-threshold interface objects: the Huber selector box, the mixed norm
`N_η` and its dual majorant, the quotient residual `κ_d`, the rank-one
independence event, and the section-level interface propositions.

- `bmApproximateFitting` is the EXTERNAL Bandeira-Maillard premise (paper
  Section 3, Theorem 1.4 of Bandeira-Maillard 2025), used only through its
  statement.
- `MixedNormBound` is the Section 11 mixed-norm lower bound
  (main-theorem-7-1), stated faithfully.
- `HuberResiduals` is the Section 4 conclusion (main-proposition-3-1) in
  the dual-norm form its Section 12 use needs.
- `QuotientBridge` is the Section 12 quotient-duality consequence: the
  mixed-norm bound implies the `κ_d` upper bound.
- `HuberMinimizerExists` is the selector existence obligation (compactness
  + continuity, paper Section 4).
- `davidsonSzarekCovariance`, `deletedSelectorMeasurable`, and
  `hansonWrightChaos` are the Section 4 concentration/selection externals
  (Davidson–Szarek, unique-minimizer measurability, Rudelson–Vershynin).
All are explicit named propositions with paper provenance, never axioms.
The two theorems proved here (`mixedNorm_holder`,
`measurementT_eq_center_residual`) are the elementary analytic bridges.
Mathematical source: paper.tex, Sections 3, 4, 11, and 12.
-/
import GaussianEllipsoid.Basic
import GaussianEllipsoid.Centering
import GaussianEllipsoid.Coordinates
import GaussianEllipsoid.ExactFit
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.Spanning
import GaussianEllipsoid.NormBridges
import GaussianEllipsoid.RobustLoss
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Matrix.MeasurableSpace

noncomputable section

namespace GaussianEllipsoid

/-! ### Spectral box and Huber selector -/

/-- The paper's fixed spectral interval `S_d = {S : λ₋I ⪯ S ⪯ λ₊I}`. -/
def spectralBox (d : Nat) (lo hi : Real) : Set (Square d) :=
  {S | (S - lo • (1 : Square d)).PosSemidef ∧
    ((hi • (1 : Square d)) - S).PosSemidef}

/-- The paper's ridge penalty `R_d(S) = τ_d / (2d) ‖S - I‖_F^2` with `τ_d = d⁻²`. -/
def ridgePenalty (d : Nat) (S : Square d) : Real :=
  ((d : Real) ^ 2)⁻¹ / (2 * d) * (frobeniusNorm (S - 1)) ^ 2

/-- The paper's Huber-plus-ridge objective `H_d(S) + R_d(S)`. -/
def huberObjective {d n : Nat} (x : Sample d n) (S : Square d) : Real :=
  empiricalHuber (residual x S) + ridgePenalty d S

/-- A matrix is a Huber minimizer if it lies in the spectral box and
minimizes the Huber-plus-ridge objective there. -/
def IsHuberMinimizer {d n : Nat} (lo hi : Real) (x : Sample d n)
    (S : Square d) : Prop :=
  S ∈ spectralBox d lo hi ∧
    ∀ T ∈ spectralBox d lo hi, huberObjective x S ≤ huberObjective x T

/-- Selector existence (paper Section 4: compactness gives existence).
Proof obligation: compactness of the spectral box plus continuity of the
objective. Tracked explicitly; the assemblies take it as a premise. -/
def HuberMinimizerExists : Prop :=
  ∀ (d n : Nat) (lo hi : Real), 0 < lo → lo ≤ hi →
    ∀ x : Sample d n, ∃ S, IsHuberMinimizer lo hi x S

/-! ### Deleted selectors -/

/-- The deleted Huber-plus-ridge objective, omitting observation `j`. -/
def deletedHuberObjective {d n : Nat} (x : Sample d n) (j : Fin n)
    (S : Square d) : Real :=
  (∑ i ∈ Finset.univ.erase j, huber (residual x S i)) / ((n : ℝ) - 1)
    + ridgePenalty d S

/-- A deleted minimizer: in the box, minimizing the deleted objective. -/
def IsDeletedMinimizer {d n : Nat} (lo hi : Real) (x : Sample d n)
    (j : Fin n) (S : Square d) : Prop :=
  S ∈ spectralBox d lo hi ∧
    ∀ T ∈ spectralBox d lo hi,
      deletedHuberObjective x j S ≤ deletedHuberObjective x j T

/-! ### Bandeira-Maillard external premise (paper Section 3) -/

/-- The minimized `L^r` residual risk over the spectral box. -/
def bmMinRisk (d n : Nat) (x : Sample d n) (lo hi r : Real) : Real :=
  sInf {t : Real | ∃ S ∈ spectralBox d lo hi,
    t = (1 / (n : Real)) * ∑ i, |residual x S i| ^ r}

/-- The Bandeira-Maillard approximate-fitting limit: for every `1 ≤ r < 4/3`
the minimized risk tends to zero in probability. -/
def BMminRisk (n : Nat → Nat) (lo hi : Real) : Prop :=
  ∀ r : Real, 1 ≤ r → r < 4 / 3 → ∀ ε > 0,
    Filter.Tendsto (fun d => ((gaussianSampleLaw d (n d))
      {x | ε < bmMinRisk d (n d) x lo hi r}).toReal)
      Filter.atTop (nhds 0)

/-- EXTERNAL PREMISE (Bandeira-Maillard 2025, Theorem 1.4, via paper
Section 3): below the threshold there is a fixed spectral interval on
which the approximate-fitting limit holds. Used only through this
statement; it is one of the eight explicit external premises. -/
def bmApproximateFitting : Prop :=
  ∀ n : Nat → Nat, (∀ d, 0 < n d) →
    Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal) →
    ∃ lo hi : Real, 0 < lo ∧ lo ≤ hi ∧ BMminRisk n lo hi

/-! ### Section 4 concentration and chaos externals -/

/-- The full sample covariance `(1/n)∑ᵢ xᵢxᵢᵀ`. -/
def sampleCovariance {d n : Nat} (x : Sample d n) : Square d :=
  ((n : ℝ))⁻¹ • (∑ i, Matrix.vecMulVec (x i) (x i))

/-- EXTERNAL PREMISE (Davidson–Szarek 2001, Theorem II.13, via paper
Section 4): non-asymptotic covariance concentration in operator norm.
`‖Σ̂ - I‖_op ≤ 4√(d/n) + 4d/n` except with probability `2e^{-d/2}`. -/
def davidsonSzarekCovariance : Prop :=
  ∀ d n : Nat, 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
    ((gaussianSampleLaw d n)
      {x | 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
        < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2)

/-- EXTERNAL PREMISE (paper Section 4, "ridge gives uniqueness and
measurability"; standard unique-minimizer continuity / Berge): deleted
selectors can be chosen measurably and locally (depending only on the
observations other than the held-out one). -/
def deletedSelectorMeasurable : Prop :=
  ∀ (d n : Nat) (lo hi : Real), 0 < lo → lo ≤ hi →
    ∀ j : Fin n, ∃ Sdel : Sample d n → Square d,
      Measurable Sdel
      ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x))
      ∧ ∀ x y : Sample d n, (∀ i, i ≠ j → x i = y i) →
        Sdel x = Sdel y

/-- EXTERNAL PREMISE (Rudelson–Vershynin 2013, Theorem 1.1, via paper
Section 4): uniform Hanson–Wright tail for the centered chaos over the
spectral box, for measurable local selectors. -/
def hansonWrightChaos : Prop :=
  ∀ (lo hi : Real), 0 < lo → lo ≤ hi →
    ∃ cHW : Real, 0 < cHW ∧ ∀ (d n : Nat) (j : Fin n)
      (Sdel : Sample d n → Square d),
      Measurable Sdel →
      (∀ x, Sdel x ∈ spectralBox d lo hi) →
      (∀ x y : Sample d n, (∀ i, i ≠ j → x i = y i) →
        Sdel x = Sdel y) →
      ∀ t : Real, 0 ≤ t →
        ((gaussianSampleLaw d n)
          {x | t < |((quadratic (Sdel x) (x j) - (Sdel x).trace)
            / Real.sqrt (d : ℝ))|}).toReal
          ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ)))

/-! ### Mixed norm, dual majorant, quotient residual -/

/-- The paper's mixed norm `N_η(y) = inf_{y=u+v} [η√d ‖u‖₁ + d ‖v‖₂]`. -/
def mixedNorm (η : Real) (d n : Nat) (y : Vector n) : Real :=
  sInf {w : Real | ∃ u v : Vector n,
    y = u + v ∧ w = η * Real.sqrt d * l1Size u + d * euclidNorm v}

/-- The dual majorant `N*_η(e) = max{‖e‖_∞/(η√d), ‖e‖₂/d}`. The paper's
Section 12 formula; only the Hölder direction is needed. -/
def dualMixed (η : Real) (d n : Nat) (e : Vector n) : Real :=
  max (‖e‖ / (η * Real.sqrt d)) (euclidNorm e / d)

/-- The quotient residual `κ_d(S) = inf{‖H‖_op : T_d(H) = -Π₀r(S)}` over
symmetric corrections (the paper's infimum is over `Sym_d`). -/
def kappa (d n : Nat) (x : Sample d n) (S : Square d) : Real :=
  sInf {r : Real | ∃ H : Square d,
    H.IsSymm ∧ measurementT x H = -center (residual x S) ∧
      matrixOpNorm H = r}

/-- The rank-one independence event: the matrices `x_i x_i^T` are linearly
independent. The paper's Section 12 rank event. -/
def rankOneIndependent {d n : Nat} (x : Sample d n) : Prop :=
  LinearIndependent ℝ (fun i : Fin n => Matrix.vecMulVec (x i) (x i))

/-! ### Section-level interface propositions -/

/-- Section 11 body (main-theorem-7-1): parameters plus the good event with
its probability bound and the mixed-norm lower bound on the adjoint. -/
def MixedNormBody (n : Nat → Nat) (δ η c : Real)
    (G : Π d, Set (Sample d (n d))) : Prop :=
  0 < η ∧ η < 1 ∧ 0 < c ∧
  Filter.limsup (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal)
      Filter.atTop ≤ δ ∧
  ∀ d, ∀ x ∈ G d, ∀ y : Vector (n d), (∑ i, y i) = 0 →
    c * mixedNorm η d (n d) y ≤ nuclearNorm (centeredAdjoint x y)

/-- Section 11 (main-theorem-7-1): below the threshold, good events with
the mixed-norm lower bound exist at every tolerance. -/
def MixedNormBound : Prop :=
  ∀ n : Nat → Nat, (∀ d, 0 < n d) →
    Filter.limsup (dimensionRatio n) Filter.atTop < (1 / 4 : ENNReal) →
    ∀ δ > 0, ∃ η c : Real, ∃ G : Π d, Set (Sample d (n d)),
      MixedNormBody n δ η c G

/-- Section 12 quotient consequence: on the good event the quotient
residual is controlled by the dual mixed norm of the centered residuals. -/
def QuotientBody (n : Nat → Nat) (η c : Real)
    (G : Π d, Set (Sample d (n d)))
    (Sstar : Π d, Sample d (n d) → Square d) : Prop :=
  ∀ d, ∀ x ∈ G d, kappa d (n d) x (Sstar d x)
    ≤ c⁻¹ * dualMixed η d (n d) (center (residual x (Sstar d x)))

/-- Section 12 bridge (B2): the mixed-norm bound implies the quotient
bound, via finite-dimensional quotient duality. Discharged from
`QuotientDuality` plus the nuclear/operator duality bridge. -/
def QuotientBridge : Prop :=
  ∀ (n : Nat → Nat) (δ η c : Real) (G : Π d, Set (Sample d (n d)))
    (Sstar : Π d, Sample d (n d) → Square d),
    MixedNormBody n δ η c G → QuotientBody n η c G Sstar

/- Note: no attainment hypothesis is needed for `κ_d`. The fiber is
always nonempty (`H = -S` works by linearity) and `sInf` approximation
(`exists_lt_of_csInf_lt`) supplies almost-minimizers with
`‖H‖_op < λ₋/2`; positive definiteness only needs a strict bound. -/

/-- Section 4 conclusion (main-proposition-3-1) in dual-norm form: for a
convergent aspect ratio below `1/4`, the dual mixed norm of every Huber
minimizer's centered residuals tends to zero in probability. -/
def HuberResiduals : Prop :=
  ∀ (n : Nat → Nat) (α₀ : Real), (∀ d, 0 < n d) →
    Filter.Tendsto (fun d => ((n d : Real) / (d : Real) ^ 2))
      Filter.atTop (nhds α₀) →
    0 < α₀ → α₀ < 1 / 4 →
    ∀ lo hi : Real, 0 < lo → lo ≤ hi → BMminRisk n lo hi →
    ∀ Sstar : Π d, Sample d (n d) → Square d,
      (∀ d x, IsHuberMinimizer lo hi x (Sstar d x)) →
      ∀ η > 0, ∀ ε > 0,
        Filter.Tendsto (fun d => ((gaussianSampleLaw d (n d))
          {x | ε < dualMixed η d (n d)
            (center (residual x (Sstar d x)))}).toReal)
          Filter.atTop (nhds 0)

/-! ### Elementary analytic bridges (proved) -/

/-- Hölder estimate for the mixed norm: `|⟨e,y⟩| ≤ N*_η(e) N_η(y)`.
This is the direction of the Section 12 dual formula that the assembly
uses; no equality is needed. -/
theorem mixedNorm_holder {d n : Nat} {η : Real} {e y : Vector n}
    (hη : 0 < η) (hd : 0 < d) :
    |∑ i, e i * y i| ≤ dualMixed η d n e * mixedNorm η d n y := by
  set M : Real := dualMixed η d n e with hMdef
  have hdR : (0 : Real) < d := Nat.cast_pos.mpr hd
  have hsqpos : 0 < Real.sqrt (d : Real) := Real.sqrt_pos.mpr hdR
  have hηsq : 0 < η * Real.sqrt (d : Real) := mul_pos hη hsqpos
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    unfold dualMixed
    apply le_max_iff.mpr
    left
    apply div_nonneg (norm_nonneg _) (le_of_lt hηsq)
  have hcoord : ∀ i : Fin n, |e i| ≤ ‖e‖ := by
    intro i
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm e i
  have hl1 : ∀ u : Vector n, |∑ i, e i * u i| ≤ ‖e‖ * l1Size u := by
    intro u
    calc |∑ i, e i * u i| ≤ ∑ i, |e i * u i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, (|e i| * |u i|) := by
            apply Finset.sum_congr rfl
            intro i _
            exact abs_mul _ _
      _ ≤ ∑ i, (‖e‖ * |u i|) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg _)
      _ = ‖e‖ * l1Size u := by
            unfold l1Size
            rw [← Finset.mul_sum]
  have hl2 : ∀ v : Vector n,
      |∑ i, e i * v i| ≤ euclidNorm e * euclidNorm v := by
    intro v
    exact dotProduct_abs_le_euclidNorm e v
  have hsup : ‖e‖ ≤ M * (η * Real.sqrt d) := by
    have h : ‖e‖ / (η * Real.sqrt d) ≤ M := by
      rw [hMdef]
      unfold dualMixed
      exact le_max_left _ _
    rwa [div_le_iff₀ hηsq] at h
  have hl2b : euclidNorm e ≤ M * d := by
    have h : euclidNorm e / (d : Real) ≤ M := by
      rw [hMdef]
      unfold dualMixed
      exact le_max_right _ _
    rwa [div_le_iff₀ hdR] at h
  have hl1nn : ∀ u : Vector n, 0 ≤ l1Size u := by
    intro u
    unfold l1Size
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hdecomp : ∀ u v : Vector n, y = u + v →
      |∑ i, e i * y i|
        ≤ M * (η * Real.sqrt d * l1Size u + d * euclidNorm v) := by
    intro u v hyv
    have hsplit : ∀ i : Fin n, e i * y i = e i * u i + e i * v i := by
      intro i
      rw [hyv]
      simp [Pi.add_apply, mul_add]
    calc |∑ i, e i * y i|
        = |∑ i, (e i * u i + e i * v i)| := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            exact hsplit i
      _ = |(∑ i, e i * u i) + (∑ i, e i * v i)| := by
            rw [Finset.sum_add_distrib]
      _ ≤ |∑ i, e i * u i| + |∑ i, e i * v i| := abs_add_le _ _
      _ ≤ (M * (η * Real.sqrt d * l1Size u)) + (M * (d * euclidNorm v)) := by
            apply add_le_add
            · calc |∑ i, e i * u i| ≤ ‖e‖ * l1Size u := hl1 u
                _ ≤ (M * (η * Real.sqrt d)) * l1Size u :=
                    mul_le_mul_of_nonneg_right hsup (hl1nn u)
                _ = M * (η * Real.sqrt d * l1Size u) := by ring
            · calc |∑ i, e i * v i| ≤ euclidNorm e * euclidNorm v := hl2 v
                _ ≤ (M * d) * euclidNorm v :=
                    mul_le_mul_of_nonneg_right hl2b (euclidNorm_nonneg v)
                _ = M * (d * euclidNorm v) := by ring
      _ = M * (η * Real.sqrt d * l1Size u + d * euclidNorm v) := by ring
  have hne : {w : Real | ∃ u v : Vector n,
      y = u + v ∧ w = η * Real.sqrt d * l1Size u + d * euclidNorm v}.Nonempty := by
    refine ⟨η * Real.sqrt d * l1Size y + d * euclidNorm 0, y, 0, ?_, rfl⟩
    simp
  have hne2 := hne
  obtain ⟨w0, u0, v0, hyv0, hw0⟩ := hne
  by_cases hM0 : M = 0
  · have h0 : |∑ i, e i * y i| ≤ 0 := by
      have h := hdecomp u0 v0 hyv0
      rw [← hw0, hM0, zero_mul] at h
      exact h
    rw [hM0, zero_mul]
    exact h0
  · have hMpos : 0 < M := lt_of_le_of_ne' hMnn hM0
    have hdiv : ∀ m ∈ {w : Real | ∃ u v : Vector n,
        y = u + v ∧ w = η * Real.sqrt d * l1Size u + d * euclidNorm v},
        |∑ i, e i * y i| / M ≤ m := by
      rintro m ⟨u, v, hyv, rfl⟩
      rw [div_le_iff₀ hMpos, mul_comm _ M]
      exact hdecomp u v hyv
    have hinf : |∑ i, e i * y i| / M ≤ mixedNorm η d n y := by
      unfold mixedNorm
      exact le_csInf hne2 hdiv
    rw [div_le_iff₀ hMpos] at hinf
    calc |∑ i, e i * y i| ≤ mixedNorm η d n y * M := hinf
      _ = M * mixedNorm η d n y := mul_comm _ _

/-- The centered measurements coincide with the centered residuals:
`T_d(S) = Π₀ r(S)`. Needs `0 < d` and `0 < n` to clear denominators. -/
theorem measurementT_eq_center_residual {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    (x : Sample d n) (S : Square d) :
    measurementT x S = center (residual x S) := by
  have hnR : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hsq : Real.sqrt (d : Real) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
  have hsum : (∑ j, (quadratic S (x j) - (d : Real)) / Real.sqrt (d : Real))
      = ((∑ j, quadratic S (x j)) - n * d) / Real.sqrt (d : Real) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    congr 1
    have hcard : (∑ _j : Fin n, (d : Real)) = (n : Real) * d := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hcard]
  funext i
  unfold measurementT center residual mean measurementA
  rw [hsum]
  field_simp
  ring

open MeasureTheory ProbabilityTheory Finset

/-! ### Verified assembly helpers -/

/-- The all-zero sample is null (Gaussian atomlessness, via one row and
one coordinate). Supplies the nonzero-observation witness on good events. -/
theorem sample_allZero_null {d n : Nat} (hd : 0 < d) (hn : 0 < n) :
    gaussianSampleLaw d n {x : Sample d n | ∀ i, x i = 0} = 0 := by
  have j : Fin n := ⟨0, hn⟩
  have k : Fin d := ⟨0, hd⟩
  have hsub : {x : Sample d n | ∀ i, x i = 0}
      ⊆ (fun x : Sample d n => x j) ⁻¹' {(0 : Vector d)} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hx j
  have hvec : gaussianVectorLaw d {(0 : Vector d)} = 0 := by
    have hsub2 : {(0 : Vector d)}
        ⊆ (fun v : Vector d => v k) ⁻¹' {(0 : ℝ)} := by
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst hv
      simp
    have hmap2 := gaussianCoordinate_map (d := d) k
    have hle : gaussianVectorLaw d {(0 : Vector d)} ≤ 0 := by
      calc gaussianVectorLaw d {(0 : Vector d)}
          ≤ gaussianVectorLaw d ((fun v : Vector d => v k) ⁻¹' {(0 : ℝ)}) :=
            measure_mono hsub2
        _ = gaussianReal 0 1 {(0 : ℝ)} := by
            have hmeas : Measurable (fun v : Vector d => v k) :=
              measurable_pi_apply k
            rw [← hmap2]
            exact (Measure.map_apply hmeas (measurableSet_singleton 0)).symm
        _ = 0 := gaussianReal_singleton_null 0
    exact le_antisymm hle zero_le
  have hle : gaussianSampleLaw d n {x : Sample d n | ∀ i, x i = 0} ≤ 0 := by
    calc gaussianSampleLaw d n {x : Sample d n | ∀ i, x i = 0}
        ≤ gaussianSampleLaw d n
            ((fun x : Sample d n => x j) ⁻¹' {(0 : Vector d)}) :=
          measure_mono hsub
      _ = gaussianVectorLaw d {(0 : Vector d)} := by
          have hmeas : Measurable (fun x : Sample d n => x j) :=
            measurable_pi_apply j
          rw [← gaussianRow_map (d := d) (n := n) j]
          exact (Measure.map_apply hmeas (measurableSet_singleton 0)).symm
      _ = 0 := hvec
  exact le_antisymm hle zero_le

/-- Bridge between the `ENNReal` dimension ratio and the real aspect ratio. -/
theorem dimensionRatio_lt_ofReal {n' : Nat → Nat} {β : ℝ} {d : Nat}
    (hd : 1 ≤ d) (hβ : 0 < β) :
    dimensionRatio n' d < ENNReal.ofReal β
      ↔ ((n' d : ℝ) / (d : ℝ) ^ 2) < β := by
  unfold dimensionRatio
  have hdN : d ≠ 0 := by omega
  have hdsq0 : ((d : ENNReal) ^ 2) ≠ 0 := by
    rw [← Nat.cast_pow]
    exact_mod_cast pow_ne_zero 2 hdN
  have hdsqT : ((d : ENNReal) ^ 2) ≠ ⊤ := by
    rw [← Nat.cast_pow]
    exact ENNReal.natCast_ne_top _
  rw [ENNReal.div_lt_iff (Or.inl hdsq0) (Or.inl hdsqT)]
  have hcast : ((n' d : Nat) : ENNReal) = ENNReal.ofReal (n' d : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have hdsq : ((d : ENNReal) ^ 2) = ENNReal.ofReal ((d : ℝ) ^ 2) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    exact (ENNReal.ofReal_natCast _).symm
  rw [hcast, hdsq, ← ENNReal.ofReal_mul (le_of_lt hβ)]
  have hpos : 0 < β * (d : ℝ) ^ 2 := by
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega : 0 < d)
    exact mul_pos hβ (pow_pos hd0 2)
  rw [ENNReal.ofReal_lt_ofReal_iff hpos]
  have hdsqR : (0 : ℝ) < (d : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
  rw [div_lt_iff₀ hdsqR]

/-- A limsup bound from an eventual pointwise bound. -/
theorem limsup_le_of_eventually_le' {u : Nat → ENNReal} {β : ENNReal}
    (h : ∀ᶠ d in Filter.atTop, u d ≤ β) : Filter.limsup u Filter.atTop ≤ β := by
  rw [Filter.limsup_eq]
  refine csInf_le (OrderBot.bddBelow _) ?_
  exact h

/-- `sInf` approximation: below every strict upper bound lies a set element. -/
theorem exists_lt_of_csInf_lt {s : Set ℝ} {a : ℝ} (hne : s.Nonempty)
    (h : sInf s < a) : ∃ b ∈ s, b < a := by
  by_contra hall
  push Not at hall
  have hall' : ∀ b ∈ s, a ≤ b := fun b hb => hall b hb
  have hle : a ≤ sInf s := le_csInf hne hall'
  exact (not_le_of_gt h) hle

/-- Finiteness of a fitting probability: every sample-law value is below `⊤`. -/
theorem sampleLaw_ne_top {d n : Nat} (s : Set (Sample d n)) :
    gaussianSampleLaw d n s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

/-- `(1/4 : ENNReal)` is `ofReal (1/4 : ℝ)`. -/
theorem ennreal_quarter_eq_ofReal : (1 / 4 : ENNReal)
    = ENNReal.ofReal (1 / 4 : ℝ) := by
  have h4 : (4 : ℝ) = ((4 : Nat) : ℝ) := by norm_cast
  rw [h4]
  have hdiv : (1 / 4 : ENNReal) = (1 : ENNReal) / ((4 : Nat) : ENNReal) := by
    norm_cast
  rw [hdiv]
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < ((4 : Nat) : ℝ))]
  norm_cast

/-- Positive definiteness of `S + H` from a PSD shift and a small symmetric
correction. The Section 12 exactification step `Q_d ⪰ (λ₋/2) I`. -/
theorem posDef_add_of_opNorm_lt {d : Nat} {S H : Square d} {lo : ℝ}
    (hS : (S - lo • (1 : Square d)).PosSemidef)
    (hH : H.IsSymm) (hlt : matrixOpNorm H < lo / 2) (hlo : 0 < lo) :
    (S + H).PosDef := by
  have hSsym : S.IsSymm := by
    have hsub : (S - lo • (1 : Square d)).IsSymm :=
      ((posSemidef_iff_coordinates _).mp hS).1
    have h1 : (lo • (1 : Square d)).IsSymm := Matrix.isSymm_one.smul lo
    have hadd := hsub.add h1
    rwa [sub_add_cancel] at hadd
  have hSH : (S + H).IsSymm := hSsym.add hH
  apply (posDef_iff_coordinates (S + H)).mpr
  refine And.intro hSH ?_
  intro v hv
  have : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  have hnorm : 0 < dotProduct v v := by
    simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hv)
  have hSlow : lo * dotProduct v v ≤ quadratic S v := by
    have hSeq : S = (S - lo • (1 : Square d)) + lo • (1 : Square d) :=
      (sub_add_cancel _ _).symm
    have hnn := quadratic_nonneg hS v
    rw [hSeq, quadratic_add, quadratic_smul, quadratic_one]
    linarith
  have hsq : (euclidNorm v) ^ 2 = dotProduct v v := by
    rw [euclidNorm_sq]
    simp [dotProduct, pow_two]
  have hHerr : |quadratic H v| ≤ matrixOpNorm H * dotProduct v v := by
    rw [← hsq]
    exact quadratic_abs_le_opNorm_mul_sq H v
  have hgap : matrixOpNorm H < lo := by linarith
  have herr := (abs_le.mp hHerr).1
  rw [quadratic_add]
  nlinarith [mul_pos (sub_pos.mpr hgap) hnorm]

/-- Every mixed-norm decomposition weight is nonnegative for `η ≥ 0`. -/
private theorem mixedElem_nonneg {η : ℝ} {d n : Nat} (hη : 0 ≤ η)
    (u v : Vector n) :
    0 ≤ η * Real.sqrt (d : ℝ) * l1Size u + (d : ℝ) * euclidNorm v := by
  have hl1 : 0 ≤ l1Size u :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have h1 : 0 ≤ η * Real.sqrt (d : ℝ) * l1Size u :=
    mul_nonneg (mul_nonneg hη (Real.sqrt_nonneg _)) hl1
  have h2 : 0 ≤ (d : ℝ) * euclidNorm v :=
    mul_nonneg (Nat.cast_nonneg _) (euclidNorm_nonneg v)
  linarith

/-- The mixed norm is nonnegative for `η ≥ 0`. -/
theorem mixedNorm_nonneg {η : ℝ} {d n : Nat} (hη : 0 ≤ η) (y : Vector n) :
    0 ≤ mixedNorm η d n y := by
  unfold mixedNorm
  refine le_csInf ?_ ?_
  · exact ⟨η * Real.sqrt (d : ℝ) * l1Size y + (d : ℝ) * euclidNorm 0,
      y, 0, by simp, rfl⟩
  · rintro w ⟨u, v, _, rfl⟩
    exact mixedElem_nonneg hη u v

/-- The mixed norm of zero vanishes (for `η ≥ 0`). -/
theorem mixedNorm_zero {η : ℝ} {d n : Nat} (hη : 0 ≤ η) :
    mixedNorm η d n 0 = 0 := by
  apply le_antisymm
  · unfold mixedNorm
    apply csInf_le _ _
    · refine ⟨0, ?_⟩
      rintro w ⟨u, v, _, rfl⟩
      exact mixedElem_nonneg hη u v
    · refine ⟨0, 0, by simp, ?_⟩
      have hl1 : l1Size (0 : Vector n) = 0 := by simp [l1Size]
      have he : euclidNorm (0 : Vector n) = 0 := by simp [euclidNorm]
      simp [hl1, he]
  · exact mixedNorm_nonneg hη 0

end GaussianEllipsoid
