module

/-
# The one-coordinate inequality (HI-ONESTEP, HI-BASE)

Paper Section 6: volume formulation `S_d(ν) ≤ (d+1)/(2d) D_d(ν) S_{d-1}(μ)`
for finitely supported `ν`. The bridge: product measures of atomic laws are
atomic on tuples (`pi_atomMeas`, `prod_atomMeas`), so `S`/`gap` of atomic laws
are finite weighted sums, to which the determinant bounds apply.
-/

public import Mathlib
public import Section_5_Layercake.Layercake

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

-- Local instances for sigma-finiteness are essential below (`pi_eq`, `prod_eq`
-- need them); the `haveI`-for-`have` style lint does not apply.
set_option linter.style.haveILetI false

section Atomic

variable {K d N : ℕ} (c : Fin N → ℝ≥0∞)
  (Z : Fin N → EuclideanSpace ℝ (Fin d))

/-- Finite atomic measure. -/
@[expose] public noncomputable def atomMeas : Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ i, c i • Measure.dirac (Z i)

/-- Atomic tuple measure. -/
@[expose] public noncomputable def atomTupleMeas :
    Measure (Fin K → EuclideanSpace ℝ (Fin d)) :=
  ∑ F : Fin K → Fin N, (∏ r, c (F r)) • Measure.dirac (fun r => Z (F r))

/-- Atomic pair measure. -/
@[expose] public noncomputable def atomPairMeas :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ∑ j, ((c i * c j) • Measure.dirac (Z i, Z j))

/-- Atomic measures are sigma-finite (weights finite). -/
public theorem sigmaFinite_atomMeas (hc : ∀ i, c i ≠ ∞) :
    SigmaFinite (atomMeas c Z) := by
  have hterm : ∀ i, SigmaFinite (c i • Measure.dirac (Z i)) := by
    intro i
    have hfin : IsFiniteMeasure (c i • Measure.dirac (Z i)) := ⟨by
      have hdirac : Measure.dirac (Z i) (Set.univ) = 1 :=
        Measure.dirac_apply_of_mem (Set.mem_univ _)
      rw [Measure.smul_apply, hdirac, smul_eq_mul, mul_one]
      exact lt_top_iff_ne_top.mpr (hc i)⟩
    exact IsFiniteMeasure.toSigmaFinite _
  have hall : ∀ s : Finset (Fin N),
      SigmaFinite (∑ i ∈ s, c i • Measure.dirac (Z i)) := by
    intro s
    induction s using Finset.induction
    case empty =>
      simp only [Finset.sum_empty]
      infer_instance
    case insert a s ha ih =>
      rw [Finset.sum_insert ha]
      infer_instance
  have h := hall Finset.univ
  simpa [atomMeas] using h

/-- Product measures of atomic laws are atomic on tuples. -/
public theorem pi_atomMeas (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun _ : Fin K => atomMeas c Z) = atomTupleMeas (K := K) c Z := by
  haveI := sigmaFinite_atomMeas c Z hc
  classical
  apply pi_eq
  intro s hs
  simp only [atomTupleMeas, atomMeas, Measure.finsetSum_apply,
    Measure.smul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : ∀ r, Z (F r) ∈ s r
  · have hmem : (fun r => Z (F r)) ∈ Set.pi Set.univ s := by
      rw [Set.mem_pi]
      intro r _
      exact hF r
    have hL : (∏ r, c (F r))
          • Measure.dirac (fun r => Z (F r)) (Set.pi Set.univ s)
        = ∏ r, c (F r) := by
      rw [Measure.dirac_apply, Set.indicator_of_mem hmem, Pi.one_apply,
        smul_eq_mul, mul_one]
    have hR : (∏ r, c (F r) • Measure.dirac (Z (F r)) (s r))
        = ∏ r, c (F r) := by
      apply Finset.prod_congr rfl
      intro r _
      rw [Measure.dirac_apply, Set.indicator_of_mem (hF r), Pi.one_apply,
        smul_eq_mul, mul_one]
    rw [hL, hR]
  · obtain ⟨r, hr⟩ := not_forall.mp hF
    have hmem : (fun r => Z (F r)) ∉ Set.pi Set.univ s := by
      intro h
      rw [Set.mem_pi] at h
      exact hr (h r (Set.mem_univ r))
    have hL : (∏ r, c (F r))
          • Measure.dirac (fun r => Z (F r)) (Set.pi Set.univ s) = 0 := by
      rw [Measure.dirac_apply, Set.indicator_of_notMem hmem, smul_zero]
    have hRf : c (F r) • Measure.dirac (Z (F r)) (s r) = 0 := by
      rw [Measure.dirac_apply, Set.indicator_of_notMem hr, smul_zero]
    have hR0 : (∏ r, c (F r) • Measure.dirac (Z (F r)) (s r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) hRf
    rw [hL, hR0]

/-- Lintegrals over atomic tuple measures are weighted sums. -/
public theorem lintegral_atomTupleMeas
    (G : (Fin K → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞) :
    (∫⁻ W, G W ∂(atomTupleMeas (K := K) c Z))
    = ∑ F : Fin K → Fin N, (∏ r, c (F r)) • G (fun r => Z (F r)) := by
  have hall : ∀ s : Finset (Fin K → Fin N),
      (∫⁻ W, G W ∂(∑ F ∈ s, (∏ r, c (F r))
        • Measure.dirac (fun r => Z (F r))))
      = ∑ F ∈ s, (∏ r, c (F r)) • G (fun r => Z (F r)) := by
    intro s
    induction s using Finset.induction
    case empty =>
      simp only [Finset.sum_empty]
      simp
    case insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lintegral_add_measure,
        lintegral_smul_measure, lintegral_dirac, ih]
  simpa only [atomTupleMeas] using hall Finset.univ

/-- `S_d` of an atomic law is a weighted sum of simplex volumes. -/
public theorem S_atomMeas (hc : ∀ i, c i ≠ ∞) :
    S d (atomMeas c Z)
    = ∑ F : Fin (d + 1) → Fin N,
      (∏ r, c (F r))
        • volume (convexHull ℝ (Set.range (fun r => Z (F r)))) := by
  haveI := sigmaFinite_atomMeas c Z hc
  simp only [S]
  rw [pi_atomMeas c Z hc]
  exact lintegral_atomTupleMeas c Z _

/-- Products of atomic laws are atomic on pairs. -/
public theorem prod_atomMeas (hc : ∀ i, c i ≠ ∞) :
    (atomMeas c Z).prod (atomMeas c Z) = atomPairMeas c Z := by
  haveI := sigmaFinite_atomMeas c Z hc
  classical
  apply prod_eq
  intro s t hs ht
  simp only [atomPairMeas, atomMeas, Measure.finsetSum_apply,
    Measure.smul_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : Z i ∈ s <;> by_cases hj : Z j ∈ t
  · have hmem : (Z i, Z j) ∈ s ×ˢ t := ⟨hi, hj⟩
    simp only [Measure.dirac_apply, Set.indicator_of_mem hmem,
      Set.indicator_of_mem hi, Set.indicator_of_mem hj, Pi.one_apply,
      smul_eq_mul]
    ring
  · have hmem : (Z i, Z j) ∉ s ×ˢ t := fun h => hj h.2
    simp only [Measure.dirac_apply, Set.indicator_of_notMem hmem,
      Set.indicator_of_mem hi, Set.indicator_of_notMem hj, Pi.one_apply,
      smul_eq_mul]
    ring
  · have hmem : (Z i, Z j) ∉ s ×ˢ t := fun h => hi h.1
    simp only [Measure.dirac_apply, Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem hi, Set.indicator_of_mem hj, Pi.one_apply,
      smul_eq_mul]
    ring
  · have hmem : (Z i, Z j) ∉ s ×ˢ t := fun h => hi h.1
    simp only [Measure.dirac_apply, Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem hi, Set.indicator_of_notMem hj, smul_eq_mul]
    ring

/-- `D_j` of an atomic law is a pairwise sum. -/
public theorem gap_atomMeas (j : Fin d) (hc : ∀ i, c i ≠ ∞) :
    gap j (atomMeas c Z)
    = ∑ i, ∑ j', (c i * c j') • (‖Z i j - Z j' j‖₊ : ℝ≥0∞) := by
  haveI := sigmaFinite_atomMeas c Z hc
  classical
  have hinner : ∀ t : Finset (Fin N), ∀ i : Fin N,
      (∫⁻ p, (‖p.1 j - p.2 j‖₊ : ℝ≥0∞)
        ∂(∑ j' ∈ t, ((c i * c j') • Measure.dirac (Z i, Z j'))))
      = ∑ j' ∈ t, (c i * c j') • (‖Z i j - Z j' j‖₊ : ℝ≥0∞) := by
    intro t i
    induction t using Finset.induction
    case empty =>
      simp only [Finset.sum_empty]
      simp
    case insert b t hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, lintegral_add_measure,
        lintegral_smul_measure, lintegral_dirac, ih]
  have hall : ∀ s : Finset (Fin N),
      (∫⁻ p, (‖p.1 j - p.2 j‖₊ : ℝ≥0∞)
        ∂(∑ i ∈ s, ∑ j' ∈ Finset.univ,
          ((c i * c j') • Measure.dirac (Z i, Z j'))))
      = ∑ i ∈ s, ∑ j' ∈ Finset.univ,
        (c i * c j') • (‖Z i j - Z j' j‖₊ : ℝ≥0∞) := by
    intro s
    induction s using Finset.induction
    case empty =>
      simp only [Finset.sum_empty]
      simp
    case insert a s ha ih =>
      have h1 := hinner Finset.univ a
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lintegral_add_measure,
        h1, ih]
  simp only [gap]
  rw [prod_atomMeas c Z hc]
  simpa only [atomPairMeas] using hall Finset.univ

end Atomic

section Bridge

variable {m N : ℕ} (p : Fin N → ℝ)
  (Z : Fin N → EuclideanSpace ℝ (Fin (m + 1)))

/-- Projected atoms (first `m` coordinates). -/
@[expose] public noncomputable def Yatom (i : Fin N) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun t : Fin m => Z i t.castSucc)

/-- Heights (last coordinate). -/
@[expose] public noncomputable def Hatom (i : Fin N) : ℝ :=
  Z i (Fin.last m)

public theorem Yatom_apply (i : Fin N) (t : Fin m) :
    Yatom Z i t = Z i t.castSucc := rfl

/-- Ordered `A` expansion along the height column. -/
public theorem det_ordMatA_eq_sum (F : Fin (m + 2) → Fin N) :
    Matrix.det (ordMatA (Yatom Z) (Hatom Z) F)
    = ∑ r : Fin (m + 2), (-1 : ℝ) ^ (r : ℕ)
      * Hatom Z (F r)
      * Matrix.det (ordMatD (Yatom Z) (F ∘ r.succAbove)) := by
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro r _
  have h00 : ordMatA (Yatom Z) (Hatom Z) F r 0 = Hatom Z (F r) := by
    simp only [ordMatA, Matrix.of_apply, Fin.cases_zero]
  have hminor : (ordMatA (Yatom Z) (Hatom Z) F).submatrix r.succAbove Fin.succ
      = ordMatD (Yatom Z) (F ∘ r.succAbove) := by
    ext a b
    simp only [ordMatA, ordMatD, Matrix.of_apply, Matrix.submatrix_apply,
      Function.comp_apply, Fin.cases_succ]
  rw [h00, hminor]

/-- `simDet` expansion along the last (height) column. -/
public theorem simDet_eq_ordered_sum (F : Fin (m + 2) → Fin N) :
    simDet (fun r => Z (F r))
    = ∑ r : Fin (m + 2), (-1 : ℝ) ^ ((r : ℕ) + (m + 1))
      * Hatom Z (F r)
      * Matrix.det (ordMatD (Yatom Z) (F ∘ r.succAbove)) := by
  have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
  have hentry : ∀ r : Fin (m + 2),
      (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Z (F r) j) c)) r
        (Fin.last (m + 1)) = Hatom Z (F r) := by
    intro r
    rw [Matrix.of_apply, hlast, Fin.cases_succ]
    rfl
  have hminor : ∀ r : Fin (m + 2),
      (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Z (F r) j) c)).submatrix
        r.succAbove (Fin.last (m + 1)).succAbove
      = ordMatD (Yatom Z) (F ∘ r.succAbove) := by
    intro r
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Function.comp_apply,
      ordMatD, Fin.succAbove_last]
    refine Fin.cases ?hz ?hs b
    · simp only [Fin.castSucc_zero, Fin.cases_zero]
    · intro t
      simp only [Fin.castSucc_succ, Fin.cases_succ, Yatom_apply]
  simp only [simDet]
  rw [Matrix.det_succ_column _ (Fin.last (m + 1))]
  apply Finset.sum_congr rfl
  intro r _
  rw [hentry r, hminor r, Fin.val_last]

/-- `|A|` agrees with `|simDet|` (column-order sign drops out). -/
public theorem abs_ordMatA_eq_abs_simDet (F : Fin (m + 2) → Fin N) :
    |Matrix.det (ordMatA (Yatom Z) (Hatom Z) F)|
    = |simDet (fun r => Z (F r))| := by
  have hA := det_ordMatA_eq_sum Z F
  have hS := simDet_eq_ordered_sum Z F
  have hfactor : simDet (fun r => Z (F r))
      = (-1 : ℝ) ^ (m + 1)
        * Matrix.det (ordMatA (Yatom Z) (Hatom Z) F) := by
    rw [hS, hA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_add]
    ring
  rw [hfactor, abs_mul]
  have hsign : |(-1 : ℝ) ^ (m + 1)| = 1 := by
    rw [abs_pow]
    simp
  rw [hsign, one_mul]

/-- `|A|` in `ofReal` volume form. -/
public theorem ofReal_abs_AT (F : Fin (m + 2) → Fin N) :
    ENNReal.ofReal |Matrix.det (ordMatA (Yatom Z) (Hatom Z) F)|
    = ((m + 1)! : ℝ≥0∞)
      * volume (convexHull ℝ (Set.range (fun r => Z (F r)))) := by
  rw [abs_ordMatA_eq_abs_simDet]
  exact abs_simDet_eq_volume_convexHull (fun r => Z (F r))

/-- `|D|` in `ofReal` volume form. -/
public theorem ofReal_abs_ordMatD (G : Fin (m + 1) → Fin N) :
    ENNReal.ofReal |Matrix.det (ordMatD (Yatom Z) G)|
    = ((m)! : ℝ≥0∞)
      * volume
        (convexHull ℝ (Set.range (fun s => Yatom Z (G s)))) := by
  have hsim : simDet (fun s => Yatom Z (G s))
      = Matrix.det (ordMatD (Yatom Z) G) := rfl
  rw [← hsim]
  exact abs_simDet_eq_volume_convexHull (fun s => Yatom Z (G s))

end Bridge

section OneStep

variable {m N : ℕ} (p : Fin N → ℝ)
  (Z : Fin N → EuclideanSpace ℝ (Fin (m + 1)))

/-- Atom weights as extended nonnegative reals. -/
@[expose] public noncomputable def wgt (i : Fin N) : ℝ≥0∞ :=
  ENNReal.ofReal (p i)

public theorem wgt_ne_top (i : Fin N) : wgt p i ≠ ∞ :=
  ENNReal.ofReal_ne_top

public theorem nonneg_ordWeight (hpos : ∀ i, 0 < p i)
    (F : Fin (m + 2) → Fin N) : 0 ≤ ordWeight p F := by
  simp only [ordWeight]
  exact Finset.prod_nonneg (fun r _ => le_of_lt (hpos (F r)))

public theorem nonneg_ordWeightD (hpos : ∀ i, 0 < p i)
    (G : Fin (m + 1) → Fin N) : 0 ≤ ordWeightD p G := by
  simp only [ordWeightD]
  exact Finset.prod_nonneg (fun s _ => le_of_lt (hpos (G s)))

public theorem nonneg_ordTermA (hpos : ∀ i, 0 < p i)
    (F : Fin (m + 2) → Fin N) :
    0 ≤ ordTermA p (Yatom Z) (Hatom Z) F := by
  simp only [ordTermA]
  exact mul_nonneg (nonneg_ordWeight p hpos F) (abs_nonneg _)

public theorem nonneg_ordTermD (hpos : ∀ i, 0 < p i)
    (G : Fin (m + 1) → Fin N) :
    0 ≤ ordTermD p (Yatom Z) G := by
  simp only [ordTermD]
  exact mul_nonneg (nonneg_ordWeightD p hpos G) (abs_nonneg _)

public theorem nonneg_gapPair (hpos : ∀ i, 0 < p i) :
    0 ≤ gapPair p (Hatom Z) := by
  have hp : ∀ i, 0 ≤ p i := fun i => le_of_lt (hpos i)
  simp only [gapPair]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hp i) (hp j)) (abs_nonneg _)))

public theorem nonneg_omitSum (hpos : ∀ i, 0 < p i) (r : Fin (m + 2)) :
    0 ≤ omitSum p (Yatom Z) r := by
  simp only [omitSum]
  exact Finset.sum_nonneg (fun F _ =>
    mul_nonneg (nonneg_ordWeight p hpos F) (abs_nonneg _))

/-- `ofReal` of an ordered `A` summand. -/
public theorem ofReal_ordTermA (hpos : ∀ i, 0 < p i)
    (F : Fin (m + 2) → Fin N) :
    ENNReal.ofReal (ordTermA p (Yatom Z) (Hatom Z) F)
    = (∏ r, wgt p (F r))
      * ((((m + 1)! : ℕ) : ℝ≥0∞)
        * volume (convexHull ℝ (Set.range (fun r => Z (F r))))) := by
  simp only [ordTermA, ordWeight]
  rw [ENNReal.ofReal_mul
      (Finset.prod_nonneg (fun r _ => le_of_lt (hpos (F r)))),
    ENNReal.ofReal_prod_of_nonneg (fun r _ => le_of_lt (hpos (F r))),
    ofReal_abs_AT Z F]
  simp only [wgt]

/-- `ofReal` of the ordered `A` sum is `(m+1)! S`. -/
public theorem ofReal_sum_ordTermA (hpos : ∀ i, 0 < p i) :
    ENNReal.ofReal (∑ F : Fin (m + 2) → Fin N,
      ordTermA p (Yatom Z) (Hatom Z) F)
    = ((((m + 1)! : ℕ)) : ℝ≥0∞)
      * S (m + 1) (atomMeas (wgt p) Z) := by
  have hc : ∀ i, wgt p i ≠ ∞ := fun i => wgt_ne_top p i
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun F _ => nonneg_ordTermA p Z hpos F)]
  trans ∑ F : Fin (m + 2) → Fin N, (∏ r, wgt p (F r))
    * (((((m + 1)! : ℕ)) : ℝ≥0∞)
      * volume (convexHull ℝ (Set.range (fun r => Z (F r)))))
  · apply Finset.sum_congr rfl
    intro F _
    exact ofReal_ordTermA p Z hpos F
  · have hfac : (∑ F : Fin (m + 2) → Fin N, (∏ r, wgt p (F r))
        * (((((m + 1)! : ℕ)) : ℝ≥0∞)
          * volume (convexHull ℝ (Set.range (fun r => Z (F r))))))
        = ((((m + 1)! : ℕ)) : ℝ≥0∞)
          * ∑ F : Fin (m + 2) → Fin N, (∏ r, wgt p (F r))
            * volume (convexHull ℝ (Set.range (fun r => Z (F r)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      ring
    rw [hfac, show m + 2 = (m + 1) + 1 from rfl]
    have hS := S_atomMeas (d := m + 1) (wgt p) Z hc
    simp only [smul_eq_mul] at hS
    rw [hS]

/-- `ofReal` of the gap pair sum is the coordinate gap. -/
public theorem ofReal_gapPair (hpos : ∀ i, 0 < p i) :
    ENNReal.ofReal (gapPair p (Hatom Z))
    = gap (Fin.last m) (atomMeas (wgt p) Z) := by
  have hc : ∀ i, wgt p i ≠ ∞ := fun i => wgt_ne_top p i
  have hp : ∀ i, 0 ≤ p i := fun i => le_of_lt (hpos i)
  have hterm : ∀ i j : Fin N,
      0 ≤ p i * p j * |Hatom Z i - Hatom Z j| :=
    fun i j => mul_nonneg (mul_nonneg (hp i) (hp j)) (abs_nonneg _)
  have hnn : ∀ x : ℝ, ENNReal.ofReal |x| = ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) := by
    intro x
    rw [← Real.norm_eq_abs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  simp only [gapPair]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => hterm i j))]
  trans ∑ i, ∑ j, (wgt p i * wgt p j)
    * ((‖Z i (Fin.last m) - Z j (Fin.last m)‖₊ : ℝ≥0∞))
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hterm i j)]
    apply Finset.sum_congr rfl
    intro j _
    have e1 : p i * p j * |Hatom Z i - Hatom Z j|
        = (p i * p j) * |Hatom Z i - Hatom Z j| := by ring
    rw [e1, ENNReal.ofReal_mul (mul_nonneg (hp i) (hp j)),
      ENNReal.ofReal_mul (hp i), hnn]
    simp only [wgt, Hatom]
  · have hG := gap_atomMeas (wgt p) Z (Fin.last m) hc
    simp only [smul_eq_mul] at hG
    rw [hG]

/-- Coordinate gap pair sum (real, general coordinate). -/
@[expose] public noncomputable def gapPairCoord (j : Fin (m + 1)) : ℝ :=
  ∑ i, ∑ j', p i * p j' * |Z i j - Z j' j|

/-- `ofReal` of a coordinate gap pair sum is the coordinate gap. -/
public theorem ofReal_gapPairCoord (hpos : ∀ i, 0 < p i) (j : Fin (m + 1)) :
    ENNReal.ofReal (gapPairCoord p Z j)
    = gap j (atomMeas (wgt p) Z) := by
  have hc : ∀ i, wgt p i ≠ ∞ := fun i => wgt_ne_top p i
  have hp : ∀ i, 0 ≤ p i := fun i => le_of_lt (hpos i)
  have hterm : ∀ i j' : Fin N,
      0 ≤ p i * p j' * |Z i j - Z j' j| :=
    fun i j' => mul_nonneg (mul_nonneg (hp i) (hp j')) (abs_nonneg _)
  have hnn : ∀ x : ℝ, ENNReal.ofReal |x| = ((‖x‖₊ : ℝ≥0) : ℝ≥0∞) := by
    intro x
    rw [← Real.norm_eq_abs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  simp only [gapPairCoord]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j' _ => hterm i j'))]
  trans ∑ i, ∑ j', (wgt p i * wgt p j')
    * ((‖Z i j - Z j' j‖₊ : ℝ≥0∞))
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_sum_of_nonneg (fun j' _ => hterm i j')]
    apply Finset.sum_congr rfl
    intro j' _
    have e1 : p i * p j' * |Z i j - Z j' j|
        = (p i * p j') * |Z i j - Z j' j| := by ring
    rw [e1, ENNReal.ofReal_mul (mul_nonneg (hp i) (hp j')),
      ENNReal.ofReal_mul (hp i), hnn]
    simp only [wgt]
  · have hG := gap_atomMeas (wgt p) Z j hc
    simp only [smul_eq_mul] at hG
    rw [hG]

/-- `ofReal` of an omission sum is `m! S` of the projected law. -/
public theorem ofReal_omitSum (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (r : Fin (m + 2)) :
    ENNReal.ofReal (omitSum p (Yatom Z) r)
    = ((((m)! : ℕ)) : ℝ≥0∞)
      * S m (atomMeas (wgt p) (Yatom Z)) := by
  have hc : ∀ i, wgt p i ≠ ∞ := fun i => wgt_ne_top p i
  rw [omitSum_eq p (Yatom Z) r hsum,
    ENNReal.ofReal_sum_of_nonneg
      (fun G _ => nonneg_ordTermD p Z hpos G)]
  trans ∑ G : Fin (m + 1) → Fin N, (∏ s, wgt p (G s))
    * (((((m)! : ℕ)) : ℝ≥0∞)
      * volume (convexHull ℝ (Set.range (fun s => Yatom Z (G s)))))
  · apply Finset.sum_congr rfl
    intro G _
    simp only [ordTermD, ordWeightD]
    rw [ENNReal.ofReal_mul
        (Finset.prod_nonneg (fun s _ => le_of_lt (hpos (G s)))),
      ENNReal.ofReal_prod_of_nonneg
        (fun s _ => le_of_lt (hpos (G s))),
      ofReal_abs_ordMatD Z G]
    simp only [wgt]
  · have hfac : (∑ G : Fin (m + 1) → Fin N, (∏ s, wgt p (G s))
        * (((((m)! : ℕ)) : ℝ≥0∞)
          * volume (convexHull ℝ (Set.range (fun s => Yatom Z (G s))))))
        = ((((m)! : ℕ)) : ℝ≥0∞)
          * ∑ G : Fin (m + 1) → Fin N, (∏ s, wgt p (G s))
            * volume (convexHull ℝ (Set.range (fun s => Yatom Z (G s)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      ring
    rw [hfac]
    have hS := S_atomMeas (d := m) (wgt p) (Yatom Z) hc
    simp only [smul_eq_mul] at hS
    rw [hS]

/-- `ofReal` of the determinant-inequality RHS in volume form. -/
public theorem ofReal_detRHS (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) :
    ENNReal.ofReal ((1 / 2) * gapPair p (Hatom Z)
      * ∑ r : Fin (m + 2), omitSum p (Yatom Z) r)
    = (ENNReal.ofReal (1 / 2) * gap (Fin.last m) (atomMeas (wgt p) Z))
      * ((((m + 2 : ℕ)) : ℝ≥0∞) * (((((m)! : ℕ)) : ℝ≥0∞)
        * S m (atomMeas (wgt p) (Yatom Z)))) := by
  have hgp : 0 ≤ gapPair p (Hatom Z) := nonneg_gapPair p Z hpos
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hgp),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ofReal_gapPair p Z hpos,
    ENNReal.ofReal_sum_of_nonneg
      (fun r _ => nonneg_omitSum p Z hpos r)]
  simp only [ofReal_omitSum p Z hpos hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Scalar identity: `(1/2)(m+2)m! = (m+1)! ((m+2)/(2(m+1)))`. -/
public theorem scalar_onestep :
    ENNReal.ofReal (1 / 2) * ((((m + 2 : ℕ))) : ℝ≥0∞)
        * ((((m)! : ℕ)) : ℝ≥0∞)
      = ((((m + 1)! : ℕ)) : ℝ≥0∞)
        * ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
          / (2 * ((((m + 1 : ℕ)) : ℝ))))) := by
  have e1 : ENNReal.ofReal (1 / 2) * ((((m + 2 : ℕ))) : ℝ≥0∞)
        * ((((m)! : ℕ)) : ℝ≥0∞)
      = ENNReal.ofReal ((1 / 2) * (((m + 2 : ℕ)) : ℝ)
        * ((((m)! : ℕ)) : ℝ)) := by
    simp only [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ)
        ≤ (1 / 2) * ((((m + 2 : ℕ)) : ℝ)))]
  have e2 : ((((m + 1)! : ℕ)) : ℝ≥0∞)
        * ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
          / (2 * ((((m + 1 : ℕ)) : ℝ)))))
      = ENNReal.ofReal ((((((m + 1)!) : ℕ)) : ℝ)
        * (((((m + 2 : ℕ)) : ℝ) / (2 * ((((m + 1 : ℕ)) : ℝ)))))) := by
    simp only [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [e1, e2]
  congr 1
  have hfact : ((((m + 1)!) : ℕ) : ℝ)
      = ((((m + 1 : ℕ)) : ℝ)) * ((((m)! : ℕ) : ℝ)) := by
    exact_mod_cast Nat.factorial_succ m
  rw [hfact]
  have hm1 : ((((m + 1 : ℕ))) : ℝ) ≠ 0 := by
    rw [ne_eq, Nat.cast_eq_zero]
    omega
  field_simp

/-- RHS volume form factored through `(m+1)!`. -/
public theorem factor_onestepRHS :
    (ENNReal.ofReal (1 / 2) * gap (Fin.last m) (atomMeas (wgt p) Z))
      * ((((m + 2 : ℕ)) : ℝ≥0∞) * (((((m)! : ℕ)) : ℝ≥0∞)
        * S m (atomMeas (wgt p) (Yatom Z))))
    = ((((m + 1)! : ℕ)) : ℝ≥0∞)
      * (ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
          / (2 * ((((m + 1 : ℕ)) : ℝ)))))
        * gap (Fin.last m) (atomMeas (wgt p) Z)
        * S m (atomMeas (wgt p) (Yatom Z))) := by
  have hrr : (ENNReal.ofReal (1 / 2)
        * gap (Fin.last m) (atomMeas (wgt p) Z))
        * ((((m + 2 : ℕ)) : ℝ≥0∞) * (((((m)! : ℕ)) : ℝ≥0∞)
          * S m (atomMeas (wgt p) (Yatom Z))))
      = (ENNReal.ofReal (1 / 2) * ((((m + 2 : ℕ))) : ℝ≥0∞)
          * ((((m)! : ℕ)) : ℝ≥0∞))
        * gap (Fin.last m) (atomMeas (wgt p) Z)
        * S m (atomMeas (wgt p) (Yatom Z)) := by
    ring
  have hrr2 : ((((m + 1)! : ℕ)) : ℝ≥0∞)
        * (ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
            / (2 * ((((m + 1 : ℕ)) : ℝ)))))
          * gap (Fin.last m) (atomMeas (wgt p) Z)
          * S m (atomMeas (wgt p) (Yatom Z)))
      = (((((m + 1)! : ℕ)) : ℝ≥0∞)
          * ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
            / (2 * ((((m + 1 : ℕ)) : ℝ))))))
        * gap (Fin.last m) (atomMeas (wgt p) Z)
        * S m (atomMeas (wgt p) (Yatom Z)) := by
    ring
  rw [hrr, hrr2, scalar_onestep]

public theorem factorial_cast_ne_zero : ((((m + 1)! : ℕ)) : ℝ≥0∞) ≠ 0 := by
  have hpos : 0 < (m + 1)! := Nat.factorial_pos _
  have h1 : (1 : ℝ≥0∞) ≤ ((((m + 1)! : ℕ)) : ℝ≥0∞) := by
    exact_mod_cast Nat.succ_le_of_lt hpos
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)

public theorem factorial_cast_ne_top : ((((m + 1)! : ℕ)) : ℝ≥0∞) ≠ ∞ := by
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_ne_top

/-- HI-ONESTEP: one-coordinate inequality for finitely supported laws.
With `d = m + 1`, the constant `(m+2)/(2(m+1))` is `(d+1)/(2d)`. -/
public theorem oneStep (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    S (m + 1) (atomMeas (wgt p) Z)
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ)
        / (2 * ((((m + 1 : ℕ)) : ℝ)))))
      * gap (Fin.last m) (atomMeas (wgt p) Z)
      * S m (atomMeas (wgt p) (Yatom Z)) := by
  have hdet := det_onestep p (Yatom Z) (Hatom Z) hpos hsum
  have h := ENNReal.ofReal_le_ofReal hdet
  rw [ofReal_sum_ordTermA p Z hpos, ofReal_detRHS p Z hpos hsum] at h
  rw [← ENNReal.mul_le_mul_iff_right
    (factorial_cast_ne_zero (m := m)) (factorial_cast_ne_top (m := m)),
    ← factor_onestepRHS p Z]
  exact h

end OneStep

section Base

variable {N : ℕ} (p : Fin N → ℝ)
  (Z : Fin N → EuclideanSpace ℝ (Fin (0 + 1)))

/-- Volume of a point in `0` dimensions is `1`. -/
public theorem volume_singleton_euclid0 (x : EuclideanSpace ℝ (Fin 0)) :
    volume ({x} : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  rw [volume_euclideanSpace_eq_dirac]
  have hx : x = 0 := (Unique.eq_default x).trans (Unique.eq_default 0).symm
  rw [hx]
  exact Measure.dirac_apply_of_mem (Set.mem_singleton 0)

/-- Reindexing `(Fin (0+1) → Fin N)` by evaluation at `0`. -/
public def singleTupleEquiv : (Fin (0 + 1) → Fin N) ≃ Fin N where
  toFun F := F 0
  invFun i := fun _ => i
  left_inv F := by
    refine funext fun r => ?_
    show (fun _ => F 0) r = F r
    have h0 : r.val = 0 := by
      have hlt := r.isLt
      omega
    have h0v : ((0 : Fin (0 + 1)) : ℕ) = 0 := by decide
    have hr : r = 0 := Fin.ext (h0.trans h0v.symm)
    rw [hr]
  right_inv i := rfl

/-- `S_0` of an atomic law is `1` (the `S_0 = 1` convention). -/
public theorem S0_atomMeas (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    S 0 (atomMeas (wgt p) (Yatom Z)) = 1 := by
  have hc : ∀ i, wgt p i ≠ ∞ := fun i => wgt_ne_top p i
  have hS := S_atomMeas (d := 0) (wgt p) (Yatom Z) hc
  rw [hS]
  trans ∑ i : Fin N, wgt p i
  · rw [← Equiv.sum_comp singleTupleEquiv (wgt p)]
    apply Finset.sum_congr rfl
    intro F _
    show (∏ r, wgt p (F r))
        • volume (convexHull ℝ (Set.range (fun r => Yatom Z (F r))))
      = wgt p (F 0)
    have hprod : (∏ r : Fin (0 + 1), wgt p (F r)) = wgt p (F 0) :=
      Fin.prod_univ_one _
    have hvol : volume (convexHull ℝ
        (Set.range (fun r => Yatom Z (F r)))) = 1 := by
      have hrange : Set.range (fun r => Yatom Z (F r))
          = {Yatom Z (F 0)} := by
        ext y
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨r, hr⟩
          have h0 : r.val = 0 := by
            have hlt := r.isLt
            omega
          have h0v : ((0 : Fin (0 + 1)) : ℕ) = 0 := by decide
          have hr2 : r = 0 := Fin.ext (h0.trans h0v.symm)
          rw [← hr, hr2]
        · intro h
          exact ⟨0, h.symm⟩
      rw [hrange, convexHull_singleton]
      exact volume_singleton_euclid0 _
    rw [hprod, hvol, smul_eq_mul, mul_one]
  · simp only [wgt, ← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => le_of_lt (hpos i)), hsum, ENNReal.ofReal_one]

/-- Omitted `D` determinants in dimension `0` are `1`. -/
public theorem det_ordMatD_zero (G : Fin (0 + 1) → Fin N) :
    Matrix.det (ordMatD (Yatom Z) G) = 1 := by
  calc Matrix.det (ordMatD (Yatom Z) G)
      = ordMatD (Yatom Z) G 0 0 := Matrix.det_fin_one _
    _ = 1 := by simp only [ordMatD, Matrix.of_apply, Fin.cases_zero]

/-- `A` determinant in dimension `0`: height difference. -/
public theorem det_ordMatA_zero (F : Fin (0 + 2) → Fin N) :
    Matrix.det (ordMatA (Yatom Z) (Hatom Z) F)
    = Hatom Z (F 0) - Hatom Z (F 1) := by
  rw [det_ordMatA_eq_sum Z F]
  have hsum : (∑ r : Fin (0 + 2), (-1 : ℝ) ^ (r : ℕ) * Hatom Z (F r)
      * Matrix.det (ordMatD (Yatom Z) (F ∘ r.succAbove)))
      = ((-1 : ℝ) ^ (((0 : Fin (0 + 2))) : ℕ) * Hatom Z (F 0)
        * Matrix.det (ordMatD (Yatom Z) (F ∘ (0 : Fin (0 + 2)).succAbove)))
      + ((-1 : ℝ) ^ (((1 : Fin (0 + 2))) : ℕ) * Hatom Z (F 1)
        * Matrix.det (ordMatD (Yatom Z) (F ∘ (1 : Fin (0 + 2)).succAbove))) :=
    Fin.sum_univ_two _
  rw [hsum, det_ordMatD_zero Z _, det_ordMatD_zero Z _]
  have h0v : (((0 : Fin (0 + 2))) : ℕ) = 0 := by decide
  have h1v : (((1 : Fin (0 + 2))) : ℕ) = 1 := by decide
  rw [h0v, h1v]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  ring

/-- Reindexing `(Fin (0+2) → Fin N)` by evaluation at `(0, 1)`. -/
public def pairTupleEquiv : (Fin (0 + 2) → Fin N) ≃ (Fin N × Fin N) where
  toFun F := (F 0, F 1)
  invFun q := fun r => if r = 0 then q.1 else q.2
  left_inv F := by
    refine funext fun r => ?_
    show (if r = 0 then F 0 else F 1) = F r
    by_cases h : r = 0
    · subst h
      simp
    · have hr1 : r = 1 := by
        have hlt : r.val < 0 + 2 := r.isLt
        have hne : r.val ≠ 0 := by
          intro hcon
          apply h
          have h0v : ((0 : Fin (0 + 2)) : ℕ) = 0 := by decide
          exact Fin.ext (hcon.trans h0v.symm)
        have hval : r.val = 1 := by omega
        have h1v : ((1 : Fin (0 + 2)) : ℕ) = 1 := by decide
        exact Fin.ext (hval.trans h1v.symm)
      rw [hr1]
      simp [(show ¬ (1 : Fin (0 + 2)) = 0 from by decide)]
  right_inv q := by
    show ((if (0 : Fin (0 + 2)) = 0 then q.1 else q.2),
      (if (1 : Fin (0 + 2)) = 0 then q.1 else q.2)) = q
    simp [(show ¬ (1 : Fin (0 + 2)) = 0 from by decide)]

/-- Ordered `A` sum in dimension `0` is the gap pair sum. -/
public theorem sum_ordTermA_zero :
    (∑ F : Fin (0 + 2) → Fin N, ordTermA p (Yatom Z) (Hatom Z) F)
    = gapPair p (Hatom Z) := by
  trans ∑ F : Fin (0 + 2) → Fin N,
    p (F 0) * p (F 1) * |Hatom Z (F 0) - Hatom Z (F 1)|
  · apply Finset.sum_congr rfl
    intro F _
    simp only [ordTermA, ordWeight]
    have hprod : (∏ r : Fin (0 + 2), p (F r)) = p (F 0) * p (F 1) :=
      Fin.prod_univ_two _
    rw [hprod, det_ordMatA_zero Z F]
  · trans ∑ q : Fin N × Fin N,
      p q.1 * p q.2 * |Hatom Z q.1 - Hatom Z q.2|
    · exact Equiv.sum_comp pairTupleEquiv
        (fun q : Fin N × Fin N => p q.1 * p q.2 * |Hatom Z q.1 - Hatom Z q.2|)
    · rw [gapPair]
      exact Fintype.sum_prod_type
        (fun q : Fin N × Fin N => p q.1 * p q.2 * |Hatom Z q.1 - Hatom Z q.2|)

/-- HI-BASE (equality): `S_1 = D_1` for finitely supported laws. -/
public theorem base_eq (hpos : ∀ i, 0 < p i) (_hsum : ∑ i, p i = 1) :
    S (0 + 1) (atomMeas (wgt p) Z)
    = gap (Fin.last 0) (atomMeas (wgt p) Z) := by
  have h1 := ofReal_sum_ordTermA (m := 0) p Z hpos
  rw [sum_ordTermA_zero p Z] at h1
  rw [ofReal_gapPair (m := 0) p Z hpos] at h1
  have hfact1 : ((((0 + 1)! : ℕ)) : ℝ≥0∞) = 1 := by
    rw [show (0 + 1)! = 1 from rfl, Nat.cast_one]
  rw [hfact1, one_mul] at h1
  exact h1.symm

/-- HI-BASE (inequality): `S_1 ≤ D_1` from the one-step bound. -/
public theorem base_le (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    S (0 + 1) (atomMeas (wgt p) Z)
    ≤ gap (Fin.last 0) (atomMeas (wgt p) Z) := by
  have h := oneStep (m := 0) p Z hpos hsum
  have hconst : ENNReal.ofReal (((((0 + 2 : ℕ)) : ℝ)
      / (2 * ((((0 + 1 : ℕ)) : ℝ))))) = 1 := by
    have e : ((((0 + 2 : ℕ)) : ℝ) / (2 * ((((0 + 1 : ℕ)) : ℝ)))) = 1 := by
      push_cast
      norm_num
    rw [e, ENNReal.ofReal_one]
  rw [hconst, S0_atomMeas p Z hpos hsum, one_mul, mul_one] at h
  exact h

end Base

end HypercubeInequality
