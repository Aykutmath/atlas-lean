module

/-
# Hypercube specialization (HI-CUBE-SETUP, HI-CUBE, HI-WCUBE)

Paper Section 9: vertex laws on `{0,1}^d`, Bernoulli gaps `D_j = 2p_j(1-p_j)`,
the counting identity for `S_d`, and the probability-weighted plus
arbitrary-weight hypercube inequalities. Zero vertex weights are handled by
restriction to the (positive) support, to which the finite-support main
theorem applies.
-/

public import Mathlib
public import Section_8_MainTheorem.Induction

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

section VertexSetup

variable {m : ℕ} (q : (Fin (m + 1) → Fin 2) → ℝ)

/-- Vertex embedding into Euclidean space. -/
@[expose] public noncomputable def vertPt (v : Fin (m + 1) → Fin 2) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (fun j => ((v j : Fin 2) : ℝ))

public theorem vertPt_apply (v : Fin (m + 1) → Fin 2) (j : Fin (m + 1)) :
    vertPt v j = ((v j : Fin 2) : ℝ) := rfl

/-- Coordinate means `p_j`. -/
@[expose] public noncomputable def vertMean (j : Fin (m + 1)) : ℝ :=
  ∑ v, q v * ((v j : Fin 2) : ℝ)

/-- Vertex law (all vertices, zero weights allowed). -/
@[expose] public noncomputable def vertMeas : Measure (EuclideanSpace ℝ (Fin (m + 1))) :=
  ∑ v, ENNReal.ofReal (q v) • Measure.dirac (vertPt v)

/-- Decidability for the support predicate (classical). -/
noncomputable instance decPred_supp :
    DecidablePred (fun v : Fin (m + 1) → Fin 2 => (0 : ℝ) < q v) :=
  fun v => Classical.propDecidable (0 < q v)

/-- Positive support as a finset. -/
@[expose] public noncomputable def suppFinset : Finset (Fin (m + 1) → Fin 2) :=
  Finset.univ.filter (fun v => (0 : ℝ) < q v)

@[expose] public noncomputable def suppCard : ℕ := (suppFinset q).card

@[expose] public noncomputable def suppEquiv : ↥(suppFinset q) ≃ Fin (suppCard q) :=
  Finset.equivFin _

@[expose] public noncomputable def suppWgt (i : Fin (suppCard q)) : ℝ :=
  q (((suppEquiv q).symm i).val)

@[expose] public noncomputable def suppPt (i : Fin (suppCard q)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  vertPt (((suppEquiv q).symm i).val)

public theorem suppWgt_pos (i : Fin (suppCard q)) : 0 < suppWgt q i := by
  simp only [suppWgt]
  have hmem : (((suppEquiv q).symm i).val) ∈ suppFinset q :=
    (((suppEquiv q).symm i).property)
  simp only [suppFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- Support sums extend to vertex sums (zero weights vanish). -/
public theorem sum_supp_eq_univ {M : Type*} [AddCommMonoid M]
    (hq_nonneg : ∀ v, 0 ≤ q v) (f : (Fin (m + 1) → Fin 2) → M)
    (hf0 : ∀ v, q v = 0 → f v = 0) :
    ∑ x : ↥(suppFinset q), f x.val = ∑ v, f v := by
  have h1 : ∑ x : ↥(suppFinset q), f x.val = ∑ v ∈ suppFinset q, f v :=
    Finset.sum_coe_sort _ _
  rw [h1]
  have h2 : ∑ v ∈ suppFinset q, f v = ∑ v ∈ Finset.univ, f v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    simp only [suppFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hv
    have hq0 : q v = 0 := le_antisymm hv (hq_nonneg v)
    exact hf0 v hq0
  exact h2

public theorem suppWgt_sum (hq_nonneg : ∀ v, 0 ≤ q v) (hq_sum : ∑ v, q v = 1) :
    ∑ i, suppWgt q i = 1 := by
  have h1 : (∑ i, suppWgt q i)
      = ∑ x : ↥(suppFinset q), q x.val := by
    simp only [suppWgt]
    exact Equiv.sum_comp (suppEquiv q).symm
      (fun x : ↥(suppFinset q) => q x.val)
  rw [h1]
  have h2 : ∑ x : ↥(suppFinset q), q x.val = ∑ v, q v :=
    sum_supp_eq_univ q hq_nonneg (fun v => q v) (fun v h => h)
  rw [h2, hq_sum]

/-- Vertex law equals the support atomic law. -/
public theorem vertMeas_eq_suppAtom (hq_nonneg : ∀ v, 0 ≤ q v) :
    vertMeas q = atomMeas (wgt (suppWgt q)) (suppPt q) := by
  simp only [vertMeas, atomMeas]
  have h1 : (∑ i, wgt (suppWgt q) i • Measure.dirac (suppPt q i))
      = ∑ x : ↥(suppFinset q),
        ENNReal.ofReal (q x.val) • Measure.dirac (vertPt x.val) := by
    simp only [wgt, suppWgt, suppPt]
    exact Equiv.sum_comp (suppEquiv q).symm
      (fun x : ↥(suppFinset q) =>
        ENNReal.ofReal (q x.val) • Measure.dirac (vertPt x.val))
  rw [h1]
  have h2 : (∑ x : ↥(suppFinset q),
        ENNReal.ofReal (q x.val) • Measure.dirac (vertPt x.val))
      = ∑ v, ENNReal.ofReal (q v) • Measure.dirac (vertPt v) := by
    refine sum_supp_eq_univ q hq_nonneg
      (fun v => ENNReal.ofReal (q v) • Measure.dirac (vertPt v)) ?_
    intro v hv
    show ENNReal.ofReal (q v) • Measure.dirac (vertPt v) = 0
    rw [hv, ENNReal.ofReal_zero, zero_smul]
  rw [h2]

/-- Finite-support main inequality applied to the vertex law. -/
public theorem cube_main_inequality (hq_nonneg : ∀ v, 0 ≤ q v)
    (hq_sum : ∑ v, q v = 1) :
    S (m + 1) (vertMeas q)
    ≤ ENNReal.ofReal (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), gap j (vertMeas q) := by
  have hmain := main_fin_support m (suppCard q) (suppWgt q) (suppPt q)
    (suppWgt_pos q) (suppWgt_sum q hq_nonneg hq_sum)
  rw [← vertMeas_eq_suppAtom q hq_nonneg] at hmain
  exact hmain

end VertexSetup

section Bernoulli

variable {m : ℕ} (q : (Fin (m + 1) → Fin 2) → ℝ)

public theorem fin2_cast_zero : ((((0 : Fin 2))) : ℝ) = 0 := by
  rw [show (((0 : Fin 2)) : ℕ) = 0 from by decide, Nat.cast_zero]

public theorem fin2_cast_one : ((((1 : Fin 2))) : ℝ) = 1 := by
  rw [show (((1 : Fin 2)) : ℕ) = 1 from by decide, Nat.cast_one]

public theorem fin2_dichotomy (b : Fin 2) : b = 0 ∨ b = 1 := by
  have hlt : b.val < 2 := b.isLt
  have h02 : b.val = 0 ∨ b.val = 1 := by omega
  have h0v : ((0 : Fin 2) : ℕ) = 0 := by decide
  have h1v : ((1 : Fin 2) : ℕ) = 1 := by decide
  rcases h02 with h | h
  · exact Or.inl (Fin.ext (h.trans h0v.symm))
  · exact Or.inr (Fin.ext (h.trans h1v.symm))

/-- Bit of a support atom at coordinate `j`. -/
@[expose] public noncomputable def suppBit (i : Fin (suppCard q))
    (j : Fin (m + 1)) : Fin 2 :=
  (((suppEquiv q).symm i).val j)

/-- Support fiber with bit `a` at coordinate `j`. -/
@[expose] public noncomputable def suppFiber (j : Fin (m + 1)) (a : Fin 2) :
    Finset (Fin (suppCard q)) :=
  Finset.univ.filter (fun i => suppBit q i j = a)

/-- Support Bernoulli parameter. -/
@[expose] public noncomputable def suppMean (j : Fin (m + 1)) : ℝ :=
  ∑ i, suppWgt q i * (suppPt q i j)

public theorem suppPt_bit (i : Fin (suppCard q)) (j : Fin (m + 1)) :
    suppPt q i j = ((suppBit q i j : Fin 2) : ℝ) := rfl

public theorem suppFiber_neg_eq (j : Fin (m + 1)) :
    Finset.univ.filter (fun i : Fin (suppCard q) => ¬ suppBit q i j = 0)
    = suppFiber q j 1 := by
  ext i
  simp only [suppFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases fin2_dichotomy (suppBit q i j) with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h hcon
    rw [h] at hcon
    exact (by decide : ¬ (1 : Fin 2) = 0) hcon

/-- Fiber gap sum factors through the bit-difference. -/
public theorem fiber_gap_sum (j : Fin (m + 1)) (a b : Fin 2) :
    (∑ i ∈ suppFiber q j a, ∑ i' ∈ suppFiber q j b,
      suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|)
    = (∑ i ∈ suppFiber q j a, suppWgt q i)
      * (∑ i' ∈ suppFiber q j b, suppWgt q i')
      * |(((a : Fin 2) : ℝ) - ((b : Fin 2) : ℝ))| := by
  have hterm : ∀ i ∈ suppFiber q j a, ∀ i' ∈ suppFiber q j b,
      suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|
      = suppWgt q i * suppWgt q i'
        * |(((a : Fin 2) : ℝ) - ((b : Fin 2) : ℝ))| := by
    intro i hi i' hi'
    simp only [suppFiber, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hi'
    have e1 : suppPt q i j = ((a : Fin 2) : ℝ) := by
      rw [suppPt_bit, hi]
    have e2 : suppPt q i' j = ((b : Fin 2) : ℝ) := by
      rw [suppPt_bit, hi']
    rw [e1, e2]
  calc (∑ i ∈ suppFiber q j a, ∑ i' ∈ suppFiber q j b,
        suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|)
      = ∑ i ∈ suppFiber q j a, ∑ i' ∈ suppFiber q j b,
        suppWgt q i * suppWgt q i'
          * abs ((((a : Fin 2) : ℝ) - ((b : Fin 2) : ℝ))) :=
        Finset.sum_congr rfl (fun i hi =>
          Finset.sum_congr rfl (fun i' hi' => hterm i hi i' hi'))
    _ = (∑ i ∈ suppFiber q j a, suppWgt q i)
        * (∑ i' ∈ suppFiber q j b, suppWgt q i')
        * abs ((((a : Fin 2) : ℝ) - ((b : Fin 2) : ℝ))) := by
        simp only [← Finset.sum_mul, ← Finset.sum_mul_sum]

/-- One-fiber mass is the support Bernoulli parameter. -/
public theorem fiber_mass_one (j : Fin (m + 1)) :
    (∑ i ∈ suppFiber q j 1, suppWgt q i) = suppMean q j := by
  simp only [suppMean]
  have hsp : (∑ i, suppWgt q i * suppPt q i j)
      = (∑ i ∈ suppFiber q j 0, suppWgt q i * suppPt q i j)
      + (∑ i ∈ suppFiber q j 1, suppWgt q i * suppPt q i j) := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (suppCard q) => suppBit q i j = 0)
      (fun i => suppWgt q i * suppPt q i j)
    rw [suppFiber_neg_eq q j] at h
    exact h.symm
  rw [hsp]
  have hz : (∑ i ∈ suppFiber q j 0, suppWgt q i * suppPt q i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [suppFiber, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    have e : suppPt q i j = ((0 : Fin 2) : ℝ) := by
      rw [suppPt_bit, hi]
    rw [e, fin2_cast_zero, mul_zero]
  have ho : (∑ i ∈ suppFiber q j 1, suppWgt q i * suppPt q i j)
      = ∑ i ∈ suppFiber q j 1, suppWgt q i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [suppFiber, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    have e : suppPt q i j = ((1 : Fin 2) : ℝ) := by
      rw [suppPt_bit, hi]
    rw [e, fin2_cast_one, mul_one]
  rw [hz, ho, zero_add]

/-- Zero-fiber mass is complementary. -/
public theorem fiber_mass_zero (j : Fin (m + 1))
    (hq_nonneg : ∀ v, 0 ≤ q v) (hq_sum : ∑ v, q v = 1) :
    (∑ i ∈ suppFiber q j 0, suppWgt q i) = 1 - suppMean q j := by
  have hsp : (∑ i, suppWgt q i)
      = (∑ i ∈ suppFiber q j 0, suppWgt q i)
      + (∑ i ∈ suppFiber q j 1, suppWgt q i) := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (suppCard q) => suppBit q i j = 0)
      (fun i => suppWgt q i)
    rw [suppFiber_neg_eq q j] at h
    exact h.symm
  rw [suppWgt_sum q hq_nonneg hq_sum, fiber_mass_one q j] at hsp
  linarith

/-- Support gap pair sum in Bernoulli form. -/
public theorem gapPairCoord_supp_eq (j : Fin (m + 1))
    (hq_nonneg : ∀ v, 0 ≤ q v) (hq_sum : ∑ v, q v = 1) :
    gapPairCoord (suppWgt q) (suppPt q) j
    = 2 * suppMean q j * (1 - suppMean q j) := by
  have hsplit : ∀ f : Fin (suppCard q) → ℝ,
      (∑ i, f i)
      = (∑ i ∈ suppFiber q j 0, f i) + (∑ i ∈ suppFiber q j 1, f i) := by
    intro f
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (suppCard q) => suppBit q i j = 0) f
    rw [suppFiber_neg_eq q j] at h
    exact h.symm
  have hf00 : (∑ i ∈ suppFiber q j 0, ∑ i' ∈ suppFiber q j 0,
        suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|) = 0 := by
    rw [fiber_gap_sum q j 0 0, fin2_cast_zero, sub_self, abs_zero, mul_zero]
  have hf11 : (∑ i ∈ suppFiber q j 1, ∑ i' ∈ suppFiber q j 1,
        suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|) = 0 := by
    rw [fiber_gap_sum q j 1 1, fin2_cast_one, sub_self, abs_zero, mul_zero]
  have hf01 : (∑ i ∈ suppFiber q j 0, ∑ i' ∈ suppFiber q j 1,
        suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|)
      = (∑ i ∈ suppFiber q j 0, suppWgt q i)
        * (∑ i' ∈ suppFiber q j 1, suppWgt q i') := by
    rw [fiber_gap_sum q j 0 1, fin2_cast_zero, fin2_cast_one]
    norm_num
  have hf10 : (∑ i ∈ suppFiber q j 1, ∑ i' ∈ suppFiber q j 0,
        suppWgt q i * suppWgt q i' * |suppPt q i j - suppPt q i' j|)
      = (∑ i ∈ suppFiber q j 1, suppWgt q i)
        * (∑ i' ∈ suppFiber q j 0, suppWgt q i') := by
    rw [fiber_gap_sum q j 1 0, fin2_cast_zero, fin2_cast_one]
    norm_num
  simp only [gapPairCoord]
  have hinner : ∀ i ∈ Finset.univ, (∑ i', suppWgt q i * suppWgt q i'
      * |suppPt q i j - suppPt q i' j|)
      = (∑ i' ∈ suppFiber q j 0, suppWgt q i * suppWgt q i'
          * |suppPt q i j - suppPt q i' j|)
      + (∑ i' ∈ suppFiber q j 1, suppWgt q i * suppWgt q i'
          * |suppPt q i j - suppPt q i' j|) :=
    fun i _ => hsplit _
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib,
    hsplit, hsplit, hf00, hf01, hf10, hf11,
    fiber_mass_one q j, fiber_mass_zero q j hq_nonneg hq_sum]
  ring

/-- Support Bernoulli parameter equals the vertex mean. -/
public theorem suppMean_eq_vertMean (j : Fin (m + 1))
    (hq_nonneg : ∀ v, 0 ≤ q v) :
    suppMean q j = vertMean q j := by
  have h1 : (∑ i, suppWgt q i * suppPt q i j)
      = ∑ x : ↥(suppFinset q), q x.val * ((x.val j : Fin 2) : ℝ) :=
    Equiv.sum_comp (suppEquiv q).symm
      (fun x : ↥(suppFinset q) => q x.val * ((x.val j : Fin 2) : ℝ))
  have hf0 : ∀ v, q v = 0 →
      (fun v => q v * ((v j : Fin 2) : ℝ)) v = 0 := by
    intro v hv
    show q v * ((v j : Fin 2) : ℝ) = 0
    rw [hv, zero_mul]
  have h2 : (∑ x : ↥(suppFinset q), q x.val * ((x.val j : Fin 2) : ℝ))
      = ∑ v, q v * ((v j : Fin 2) : ℝ) :=
    sum_supp_eq_univ q hq_nonneg
      (fun v => q v * ((v j : Fin 2) : ℝ)) hf0
  simp only [suppMean, vertMean]
  rw [h1, h2]

/-- HI-CUBE Bernoulli gaps: `D_j = 2p_j(1-p_j)`. -/
public theorem gap_vertMeas_eq (j : Fin (m + 1))
    (hq_nonneg : ∀ v, 0 ≤ q v) (hq_sum : ∑ v, q v = 1) :
    gap j (vertMeas q)
    = ENNReal.ofReal (2 * vertMean q j * (1 - vertMean q j)) := by
  rw [vertMeas_eq_suppAtom q hq_nonneg,
    ← ofReal_gapPairCoord (suppWgt q) (suppPt q) (suppWgt_pos q) j,
    gapPairCoord_supp_eq q j hq_nonneg hq_sum,
    suppMean_eq_vertMean q j hq_nonneg]

end Bernoulli

section Counting

variable {m : ℕ} (q : (Fin (m + 1) → Fin 2) → ℝ)

/-- Support `S` summand. -/
@[expose] public noncomputable def suppSterm (F : Fin (m + 2) → Fin (suppCard q)) : ℝ≥0∞ :=
  (∏ r, wgt (suppWgt q) (F r))
    • volume (convexHull ℝ (Set.range (fun r => suppPt q (F r))))

/-- Non-injective tuples have zero volume. -/
public theorem suppVol_zero (F : Fin (m + 2) → Fin (suppCard q))
    (hF : ¬ Function.Injective F) :
    volume (convexHull ℝ (Set.range (fun r => suppPt q (F r)))) = 0 := by
  simp only [Function.Injective] at hF
  push Not at hF
  obtain ⟨a, b, hab, hne⟩ := hF
  have hdet : simDet (fun r => suppPt q (F r)) = 0 := by
    simp only [simDet]
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp only [Matrix.of_apply]
    rw [hab]
  have hvol := abs_simDet_eq_volume_convexHull (fun r => suppPt q (F r))
  rw [hdet, abs_zero, ENNReal.ofReal_zero] at hvol
  have hfact : ((((m + 1)! : ℕ)) : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < (m + 1)! := Nat.factorial_pos _
    have h1 : (1 : ℝ≥0∞) ≤ ((((m + 1)! : ℕ)) : ℝ≥0∞) := by
      exact_mod_cast Nat.succ_le_of_lt hpos
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  exact (mul_eq_zero.mp hvol.symm).resolve_left hfact

/-- Support `S` summand vanishes on non-injective tuples. -/
public theorem suppSterm_van (F : Fin (m + 2) → Fin (suppCard q))
    (hF : ¬ Function.Injective F) : suppSterm q F = 0 := by
  simp only [suppSterm, suppVol_zero q F hF, smul_eq_mul, mul_zero]

/-- Support `S` summand is permutation-invariant. -/
public theorem suppSterm_invar (e : Fin (m + 2) → Fin (suppCard q))
    (σ : Equiv.Perm (Fin (m + 2))) :
    suppSterm q (e ∘ ⇑σ) = suppSterm q e := by
  have hweight : (∏ r, wgt (suppWgt q) ((e ∘ ⇑σ) r))
      = ∏ r, wgt (suppWgt q) (e r) :=
    Equiv.prod_comp σ (fun s => wgt (suppWgt q) (e s))
  have hrange : Set.range (fun r => suppPt q ((e ∘ ⇑σ) r))
      = Set.range (fun r => suppPt q (e r)) := by
    have hσ : Set.range (⇑σ : Fin (m + 2) → Fin (m + 2)) = Set.univ :=
      Set.range_eq_univ.mpr σ.surjective
    calc Set.range (fun r => suppPt q ((e ∘ ⇑σ) r))
        = Set.range ((fun s => suppPt q (e s)) ∘ ⇑σ) := rfl
      _ = (fun s => suppPt q (e s)) '' Set.range (⇑σ) := Set.range_comp _ _
      _ = (fun s => suppPt q (e s)) '' Set.univ := by rw [hσ]
      _ = Set.range (fun r => suppPt q (e r)) := Set.image_univ
  simp only [suppSterm, hweight, hrange]

/-- Support `T` summand. -/
@[expose] public noncomputable def suppTSum : ℝ≥0∞ :=
  ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
    volume (convexHull ℝ ((fun i => suppPt q i) '' (T : Set (Fin (suppCard q)))))
    * ∏ i ∈ T, wgt (suppWgt q) i

/-- Vertex `T` summand. -/
@[expose] public noncomputable def vertTSum : ℝ≥0∞ :=
  ∑ U ∈ Finset.powersetCard (m + 2) Finset.univ,
    volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) '' (U : Set (Fin (m + 1) → Fin 2))))
    * ∏ v ∈ U, ENNReal.ofReal (q v)

/-- Ordered-tuple summand at a fixed set. -/
public theorem suppSterm_orderEmb (T : Finset (Fin (suppCard q)))
    (hT : T.card = m + 2) :
    suppSterm q ⇑(T.orderEmbOfFin hT)
    = volume (convexHull ℝ ((fun i => suppPt q i) '' (T : Set _)))
      * ∏ i ∈ T, wgt (suppWgt q) i := by
  have hmem : ∀ r, (T.orderEmbOfFin hT) r ∈ T := by
    intro r
    have hr : (T.orderEmbOfFin hT) r
        ∈ Set.range ⇑(T.orderEmbOfFin hT) :=
      Set.mem_range_self r
    rw [Finset.range_orderEmbOfFin] at hr
    exact Finset.mem_coe.mp hr
  have hweight : (∏ r, wgt (suppWgt q) ((T.orderEmbOfFin hT) r))
      = ∏ i ∈ T, wgt (suppWgt q) i := by
    apply Finset.prod_bij (fun r _ => (T.orderEmbOfFin hT) r)
      (fun r _ => hmem r)
    · intro r₁ _ r₂ _ h
      exact (T.orderEmbOfFin hT).injective h
    · intro i hi
      have hr : (i : Fin (suppCard q))
          ∈ Set.range ⇑(T.orderEmbOfFin hT) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hi
      obtain ⟨r, hr⟩ := hr
      exact ⟨r, Finset.mem_univ r, hr⟩
    · intro r _
      rfl
  have hvol : volume (convexHull ℝ
        (Set.range (fun r => suppPt q ((T.orderEmbOfFin hT) r))))
      = volume (convexHull ℝ ((fun i => suppPt q i) '' (T : Set _))) := by
    congr 2
    calc Set.range (fun r => suppPt q ((T.orderEmbOfFin hT) r))
        = Set.range ((fun i => suppPt q i) ∘ ⇑(T.orderEmbOfFin hT)) := rfl
      _ = (fun i => suppPt q i) '' Set.range ⇑(T.orderEmbOfFin hT) :=
        Set.range_comp _ _
      _ = (fun i => suppPt q i) '' (T : Set _) := by
        rw [Finset.range_orderEmbOfFin]
  simp only [suppSterm, smul_eq_mul]
  rw [hweight, hvol]
  exact mul_comm _ _

/-- `S` of the support law via the counting engine. -/
public theorem suppS_eq_tsum :
    S (m + 1) (atomMeas (wgt (suppWgt q)) (suppPt q))
    = ((((m + 2)! : ℕ)) : ℝ≥0∞) * suppTSum q := by
  have hc : ∀ i, wgt (suppWgt q) i ≠ ∞ := fun i => wgt_ne_top _ i
  have hS := S_atomMeas (wgt (suppWgt q)) (suppPt q) (d := m + 1) hc
  have hcount := counting_engine_ennreal (K := m + 2) (N := suppCard q)
    (suppSterm q) (suppSterm_van q) (suppSterm_invar q)
  have hper : ∀ T : { T : Finset (Fin (suppCard q)) // T.card = m + 2 },
      suppSterm q ⇑(T.1.orderEmbOfFin T.2)
      = volume (convexHull ℝ ((fun i => suppPt q i) '' (T.1 : Set _)))
        * ∏ i ∈ T.1, wgt (suppWgt q) i :=
    fun T => suppSterm_orderEmb q T.1 T.2
  have hconv := sum_subtype_card_eq_powersetCard_ennreal (K := m + 2)
    (N := suppCard q)
    (fun T => volume (convexHull ℝ ((fun i => suppPt q i) '' (T : Set _)))
      * ∏ i ∈ T, wgt (suppWgt q) i)
  rw [hS]
  show (∑ F : Fin (m + 2) → Fin (suppCard q), suppSterm q F)
    = ((((m + 2)! : ℕ)) : ℝ≥0∞) * suppTSum q
  rw [hcount]
  congr 1
  trans ∑ T : { T : Finset (Fin (suppCard q)) // T.card = m + 2 },
    (volume (convexHull ℝ ((fun i => suppPt q i) '' (T.1 : Set _)))
      * ∏ i ∈ T.1, wgt (suppWgt q) i)
  · exact Finset.sum_congr rfl (fun T _ => hper T)
  · exact hconv

/-- Support index to vertex. -/
@[expose] public noncomputable def suppVert (i : Fin (suppCard q)) :
    Fin (m + 1) → Fin 2 :=
  ((suppEquiv q).symm i).val

public theorem suppVert_injective : Function.Injective (suppVert q) := by
  intro a b hab
  simp only [suppVert] at hab
  have hsub : (suppEquiv q).symm a = (suppEquiv q).symm b :=
    Subtype.ext hab
  exact (suppEquiv q).symm.injective hsub

/-- Vertex image of a support set. -/
@[expose] public noncomputable def suppImage (T : Finset (Fin (suppCard q))) :
    Finset (Fin (m + 1) → Fin 2) :=
  T.map ⟨suppVert q, suppVert_injective q⟩

public theorem suppImage_card (T : Finset (Fin (suppCard q))) :
    (suppImage q T).card = T.card := by
  simp only [suppImage, Finset.card_map]

public theorem suppImage_mem_supp (T : Finset (Fin (suppCard q))) :
    suppImage q T ⊆ suppFinset q := by
  intro v hv
  simp only [suppImage, Finset.mem_map] at hv
  obtain ⟨i, _, rfl⟩ := hv
  exact ((suppEquiv q).symm i).property

/-- Support `T`-term equals the vertex `T`-term of its image. -/
public theorem suppTerm_eq_vertTerm (T : Finset (Fin (suppCard q))) :
    volume (convexHull ℝ ((fun i => suppPt q i) '' (T : Set _)))
      * ∏ i ∈ T, wgt (suppWgt q) i
    = volume (convexHull ℝ
        ((fun v : Fin (m + 1) → Fin 2 => vertPt v) '' ((suppImage q T : Finset _) : Set _)))
      * ∏ v ∈ suppImage q T, ENNReal.ofReal (q v) := by
  have hvol : volume (convexHull ℝ
        ((fun i => suppPt q i) '' (T : Set (Fin (suppCard q)))))
      = volume (convexHull ℝ
        ((fun v : Fin (m + 1) → Fin 2 => vertPt v) '' ((suppImage q T : Finset _) : Set _))) := by
    have himg : (fun i => suppPt q i) '' (T : Set (Fin (suppCard q)))
        = (fun v : Fin (m + 1) → Fin 2 => vertPt v) '' ((suppImage q T : Finset _) : Set _) := by
      have hfun : (fun i => suppPt q i)
          = (fun v : Fin (m + 1) → Fin 2 => vertPt v) ∘ (suppVert q) := rfl
      rw [hfun, Set.image_comp]
      simp only [suppImage, Finset.coe_map, Function.Embedding.coeFn_mk]
    rw [himg]
  have hwgt : (∏ i ∈ T, wgt (suppWgt q) i)
      = ∏ v ∈ suppImage q T, ENNReal.ofReal (q v) := by
    simp only [suppImage]
    trans ∏ i ∈ T, ENNReal.ofReal (q (suppVert q i))
    · rfl
    · exact (Finset.prod_map T ⟨suppVert q, suppVert_injective q⟩
        (fun v => ENNReal.ofReal (q v))).symm
  rw [hvol, hwgt]

/-- Off-support `T`-terms vanish. -/
public theorem vertTerm_zero (hq_nonneg : ∀ v, 0 ≤ q v)
    (U : Finset (Fin (m + 1) → Fin 2)) (_ : U ∈ Finset.powersetCard (m + 2) Finset.univ)
    (hU : ¬ U ⊆ suppFinset q) :
    volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) '' (U : Set _)))
      * ∏ v ∈ U, ENNReal.ofReal (q v) = 0 := by
  simp only [Finset.subset_iff] at hU
  push Not at hU
  obtain ⟨v, hvU, hvs⟩ := hU
  have hq0 : q v = 0 := by
    simp only [suppFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hvs
    exact le_antisymm hvs (hq_nonneg v)
  have hprod : (∏ v ∈ U, ENNReal.ofReal (q v)) = 0 := by
    apply Finset.prod_eq_zero hvU
    rw [hq0, ENNReal.ofReal_zero]
  rw [hprod, mul_zero]

/-- Vertex `T`-sum restricts to on-support sets. -/
public theorem vertTSum_eq_filtered (hq_nonneg : ∀ v, 0 ≤ q v) :
    vertTSum q
    = ∑ U ∈ (Finset.powersetCard (m + 2) Finset.univ).filter
        (· ⊆ suppFinset q),
      volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) '' (U : Set _)))
      * ∏ v ∈ U, ENNReal.ofReal (q v) := by
  simp only [vertTSum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro U hU hUf
  simp only [Finset.mem_filter] at hUf
  have hnot : ¬ U ⊆ suppFinset q := fun hsub => hUf ⟨hU, hsub⟩
  exact vertTerm_zero q hq_nonneg U hU hnot

/-- Support and vertex `T`-sums agree. -/
public theorem suppTSum_eq_vertTSum (hq_nonneg : ∀ v, 0 ≤ q v) :
    suppTSum q = vertTSum q := by
  rw [vertTSum_eq_filtered q hq_nonneg]
  simp only [suppTSum]
  apply Finset.sum_bij (fun T _ => suppImage q T)
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, suppImage_mem_supp q T⟩
    rw [suppImage_card q T]
    exact (Finset.mem_powersetCard.mp hT).2
  · intro T₁ _ T₂ _ h
    simp only [suppImage] at h
    exact Finset.map_injective ⟨suppVert q, suppVert_injective q⟩ h
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hU
    obtain ⟨⟨-, hcard⟩, hsub⟩ := hU
    set T : Finset (Fin (suppCard q)) :=
      Finset.univ.filter (fun i => suppVert q i ∈ U) with hTdef
    have hsurj : ∀ v ∈ U, ∃ i, suppVert q i = v := by
      intro v hv
      have hvs : v ∈ suppFinset q := hsub hv
      refine ⟨(suppEquiv q) ⟨v, hvs⟩, ?_⟩
      simp only [suppVert]
      rw [Equiv.symm_apply_apply]
    have hTU : T.map ⟨suppVert q, suppVert_injective q⟩ = U := by
      ext v
      simp only [Finset.mem_map, hTdef, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hv
        obtain ⟨i, rfl⟩ := hsurj v hv
        exact ⟨i, hv, rfl⟩
    have hcardT : T.card = m + 2 := by
      have hcc := congrArg Finset.card hTU
      simp only [Finset.card_map] at hcc
      rw [hcard] at hcc
      exact hcc
    refine ⟨T, ?_, ?_⟩
    · simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hcardT⟩
    · show suppImage q T = U
      simp only [suppImage]
      exact hTU
  · intro T _
    exact suppTerm_eq_vertTerm q T

/-- `S` of the vertex law in `T`-sum form. -/
public theorem vertS_eq_tsum (hq_nonneg : ∀ v, 0 ≤ q v) :
    S (m + 1) (vertMeas q)
    = ((((m + 2)! : ℕ)) : ℝ≥0∞) * vertTSum q := by
  rw [vertMeas_eq_suppAtom q hq_nonneg, suppS_eq_tsum q,
    suppTSum_eq_vertTSum q hq_nonneg]

end Counting

section ProbForm

variable {m : ℕ} (q : (Fin (m + 1) → Fin 2) → ℝ)

/-- Real volume of a vertex-set hull. -/
@[expose] public noncomputable def cubeVol (U : Finset (Fin (m + 1) → Fin 2)) : ℝ :=
  (volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
    (U : Set (Fin (m + 1) → Fin 2))))).toReal

/-- Real probability-weighted `T`-sum (HI-CUBE left side). -/
@[expose] public noncomputable def cubeTsum : ℝ :=
  ∑ U ∈ Finset.powersetCard (m + 2) Finset.univ,
    cubeVol U * ∏ v ∈ U, q v

public theorem volume_vertHull_ne_top (U : Finset (Fin (m + 1) → Fin 2)) :
    volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
      (U : Set (Fin (m + 1) → Fin 2)))) ≠ ∞ := by
  have hfin : ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
      (U : Set (Fin (m + 1) → Fin 2))).Finite :=
    (Finset.finite_toSet U).image _
  have hc : IsCompact (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
      (U : Set (Fin (m + 1) → Fin 2)))) :=
    hfin.isCompact_convexHull ℝ
  exact ne_top_of_lt hc.measure_lt_top

public theorem cubeVol_nonneg (U : Finset (Fin (m + 1) → Fin 2)) :
    0 ≤ cubeVol U := by
  simp only [cubeVol]
  exact ENNReal.toReal_nonneg

/-- Each `T`-term is a finite real. -/
public theorem vertTerm_eq_ofReal (hq_nonneg : ∀ v, 0 ≤ q v)
    (U : Finset (Fin (m + 1) → Fin 2)) :
    volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
        (U : Set (Fin (m + 1) → Fin 2))))
      * ∏ v ∈ U, ENNReal.ofReal (q v)
    = ENNReal.ofReal (cubeVol U * ∏ v ∈ U, q v) := by
  rw [← ENNReal.ofReal_toReal (volume_vertHull_ne_top U),
    ← ENNReal.ofReal_prod_of_nonneg (fun v _ => hq_nonneg v),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simp only [cubeVol]

/-- The `T`-sum is a finite real. -/
public theorem vertTSum_eq_ofReal (hq_nonneg : ∀ v, 0 ≤ q v) :
    vertTSum q = ENNReal.ofReal (cubeTsum q) := by
  have hterm : ∀ U ∈ Finset.powersetCard (m + 2) Finset.univ,
      volume (convexHull ℝ ((fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
          (U : Set (Fin (m + 1) → Fin 2))))
        * ∏ v ∈ U, ENNReal.ofReal (q v)
      = ENNReal.ofReal (cubeVol U * ∏ v ∈ U, q v) :=
    fun U _ => vertTerm_eq_ofReal q hq_nonneg U
  rw [vertTSum, Finset.sum_congr rfl hterm, cubeTsum,
    ENNReal.ofReal_sum_of_nonneg]
  intro U _
  exact mul_nonneg (cubeVol_nonneg U)
    (Finset.prod_nonneg (fun v _ => hq_nonneg v))

/-- Coordinate means lie in `[0,1]`. -/
public theorem vertMean_nonneg (hq_nonneg : ∀ v, 0 ≤ q v) (j : Fin (m + 1)) :
    0 ≤ vertMean q j := by
  simp only [vertMean]
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (hq_nonneg v) (Nat.cast_nonneg _)

public theorem vertMean_le_one (hq_nonneg : ∀ v, 0 ≤ q v)
    (hq_sum : ∑ v, q v = 1) (j : Fin (m + 1)) :
    vertMean q j ≤ 1 := by
  have hbit : ∀ v : Fin (m + 1) → Fin 2, (((v j : Fin 2)) : ℝ) ≤ 1 := by
    intro v
    have h2 : (v j).val ≤ 1 := by
      have hlt : (v j).val < 2 := (v j).isLt
      omega
    calc (((v j : Fin 2)) : ℝ) = (((v j).val : ℕ) : ℝ) := by simp
      _ ≤ ((1 : ℕ) : ℝ) := Nat.cast_le.mpr h2
      _ = 1 := Nat.cast_one
  calc vertMean q j = ∑ v, q v * (((v j : Fin 2)) : ℝ) := rfl
    _ ≤ ∑ v, q v := Finset.sum_le_sum (fun v _ =>
      mul_le_of_le_one_right (hq_nonneg v) (hbit v))
    _ = 1 := hq_sum

/-- Gap factors are nonnegative. -/
public theorem gapFactor_nonneg (hq_nonneg : ∀ v, 0 ≤ q v)
    (hq_sum : ∑ v, q v = 1) (j : Fin (m + 1)) :
    0 ≤ 2 * vertMean q j * (1 - vertMean q j) := by
  have h0 := vertMean_nonneg q hq_nonneg j
  have h1 := vertMean_le_one q hq_nonneg hq_sum j
  have : 0 ≤ (2 : ℝ) * vertMean q j := by positivity
  have hsub : 0 ≤ 1 - vertMean q j := by linarith
  calc (0 : ℝ) ≤ (2 * vertMean q j) * (1 - vertMean q j) :=
        mul_nonneg this hsub
    _ = 2 * vertMean q j * (1 - vertMean q j) := by ring

/-- HI-CUBE: probability-weighted hypercube inequality (Cor 9.1). -/
public theorem cube_prob_weighted (hq_nonneg : ∀ v, 0 ≤ q v)
    (hq_sum : ∑ v, q v = 1) :
    cubeTsum q
    ≤ (∏ j : Fin (m + 1), vertMean q j * (1 - vertMean q j))
      / (((m + 1)! : ℕ) : ℝ) := by
  have hmain := cube_main_inequality q hq_nonneg hq_sum
  rw [vertS_eq_tsum q hq_nonneg, vertTSum_eq_ofReal q hq_nonneg] at hmain
  have hgap : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
      gap j (vertMeas q)
      = ENNReal.ofReal (2 * vertMean q j * (1 - vertMean q j)) :=
    fun j _ => gap_vertMeas_eq q j hq_nonneg hq_sum
  rw [Finset.prod_congr rfl hgap] at hmain
  have hLHS0 : (0 : ℝ) ≤ ((((m + 2)!) : ℕ) : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1))) := by positivity
  rw [← ENNReal.ofReal_natCast (((m + 2)!) : ℕ),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => gapFactor_nonneg q hq_nonneg hq_sum j),
    ← ENNReal.ofReal_mul hLHS0, ← ENNReal.ofReal_mul hC0] at hmain
  have hF1 : (0 : ℝ) < ((((m + 1)!) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hRHS0 : 0 ≤ (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ∏ j : Fin (m + 1), 2 * vertMean q j * (1 - vertMean q j) := by
    apply mul_nonneg _ (Finset.prod_nonneg (fun j _ =>
      gapFactor_nonneg q hq_nonneg hq_sum j))
    positivity
  rw [ENNReal.ofReal_le_ofReal_iff hRHS0] at hmain
  have hprod : (∏ j : Fin (m + 1), 2 * vertMean q j * (1 - vertMean q j))
      = (2 : ℝ) ^ (m + 1)
        * ∏ j : Fin (m + 1), vertMean q j * (1 - vertMean q j) := by
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
        2 * vertMean q j * (1 - vertMean q j)
        = 2 * (vertMean q j * (1 - vertMean q j)) := fun j _ => by ring
    rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib]
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfac : ((((m + 2)!) : ℕ) : ℝ)
      = (((m + 2 : ℕ)) : ℝ) * ((((m + 1)!) : ℕ) : ℝ) := by
    have h2 : m + 2 = (m + 1) + 1 := by ring
    rw [h2, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hC : (((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)))
      * ((2 : ℝ) ^ (m + 1)
        * ∏ j : Fin (m + 1), vertMean q j * (1 - vertMean q j))
      = (((m + 2 : ℕ)) : ℝ)
        * ∏ j : Fin (m + 1), vertMean q j * (1 - vertMean q j) := by
    field_simp
  rw [hprod, hfac, mul_assoc, hC] at hmain
  have hm2 : (0 : ℝ) < (((m + 2 : ℕ)) : ℝ) := by positivity
  have hcan := le_of_mul_le_mul_left hmain hm2
  rw [le_div_iff₀ hF1, mul_comm (cubeTsum q)]
  exact hcan

end ProbForm

section WeightForm

variable {m : ℕ} (x : (Fin (m + 1) → Fin 2) → ℝ)

/-- Total weight `Q`. -/
@[expose] public noncomputable def cubeQ : ℝ := ∑ v, x v

/-- Vertex fiber over bit `b` at coordinate `j` (a facet for fixed `j`). -/
@[expose] public noncomputable def vertFiber (j : Fin (m + 1)) (b : Fin 2) :
    Finset (Fin (m + 1) → Fin 2) :=
  Finset.univ.filter (fun v => v j = b)

/-- Facet sums `M_{j,b}`. -/
@[expose] public noncomputable def cubeM (j : Fin (m + 1)) (b : Fin 2) : ℝ :=
  ∑ v ∈ vertFiber j b, x v

/-- Normalized-volume polynomial `F(x)`. -/
@[expose] public noncomputable def cubeF : ℝ :=
  ∑ U ∈ Finset.powersetCard (m + 2) Finset.univ,
    ((((m + 1)!) : ℕ) : ℝ) * cubeVol U * ∏ v ∈ U, x v

/-- Opposite facet sums add to the total. -/
public theorem cubeM_add (j : Fin (m + 1)) :
    cubeM x j 0 + cubeM x j 1 = cubeQ x := by
  have hdisj : Disjoint
      (Finset.univ.filter (fun v : Fin (m + 1) → Fin 2 => v j = 0))
      (Finset.univ.filter (fun v : Fin (m + 1) → Fin 2 => v j = 1)) := by
    rw [Finset.disjoint_filter]
    intro v _ h0 h1
    rw [h0] at h1
    exact (by decide : (0 : Fin 2) ≠ 1) h1
  have hunion : Finset.univ.filter (fun v : Fin (m + 1) → Fin 2 => v j = 0)
        ∪ Finset.univ.filter (fun v : Fin (m + 1) → Fin 2 => v j = 1)
      = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fin2_dichotomy (v j)
  have hsum := Finset.sum_union (f := x) hdisj
  rw [hunion] at hsum
  simp only [cubeM, cubeQ, vertFiber]
  exact hsum.symm

/-- `F` factors through the probability `T`-sum. -/
public theorem cubeF_eq_factorial :
    cubeF x = ((((m + 1)!) : ℕ) : ℝ) * cubeTsum x := by
  simp only [cubeF, cubeTsum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U _ => by ring)

/-- HI-WCUBE: arbitrary-weight hypercube inequality (Cor 9.2). -/
public theorem weighted_cube (hx_nonneg : ∀ v, 0 ≤ x v) :
    cubeF x * (cubeQ x) ^ m
    ≤ ∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1 := by
  by_cases hQ : cubeQ x = 0
  · -- Zero case: all weights vanish, both sides are zero.
    have hx0 : ∀ v, x v = 0 := by
      simp only [cubeQ] at hQ
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => hx_nonneg v) (s := (Finset.univ :
          Finset (Fin (m + 1) → Fin 2))) (f := x)
      intro v
      exact (hiff.mp hQ) v (Finset.mem_univ v)
    have hM0 : ∀ (j : Fin (m + 1)) (b : Fin 2), cubeM x j b = 0 := by
      intro j b
      simp only [cubeM]
      exact Finset.sum_eq_zero (fun v _ => hx0 v)
    have hRHS0 : (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, Nat.zero_lt_succ m⟩ :
        Fin (m + 1)))
      simp [hM0]
    have hF0 : cubeF x = 0 := by
      simp only [cubeF]
      apply Finset.sum_eq_zero
      intro U hU
      have hc : U.card = m + 2 := (Finset.mem_powersetCard.mp hU).2
      have hne : U.Nonempty := by
        rw [← Finset.card_pos, hc]
        omega
      obtain ⟨v, hv⟩ := hne
      have hprod : ∏ v ∈ U, x v = 0 := Finset.prod_eq_zero hv (hx0 v)
      rw [hprod, mul_zero]
    rw [hF0, zero_mul, hRHS0]
  · -- Positive case: normalize to a probability and apply HI-CUBE.
    have hQpos : 0 < cubeQ x := by
      have hnn : 0 ≤ cubeQ x := by
        simp only [cubeQ]
        exact Finset.sum_nonneg (fun v _ => hx_nonneg v)
      exact lt_of_le_of_ne hnn (Ne.symm hQ)
    have hQne : cubeQ x ≠ 0 := ne_of_gt hQpos
    set q : (Fin (m + 1) → Fin 2) → ℝ := fun v => x v / cubeQ x with hqdef
    have hq_nonneg : ∀ v, 0 ≤ q v := by
      intro v
      simp only [hqdef]
      exact div_nonneg (hx_nonneg v) (le_of_lt hQpos)
    have hq_sum : (∑ v, q v) = 1 := by
      simp only [hqdef, div_eq_mul_inv, ← Finset.sum_mul]
      have hQQ : (∑ v, x v) = cubeQ x := rfl
      rw [hQQ]
      exact mul_inv_cancel₀ hQne
    have hcub := cube_prob_weighted q hq_nonneg hq_sum
    -- `T`-sum scaling.
    have hterm : ∀ U ∈ Finset.powersetCard (m + 2) Finset.univ,
        cubeVol U * ∏ v ∈ U, q v
        = (cubeVol U * ∏ v ∈ U, x v) / (cubeQ x) ^ (m + 2) := by
      intro U hU
      have hc : U.card = m + 2 := (Finset.mem_powersetCard.mp hU).2
      have hprod : (∏ v ∈ U, q v) = (∏ v ∈ U, x v) / (cubeQ x) ^ U.card := by
        simp only [hqdef, Finset.prod_div_distrib, Finset.prod_const]
      rw [hprod, hc]
      ring
    have hTsum : cubeTsum q = cubeTsum x / (cubeQ x) ^ (m + 2) := by
      calc cubeTsum q
          = ∑ U ∈ Finset.powersetCard (m + 2) Finset.univ,
            ((cubeVol U * ∏ v ∈ U, x v) / (cubeQ x) ^ (m + 2)) := by
              simp only [cubeTsum]
              exact Finset.sum_congr rfl hterm
        _ = cubeTsum x / (cubeQ x) ^ (m + 2) := by
              simp only [cubeTsum, div_eq_mul_inv, ← Finset.sum_mul]
    -- Means in terms of facet sums.
    have hbit : ∀ j : Fin (m + 1), ∀ v : Fin (m + 1) → Fin 2,
        (x v / cubeQ x) * (((v j : Fin 2)) : ℝ)
        = if v j = 1 then x v / cubeQ x else 0 := by
      intro j v
      rcases fin2_dichotomy (v j) with h | h
      · simp [h]
      · simp [h]
    have hmean1 : ∀ j : Fin (m + 1),
        vertMean q j = cubeM x j 1 / cubeQ x := by
      intro j
      simp only [vertMean, cubeM, vertFiber, hqdef]
      simp only [hbit j, ← Finset.sum_filter]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    have hmean0 : ∀ j : Fin (m + 1),
        1 - vertMean q j = cubeM x j 0 / cubeQ x := by
      intro j
      rw [hmean1 j]
      have hadd := cubeM_add x j
      field_simp
      linarith
    have hprod : (∏ j : Fin (m + 1), vertMean q j * (1 - vertMean q j))
        = (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1)
          / (cubeQ x) ^ (2 * (m + 1)) := by
      have hterm2 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
          vertMean q j * (1 - vertMean q j)
          = (cubeM x j 0 * cubeM x j 1) / (cubeQ x) ^ 2 := by
        intro j _
        rw [hmean0 j, hmean1 j, div_mul_div_comm, pow_two,
          mul_comm (cubeM x j 1) (cubeM x j 0)]
      rw [Finset.prod_congr rfl hterm2, Finset.prod_div_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [hTsum, hprod] at hcub
    have hF1pos : (0 : ℝ) < ((((m + 1)!) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hQpow1 : (0 : ℝ) < (cubeQ x) ^ (m + 2) := pow_pos hQpos _
    have hQpow2 : (0 : ℝ) < (cubeQ x) ^ (2 * (m + 1)) := pow_pos hQpos _
    have hpow : (cubeQ x) ^ (2 * (m + 1))
        = (cubeQ x) ^ (m + 2) * (cubeQ x) ^ m := by
      conv_lhs => rw [show 2 * (m + 1) = (m + 2) + m from by ring]
      rw [pow_add]
    rw [div_div, div_le_div_iff₀ hQpow1
      (mul_pos hQpow2 hF1pos)] at hcub
    rw [hpow] at hcub
    have hcan : cubeTsum x * ((cubeQ x) ^ m * ((((m + 1)!) : ℕ) : ℝ))
        ≤ (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1) := by
      have h2' : (cubeTsum x * ((cubeQ x) ^ m * ((((m + 1)!) : ℕ) : ℝ)))
          * (cubeQ x) ^ (m + 2)
          ≤ (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1)
            * (cubeQ x) ^ (m + 2) := by
        calc (cubeTsum x * ((cubeQ x) ^ m * ((((m + 1)!) : ℕ) : ℝ)))
              * (cubeQ x) ^ (m + 2)
            = cubeTsum x
              * (((cubeQ x) ^ (m + 2) * (cubeQ x) ^ m)
                * ((((m + 1)!) : ℕ) : ℝ)) := by ring
          _ ≤ (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1)
              * (cubeQ x) ^ (m + 2) := hcub
      exact le_of_mul_le_mul_right h2' hQpow1
    rw [cubeF_eq_factorial]
    calc ((((m + 1)!) : ℕ) : ℝ) * cubeTsum x * (cubeQ x) ^ m
        = cubeTsum x * ((cubeQ x) ^ m * ((((m + 1)!) : ℕ) : ℝ)) := by ring
      _ ≤ (∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1) := hcan

/-- Facet-product reindexing. -/
public theorem facet_prod_eq :
    (∏ s : Fin (m + 1) × Fin 2, cubeM x s.1 s.2)
    = ∏ j : Fin (m + 1), cubeM x j 0 * cubeM x j 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  exact Fin.prod_univ_two (fun b => cubeM x j b)

/-- HI-WCUBE in facet-product form. -/
public theorem weighted_cube_facet (hx_nonneg : ∀ v, 0 ≤ x v) :
    cubeF x * (cubeQ x) ^ m
    ≤ ∏ s : Fin (m + 1) × Fin 2, cubeM x s.1 s.2 := by
  rw [facet_prod_eq]
  exact weighted_cube x hx_nonneg

end WeightForm

end HypercubeInequality
