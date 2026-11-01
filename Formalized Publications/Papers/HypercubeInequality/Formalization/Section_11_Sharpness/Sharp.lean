module

/-
# Sharpness (HI-SHARP-RATIO, HI-SHARP, HI-SHARP-EQ)

Paper Section 10: optimality of the constant `(d+1)/2^d` via the extremizing
family (mass `1-dε` at the origin, `ε` at each coordinate vector), the exact
ratio identity, and the equality cases in dimensions one and two.
-/

public import Mathlib
public import Section_9_Hypercube.Cube

namespace HypercubeInequality

open MeasureTheory Measure Finset Filter
open scoped ENNReal NNReal BigOperators Nat Topology

section SharpFamily

variable {m : ℕ}

/-- `j`-th coordinate vertex. -/
@[expose] public noncomputable def sharpVert (j : Fin (m + 1)) :
    Fin (m + 1) → Fin 2 :=
  Pi.single j 1

public theorem sharpVert_ne_zero (j : Fin (m + 1)) : sharpVert j ≠ 0 := by
  intro h
  have hjj := congrFun h j
  simp only [sharpVert, Pi.single_eq_same, Pi.zero_apply] at hjj
  exact (by decide : (1 : Fin 2) ≠ 0) hjj

public theorem sharpVert_injective : Function.Injective (@sharpVert m) := by
  intro a b hab
  have h := congrFun hab a
  simp only [sharpVert, Pi.single_eq_same, Pi.single_apply] at h
  split_ifs at h with hcond
  · exact hcond
  · exact absurd h (by decide : (1 : Fin 2) ≠ 0)

/-- Extremizing weights: `1-dε` at the origin, `ε` at each coordinate vertex. -/
@[expose] public noncomputable def sharpQ (ε : ℝ) (v : Fin (m + 1) → Fin 2) : ℝ :=
  (if v = 0 then 1 - ((m + 1 : ℕ) : ℝ) * ε else 0)
    + ∑ j : Fin (m + 1), (if v = sharpVert j then ε else 0)

public theorem sharpQ_zero (ε : ℝ) :
    sharpQ ε (0 : Fin (m + 1) → Fin 2) = 1 - ((m + 1 : ℕ) : ℝ) * ε := by
  have hsum : (∑ j : Fin (m + 1),
      (if (0 : Fin (m + 1) → Fin 2) = sharpVert j then ε else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (fun h => sharpVert_ne_zero j h.symm)
  simp only [sharpQ, ite_true, hsum, add_zero]

public theorem sharpQ_vert (ε : ℝ) (i : Fin (m + 1)) :
    sharpQ ε (sharpVert i) = ε := by
  have h2 : (∑ j : Fin (m + 1),
      (if sharpVert i = sharpVert j then ε else 0)) = ε := by
    trans (if sharpVert i = sharpVert i then ε else 0)
    · exact Finset.sum_eq_single i
        (fun j _ hji => ite_eq_right (fun h => hji (sharpVert_injective h).symm))
        (fun h => absurd (Finset.mem_univ i) h)
    · simp
  simp only [sharpQ]
  rw [ite_eq_right (sharpVert_ne_zero i), zero_add]
  exact h2

public theorem sharpQ_eq_zero_of_off (ε : ℝ) (v : Fin (m + 1) → Fin 2)
    (hv0 : v ≠ 0) (hve : ∀ j, v ≠ sharpVert j) :
    sharpQ ε v = 0 := by
  have hsum : (∑ j : Fin (m + 1), (if v = sharpVert j then ε else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (hve j)
  simp only [sharpQ]
  rw [ite_eq_right hv0, hsum, zero_add]

public theorem sharpQ_nonneg (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ((m + 1 : ℕ) : ℝ) * ε ≤ 1) (v : Fin (m + 1) → Fin 2) :
    0 ≤ sharpQ ε v := by
  simp only [sharpQ]
  apply add_nonneg _ (Finset.sum_nonneg (fun j _ => by split_ifs <;> linarith))
  split_ifs with h
  · linarith
  · exact le_refl 0

/-- Support of the extremizing family. -/
@[expose] public noncomputable def simplexFinset : Finset (Fin (m + 1) → Fin 2) :=
  insert (0 : Fin (m + 1) → Fin 2) (Finset.univ.image (@sharpVert m))

public theorem sharpVert_mem_image (j : Fin (m + 1)) :
    sharpVert j ∈ Finset.univ.image (@sharpVert m) := by
  exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

public theorem zero_not_mem_image :
    (0 : Fin (m + 1) → Fin 2) ∉ Finset.univ.image (@sharpVert m) := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  exact sharpVert_ne_zero j hj

public theorem simplexFinset_card : simplexFinset (m := m).card = m + 2 := by
  simp only [simplexFinset, Finset.card_insert_of_notMem zero_not_mem_image,
    Finset.card_image_of_injective _ sharpVert_injective, Finset.card_univ,
    Fintype.card_fin]

public theorem sharpQ_support (v : Fin (m + 1) → Fin 2)
    (hv : v ∈ simplexFinset (m := m)) :
    v = 0 ∨ ∃ j, v = sharpVert j := by
  simp only [simplexFinset, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, rfl⟩

public theorem sharpQ_eq_zero_of_not_mem (ε : ℝ) (v : Fin (m + 1) → Fin 2)
    (hv : v ∉ simplexFinset (m := m)) :
    sharpQ ε v = 0 := by
  apply sharpQ_eq_zero_of_off
  · intro h0
    apply hv
    simp only [simplexFinset, Finset.mem_insert]
    exact Or.inl h0
  · intro j hj
    apply hv
    simp only [simplexFinset, Finset.mem_insert]
    exact Or.inr (by
      rw [hj]
      exact sharpVert_mem_image j)

public theorem sharpQ_sum (ε : ℝ) :
    (∑ v : Fin (m + 1) → Fin 2, sharpQ ε v) = 1 := by
  have hsub : (∑ v ∈ simplexFinset (m := m), sharpQ ε v)
      = ∑ v ∈ (Finset.univ : Finset (Fin (m + 1) → Fin 2)), sharpQ ε v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact sharpQ_eq_zero_of_not_mem ε v hv
  have hsplit : (∑ v ∈ simplexFinset (m := m), sharpQ ε v)
      = sharpQ ε (0 : Fin (m + 1) → Fin 2) + ∑ j : Fin (m + 1), ε := by
    have hins : (∑ v ∈ simplexFinset (m := m), sharpQ ε v)
        = sharpQ ε (0 : Fin (m + 1) → Fin 2)
          + ∑ v ∈ Finset.univ.image (@sharpVert m), sharpQ ε v := by
      simp only [simplexFinset]
      exact Finset.sum_insert zero_not_mem_image
    have himg : (∑ v ∈ Finset.univ.image (@sharpVert m), sharpQ ε v)
        = ∑ j : Fin (m + 1), ε := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j _
        exact sharpQ_vert ε j
      · intro a _ b _ hab
        exact sharpVert_injective hab
    rw [hins, himg]
  rw [← hsub, hsplit, sharpQ_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Coordinate means of the extremizing family. -/
public theorem sharpMean (ε : ℝ) (j : Fin (m + 1)) :
    vertMean (sharpQ ε) j = ε := by
  have hbit0 : ((((0 : Fin (m + 1) → Fin 2) j : Fin 2)) : ℝ) = 0 := by
    simp
  have hbit1 : ∀ i : Fin (m + 1),
      ((((sharpVert i j : Fin 2))) : ℝ) = if j = i then 1 else 0 := by
    intro i
    simp only [sharpVert, Pi.single_apply]
    rw [apply_ite (fun b : Fin 2 => (b : ℝ))]
    simp
  have hsum1 : (∑ i : Fin (m + 1), ((((sharpVert i j : Fin 2))) : ℝ)) = 1 := by
    simp only [hbit1]
    trans (if j = j then (1 : ℝ) else 0)
    · exact Finset.sum_eq_single j
        (fun i _ hij => ite_eq_right (fun h => hij h.symm))
        (fun h => absurd (Finset.mem_univ j) h)
    · simp
  have hsub : (∑ v ∈ simplexFinset (m := m),
        sharpQ ε v * ((((v j : Fin 2))) : ℝ))
      = ∑ v, sharpQ ε v * ((((v j : Fin 2))) : ℝ) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [sharpQ_eq_zero_of_not_mem ε v hv, zero_mul]
  have hsplit : (∑ v ∈ simplexFinset (m := m),
        sharpQ ε v * ((((v j : Fin 2))) : ℝ)) = ε := by
    have hins : (∑ v ∈ simplexFinset (m := m),
          sharpQ ε v * ((((v j : Fin 2))) : ℝ))
        = sharpQ ε (0 : Fin (m + 1) → Fin 2) * ((((0 : Fin (m + 1) → Fin 2) j : Fin 2)) : ℝ)
          + ∑ v ∈ Finset.univ.image (@sharpVert m),
            sharpQ ε v * ((((v j : Fin 2))) : ℝ) := by
      simp only [simplexFinset]
      exact Finset.sum_insert zero_not_mem_image
    have himg : (∑ v ∈ Finset.univ.image (@sharpVert m),
          sharpQ ε v * ((((v j : Fin 2))) : ℝ))
        = ε * ∑ i : Fin (m + 1), ((((sharpVert i j : Fin 2))) : ℝ) := by
      rw [Finset.sum_image]
      · have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
            sharpQ ε (sharpVert i) * ((((sharpVert i j : Fin 2))) : ℝ)
            = ε * ((((sharpVert i j : Fin 2))) : ℝ) := by
          intro i _
          rw [sharpQ_vert]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      · intro a _ b _ hab
        exact sharpVert_injective hab
    rw [hins, himg, hsum1, hbit0, mul_one, mul_zero, zero_add]
  simp only [vertMean]
  rw [← hsub, hsplit]

/-- Gaps of the extremizing family. -/
public theorem sharpGap (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ((m + 1 : ℕ) : ℝ) * ε ≤ 1) (j : Fin (m + 1)) :
    gap j (vertMeas (sharpQ ε))
    = ENNReal.ofReal (2 * ε * (1 - ε)) := by
  rw [gap_vertMeas_eq _ j (sharpQ_nonneg ε hε0 hε1) (sharpQ_sum ε),
    sharpMean ε j]

end SharpFamily

section SharpVolume

variable {m : ℕ}

/-- Ordered enumeration of the simplex vertices. -/
@[expose] public noncomputable def sharpTuple : Fin (m + 1 + 1) →
    EuclideanSpace ℝ (Fin (m + 1)) :=
  Fin.cases (vertPt (0 : Fin (m + 1) → Fin 2))
    (fun s => vertPt (sharpVert s))

public theorem sharpRange :
    Set.range sharpTuple
    = (fun v : Fin (m + 1) → Fin 2 => vertPt v) ''
      (↑(simplexFinset (m := m)) : Set (Fin (m + 1) → Fin 2)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨r, rfl⟩ := hy
    refine Fin.cases ?_ ?_ r
    · simp only [sharpTuple, Fin.cases_zero]
      exact Set.mem_image_of_mem _
        (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
    · intro i
      simp only [sharpTuple, Fin.cases_succ]
      apply Set.mem_image_of_mem
      rw [Finset.mem_coe]
      simp only [simplexFinset, Finset.mem_insert]
      exact Or.inr (sharpVert_mem_image i)
  · intro hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hmem : w ∈ simplexFinset (m := m) := Finset.mem_coe.mp hw
    rcases sharpQ_support w hmem with rfl | ⟨s, rfl⟩
    · exact ⟨0, by simp only [sharpTuple, Fin.cases_zero]⟩
    · exact ⟨s.succ, by simp only [sharpTuple, Fin.cases_succ]⟩

/-- The difference matrix of the simplex tuple is the identity. -/
public theorem sharpDiff_eq_one : diffMatrix (sharpTuple (m := m)) = 1 := by
  ext s t
  simp only [diffMatrix, Matrix.of_apply, Matrix.one_apply]
  have hs : sharpTuple (m := m) s.succ = vertPt (sharpVert s) := by
    simp only [sharpTuple, Fin.cases_succ]
  have h0 : sharpTuple (m := m) 0 = vertPt (0 : Fin (m + 1) → Fin 2) := by
    simp only [sharpTuple, Fin.cases_zero]
  rw [hs, h0, vertPt_apply, vertPt_apply]
  have hz : ((((0 : Fin (m + 1) → Fin 2) t : Fin 2)) : ℝ) = 0 := by simp
  rw [hz, sub_zero]
  simp only [sharpVert, Pi.single_apply, apply_ite]
  simp only [fin2_cast_zero, fin2_cast_one]
  by_cases hst : s = t
  · simp [hst]
  · have hts : t ≠ s := fun h => hst h.symm
    simp [hst, hts]

/-- Volume of the standard simplex hull. -/
public theorem sharpVol :
    cubeVol (simplexFinset (m := m)) = 1 / ((((m + 1)!) : ℕ) : ℝ) := by
  have hsimDet : simDet (sharpTuple (m := m)) = 1 := by
    rw [simDet_eq_det_diffMatrix, sharpDiff_eq_one, Matrix.det_one]
  have hbridge :=
    abs_simDet_eq_volume_convexHull (k := m + 1) (sharpTuple (m := m))
  rw [hsimDet, abs_one, sharpRange,
    ← ENNReal.ofReal_natCast ((m + 1)!)] at hbridge
  have hF0 : (0 : ℝ) ≤ ((((m + 1)!) : ℕ) : ℝ) := by positivity
  have hcon := congrArg ENNReal.toReal hbridge
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hF0] at hcon
  have hFne : ((((m + 1)!) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))
  rw [eq_div_iff hFne]
  simp only [cubeVol]
  rw [mul_comm]
  exact hcon.symm

/-- `T`-sum of the extremizing family (single-term collapse). -/
public theorem sharpTsum (ε : ℝ) :
    cubeTsum (sharpQ (m := m) ε)
    = (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1)
      / ((((m + 1)!) : ℕ) : ℝ) := by
  have hmem : simplexFinset (m := m)
      ∈ Finset.powersetCard (m + 2) Finset.univ := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, simplexFinset_card⟩
  have hsingle : ∀ T ∈ Finset.powersetCard (m + 2) Finset.univ,
      T ≠ simplexFinset (m := m) →
      cubeVol T * ∏ v ∈ T, sharpQ ε v = 0 := by
    intro T hT hne
    have hcard : T.card = m + 2 := (Finset.mem_powersetCard.mp hT).2
    have hsub : ¬ T ⊆ simplexFinset (m := m) := by
      intro hs
      apply hne
      have hle : (simplexFinset (m := m)).card ≤ T.card := by
        rw [simplexFinset_card, hcard]
      exact Finset.eq_of_subset_of_card_le hs hle
    have hex : ∃ v ∈ T, v ∉ simplexFinset (m := m) := by
      rw [Finset.subset_iff] at hsub
      by_contra hc
      apply hsub
      intro v hvT
      by_contra hvS
      exact hc ⟨v, hvT, hvS⟩
    obtain ⟨v, hvT, hvS⟩ := hex
    have hq0 : sharpQ ε v = 0 := sharpQ_eq_zero_of_not_mem ε v hvS
    have hprod : ∏ v ∈ T, sharpQ ε v = 0 := Finset.prod_eq_zero hvT hq0
    rw [hprod, mul_zero]
  have hval : cubeVol (simplexFinset (m := m))
        * ∏ v ∈ simplexFinset (m := m), sharpQ ε v
      = (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1)
        / ((((m + 1)!) : ℕ) : ℝ) := by
    have hprod : (∏ v ∈ simplexFinset (m := m), sharpQ ε v)
        = (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1) := by
      have hins : (∏ v ∈ simplexFinset (m := m), sharpQ ε v)
          = sharpQ ε (0 : Fin (m + 1) → Fin 2)
            * ∏ v ∈ Finset.univ.image (@sharpVert m), sharpQ ε v := by
        simp only [simplexFinset]
        exact Finset.prod_insert zero_not_mem_image
      have himg : (∏ v ∈ Finset.univ.image (@sharpVert m), sharpQ ε v)
          = ε ^ (m + 1) := by
        rw [Finset.prod_image]
        · simp only [sharpQ_vert, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
        · intro a _ b _ hab
          exact sharpVert_injective hab
      rw [hins, himg, sharpQ_zero]
    rw [hprod, sharpVol]
    ring
  simp only [cubeTsum]
  rw [Finset.sum_eq_single (simplexFinset (m := m)) hsingle]
  · exact hval
  · intro hcon
    exact absurd hmem hcon

/-- `S` of the extremizing family. -/
public theorem sharpS_eq (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ((m + 1 : ℕ) : ℝ) * ε ≤ 1) :
    S (m + 1) (vertMeas (sharpQ ε))
    = ENNReal.ofReal (((m + 2 : ℕ) : ℝ) * (1 - ((m + 1 : ℕ) : ℝ) * ε)
      * ε ^ (m + 1)) := by
  have hnn := sharpQ_nonneg ε hε0 hε1
  rw [vertS_eq_tsum _ hnn, vertTSum_eq_ofReal _ hnn, sharpTsum ε,
    ← ENNReal.ofReal_natCast ((m + 2)!),
    ← ENNReal.ofReal_mul (by positivity :
      (0 : ℝ) ≤ ((((m + 2)!) : ℕ) : ℝ))]
  congr 1
  have hF1 : ((((m + 1)!) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))
  have hfac : ((((m + 2)!) : ℕ) : ℝ)
      = (((m + 2 : ℕ)) : ℝ) * ((((m + 1)!) : ℕ) : ℝ) := by
    have h2 : m + 2 = (m + 1) + 1 := by ring
    rw [h2, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hfac]
  field_simp

/-- HI-SHARP-RATIO: exact ratio identity for the extremizing family. -/
public theorem sharpRatio (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ((m + 1 : ℕ) : ℝ) * ε < 1) :
    (((m + 2 : ℕ) : ℝ) * (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1))
      / (2 * ε * (1 - ε)) ^ (m + 1)
    = (((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1))
      * ((1 - ((m + 1 : ℕ) : ℝ) * ε) / (1 - ε) ^ (m + 1)) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ m + 1 := Nat.le_add_left 1 m
    exact_mod_cast h1
  have hε1' : ε < 1 := by
    have hle := mul_le_mul_of_nonneg_left hm (le_of_lt hε0)
    have hlt : ε * ((m + 1 : ℕ) : ℝ) < 1 := by
      rw [mul_comm]
      exact hε1
    linarith
  have h1ε : (1 : ℝ) - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε1')
  have hD : 2 * ε * (1 - ε) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hεne) h1ε
  have hDd : (2 * ε * (1 - ε)) ^ (m + 1) ≠ 0 := pow_ne_zero _ hD
  have h1εd : ((1 : ℝ) - ε) ^ (m + 1) ≠ 0 := pow_ne_zero _ h1ε
  have h2d : (2 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hεd : ε ^ (m + 1) ≠ 0 := pow_ne_zero _ hεne
  have hexpand : (2 * ε * (1 - ε)) ^ (m + 1)
      = 2 ^ (m + 1) * ε ^ (m + 1) * (1 - ε) ^ (m + 1) := by
    rw [mul_pow, mul_pow]
  rw [hexpand]
  field_simp

end SharpVolume

section SharpOptimal

variable {m : ℕ}

/-- The ratio factor `f(ε) = (1-dε)/(1-ε)^d`. -/
@[expose] public noncomputable def sharpFactor (ε : ℝ) : ℝ :=
  (1 - ((m + 1 : ℕ) : ℝ) * ε) / (1 - ε) ^ (m + 1)

public theorem sharpFactor_zero : sharpFactor (m := m) 0 = 1 := by
  simp [sharpFactor]

public theorem sharpFactor_continuous :
    ContinuousAt (sharpFactor (m := m)) 0 := by
  have hg : ContinuousAt (fun ε : ℝ => 1 - ((m + 1 : ℕ) : ℝ) * ε) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hh : ContinuousAt (fun ε : ℝ => ((1 - ε) ^ (m + 1))) 0 :=
    (continuousAt_const.sub continuousAt_id).pow _
  have hne : ((1 : ℝ) - 0) ^ (m + 1) ≠ 0 := by simp
  show ContinuousAt
    (fun ε : ℝ => (1 - ((m + 1 : ℕ) : ℝ) * ε) / (1 - ε) ^ (m + 1)) 0
  exact hg.div hh hne

/-- HI-SHARP: optimality of `(d+1)/2^d` among vertex-supported laws. -/
public theorem sharp_optimal (c : ℝ)
    (hc : c < ((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1)) :
    ∃ (q : (Fin (m + 1) → Fin 2) → ℝ),
      (∀ v, 0 ≤ q v) ∧ (∑ v, q v) = 1 ∧
      ENNReal.ofReal c * ∏ j : Fin (m + 1), gap j (vertMeas q)
        < S (m + 1) (vertMeas q) := by
  have hC : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1) := by positivity
  have hcc : c / (((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1)) < 1 :=
    (div_lt_one hC).mpr hc
  have htf : Tendsto (sharpFactor (m := m)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 := (sharpFactor_continuous (m := m)).tendsto
    rw [sharpFactor_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hgt : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c / (((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1)) < sharpFactor (m := m) ε :=
    (tendsto_order.1 htf).1 _ hcc
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / ((m + 1 : ℕ) : ℝ) := by
    have h01 : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 / ((m + 1 : ℕ) : ℝ) :=
      eventually_lt_nhds h01
    exact hev.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    eventually_of_mem self_mem_nhdsWithin (fun ε hε => hε)
  obtain ⟨ε, hε0, hcc', hεbound⟩ := (hpos.and (hgt.and hbound)).exists
  have hε1 : ((m + 1 : ℕ) : ℝ) * ε < 1 := by
    have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [lt_div_iff₀ hmpos] at hεbound
    rw [mul_comm]
    exact hεbound
  have hε1' : ε < 1 := by
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      have h1 : 1 ≤ m + 1 := Nat.le_add_left 1 m
      exact_mod_cast h1
    have hle := mul_le_mul_of_nonneg_left hm (le_of_lt hε0)
    have hlt : ε * ((m + 1 : ℕ) : ℝ) < 1 := by
      rw [mul_comm]
      exact hε1
    linarith
  have hPpos : (0 : ℝ) < (2 * ε * (1 - ε)) ^ (m + 1) := by
    have h1ε : (0 : ℝ) < 1 - ε := sub_pos.mpr hε1'
    have hD : (0 : ℝ) < 2 * ε * (1 - ε) :=
      mul_pos (mul_pos (by norm_num) hε0) h1ε
    exact pow_pos hD _
  have hSpos : (0 : ℝ)
      < ((m + 2 : ℕ) : ℝ) * (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1) := by
    have h1 : (0 : ℝ) < 1 - ((m + 1 : ℕ) : ℝ) * ε := sub_pos.mpr hε1
    have h2 : (0 : ℝ) < ε ^ (m + 1) := pow_pos hε0 _
    have h3 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    exact mul_pos (mul_pos h3 h1) h2
  have hratio := sharpRatio ε hε0 hε1
  have hSeq : (((m + 2 : ℕ) : ℝ) * (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1))
      = (((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1)) * sharpFactor (m := m) ε
        * (2 * ε * (1 - ε)) ^ (m + 1) := by
    have hPne : (2 * ε * (1 - ε)) ^ (m + 1) ≠ 0 := ne_of_gt hPpos
    rw [div_eq_iff hPne] at hratio
    simp only [sharpFactor]
    rw [hratio]
  have hCf : c < (((m + 2 : ℕ) : ℝ) / 2 ^ (m + 1))
      * sharpFactor (m := m) ε := by
    have h := (div_lt_iff₀ hC).mp hcc'
    rw [mul_comm]
    exact h
  have hreal : c * (2 * ε * (1 - ε)) ^ (m + 1)
      < ((m + 2 : ℕ) : ℝ) * (1 - ((m + 1 : ℕ) : ℝ) * ε) * ε ^ (m + 1) := by
    rw [hSeq]
    exact mul_lt_mul_of_pos_right hCf hPpos
  refine ⟨sharpQ (m := m) ε, sharpQ_nonneg ε (le_of_lt hε0) (le_of_lt hε1),
    sharpQ_sum ε, ?_⟩
  have hS := sharpS_eq ε (le_of_lt hε0) (le_of_lt hε1)
  have hP : (∏ j : Fin (m + 1), gap j (vertMeas (sharpQ (m := m) ε)))
      = ENNReal.ofReal ((2 * ε * (1 - ε)) ^ (m + 1)) := by
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
        gap j (vertMeas (sharpQ (m := m) ε))
        = ENNReal.ofReal (2 * ε * (1 - ε)) :=
      fun j _ => sharpGap ε (le_of_lt hε0) (le_of_lt hε1) j
    rw [Finset.prod_congr rfl hterm, ← ENNReal.ofReal_prod_of_nonneg]
    · simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro j _
      have h1ε : (0 : ℝ) ≤ 1 - ε := sub_nonneg.mpr (le_of_lt hε1')
      exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hε0)) h1ε
  rw [hS, hP]
  by_cases hc0 : 0 ≤ c
  · rw [← ENNReal.ofReal_mul hc0]
    exact (ENNReal.ofReal_lt_ofReal_iff hSpos).mpr hreal
  · rw [not_le] at hc0
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hc0), zero_mul]
    exact ENNReal.ofReal_pos.mpr hSpos

end SharpOptimal

section SquareEq

/-- Uniform weights on the square. -/
@[expose] public noncomputable def squareQ : (Fin 2 → Fin 2) → ℝ := fun _ => 1 / 4

public theorem squareQ_nonneg (v : Fin 2 → Fin 2) : 0 ≤ squareQ v := by
  simp [squareQ]

public theorem squareQ_sum : (∑ v : Fin 2 → Fin 2, squareQ v) = 1 := by
  have hcard : Fintype.card (Fin 2 → Fin 2) = 4 := by decide
  simp only [squareQ, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  norm_num

public theorem squareMean (j : Fin 2) :
    vertMean (m := 1) squareQ j = 1 / 2 := by
  have hterm : ∀ v : Fin 2 → Fin 2,
      ((((v j : Fin 2))) : ℝ) = if v j = 1 then 1 else 0 := by
    intro v
    rcases fin2_dichotomy (v j) with h | h
    · simp [h]
    · simp [h]
  have hbit : (∑ v : Fin 2 → Fin 2, ((((v j : Fin 2))) : ℝ)) = 2 := by
    simp only [hterm, ← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_one]
    have hcard : (Finset.univ.filter
        (fun v : Fin 2 → Fin 2 => v j = 1)).card = 2 := by
      fin_cases j <;> decide
    rw [hcard]
    simp
  simp only [vertMean, squareQ]
  rw [← Finset.mul_sum, hbit]
  norm_num

public theorem squareGap (j : Fin 2) :
    gap j (vertMeas (m := 1) squareQ) = ENNReal.ofReal (1 / 2) := by
  rw [gap_vertMeas_eq _ j squareQ_nonneg squareQ_sum, squareMean j]
  congr 1
  norm_num

/-- The four 3-vertex subsets of the square. -/
@[expose] public noncomputable def sqT1 : Finset (Fin 2 → Fin 2) :=
  {![0, 1], ![1, 0], ![1, 1]}
@[expose] public noncomputable def sqT2 : Finset (Fin 2 → Fin 2) :=
  {![0, 0], ![1, 0], ![1, 1]}
@[expose] public noncomputable def sqT3 : Finset (Fin 2 → Fin 2) :=
  {![0, 0], ![0, 1], ![1, 1]}
@[expose] public noncomputable def sqT4 : Finset (Fin 2 → Fin 2) :=
  {![0, 0], ![0, 1], ![1, 0]}

public theorem sqEnum : Finset.powersetCard (1 + 2)
    (Finset.univ : Finset (Fin 2 → Fin 2)) = {sqT1, sqT2, sqT3, sqT4} := by
  decide

/-- Volume of a square triangle from an explicit ordered tuple. -/
public theorem cubeVol_sqT (T : Finset (Fin 2 → Fin 2))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (hrange : Set.range v
      = (fun v : Fin 2 → Fin 2 => vertPt (m := 1) v) '' (↑T : Set _))
    (hdet : |Matrix.det (diffMatrix (k := 2) v)| = 1) :
    cubeVol (m := 1) T = 1 / 2 := by
  have hbridge := abs_simDet_eq_volume_convexHull (k := 2) v
  rw [simDet_eq_det_diffMatrix (k := 2) v, hdet, hrange,
    ← ENNReal.ofReal_natCast (Nat.factorial 2)] at hbridge
  have hcon := congrArg ENNReal.toReal hbridge
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ (((Nat.factorial 2 : ℕ)) : ℝ))] at hcon
  have h2n : Nat.factorial 2 = 2 := by decide
  rw [h2n, Nat.cast_ofNat] at hcon
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [cubeVol]
  rw [mul_comm]
  exact hcon.symm

public theorem sqVol1 : cubeVol (m := 1) sqT1 = 1 / 2 := by
  apply cubeVol_sqT _ ![vertPt (m := 1) ![0, 1], vertPt (m := 1) ![1, 0],
    vertPt (m := 1) ![1, 1]]
  · ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, sqT1, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨![0, 1], Or.inl rfl, rfl⟩
      · exact ⟨![1, 0], Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨![1, 1], Or.inr (Or.inr rfl), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · have hM : diffMatrix (k := 2)
        (![vertPt (m := 1) ![0, 1], vertPt (m := 1) ![1, 0],
          vertPt (m := 1) ![1, 1]] : Fin 3 → EuclideanSpace ℝ (Fin 2))
        = !![1, -1; 1, 0] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp [diffMatrix, vertPt_apply, Matrix.of_apply]
    rw [hM, Matrix.det_fin_two_of]
    norm_num

public theorem sqVol2 : cubeVol (m := 1) sqT2 = 1 / 2 := by
  apply cubeVol_sqT _ ![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![1, 0],
    vertPt (m := 1) ![1, 1]]
  · ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, sqT2, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨![0, 0], Or.inl rfl, rfl⟩
      · exact ⟨![1, 0], Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨![1, 1], Or.inr (Or.inr rfl), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · have hM : diffMatrix (k := 2)
        (![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![1, 0],
          vertPt (m := 1) ![1, 1]] : Fin 3 → EuclideanSpace ℝ (Fin 2))
        = !![1, 0; 1, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp [diffMatrix, vertPt_apply, Matrix.of_apply]
    rw [hM, Matrix.det_fin_two_of]
    norm_num

public theorem sqVol3 : cubeVol (m := 1) sqT3 = 1 / 2 := by
  apply cubeVol_sqT _ ![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![0, 1],
    vertPt (m := 1) ![1, 1]]
  · ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, sqT3, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨![0, 0], Or.inl rfl, rfl⟩
      · exact ⟨![0, 1], Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨![1, 1], Or.inr (Or.inr rfl), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · have hM : diffMatrix (k := 2)
        (![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![0, 1],
          vertPt (m := 1) ![1, 1]] : Fin 3 → EuclideanSpace ℝ (Fin 2))
        = !![0, 1; 1, 1] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp [diffMatrix, vertPt_apply, Matrix.of_apply]
    rw [hM, Matrix.det_fin_two_of]
    norm_num

public theorem sqVol4 : cubeVol (m := 1) sqT4 = 1 / 2 := by
  apply cubeVol_sqT _ ![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![0, 1],
    vertPt (m := 1) ![1, 0]]
  · ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, sqT4, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      fin_cases r
      · exact ⟨![0, 0], Or.inl rfl, rfl⟩
      · exact ⟨![0, 1], Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨![1, 0], Or.inr (Or.inr rfl), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · have hM : diffMatrix (k := 2)
        (![vertPt (m := 1) ![0, 0], vertPt (m := 1) ![0, 1],
          vertPt (m := 1) ![1, 0]] : Fin 3 → EuclideanSpace ℝ (Fin 2))
        = !![0, 1; 1, 0] := by
      ext s t
      fin_cases s <;> fin_cases t <;> simp [diffMatrix, vertPt_apply, Matrix.of_apply]
    rw [hM, Matrix.det_fin_two_of]
    norm_num

/-- HI-SHARP-EQ (square): `S_2 = 3/16` for the uniform law. -/
public theorem squareS :
    S 2 (vertMeas (m := 1) squareQ) = ENNReal.ofReal (3 / 16) := by
  show S (1 + 1) (vertMeas (m := 1) squareQ) = ENNReal.ofReal (3 / 16)
  have hnn : ∀ v, 0 ≤ squareQ v := squareQ_nonneg
  rw [vertS_eq_tsum (m := 1) _ hnn, vertTSum_eq_ofReal (m := 1) _ hnn]
  have htsum : cubeTsum (m := 1) squareQ = 1 / 32 := by
    simp only [cubeTsum]
    rw [sqEnum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have hterm1 : cubeVol (m := 1) sqT1 * ∏ v ∈ sqT1, squareQ v
        = 1 / 2 * (1 / 64 : ℝ) := by
      rw [sqVol1]
      congr 1
      simp only [sqT1, squareQ]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      norm_num
    have hterm2 : cubeVol (m := 1) sqT2 * ∏ v ∈ sqT2, squareQ v
        = 1 / 2 * (1 / 64 : ℝ) := by
      rw [sqVol2]
      congr 1
      simp only [sqT2, squareQ]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      norm_num
    have hterm3 : cubeVol (m := 1) sqT3 * ∏ v ∈ sqT3, squareQ v
        = 1 / 2 * (1 / 64 : ℝ) := by
      rw [sqVol3]
      congr 1
      simp only [sqT3, squareQ]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      norm_num
    have hterm4 : cubeVol (m := 1) sqT4 * ∏ v ∈ sqT4, squareQ v
        = 1 / 2 * (1 / 64 : ℝ) := by
      rw [sqVol4]
      congr 1
      simp only [sqT4, squareQ]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      norm_num
    rw [hterm1, hterm2, hterm3, hterm4]
    norm_num
  rw [htsum, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity :
      (0 : ℝ) ≤ ((((1 + 2)! : ℕ)) : ℝ))]
  congr 1
  have hf : Nat.factorial (1 + 2) = 6 := by decide
  rw [hf]
  norm_num

end SquareEq

section OneDimEq

/-- 1-D volume identity: hull volume is segment length. -/
public theorem oneDim_vol (Z : Fin 2 → EuclideanSpace ℝ (Fin 1)) :
    volume (convexHull ℝ (Set.range Z))
    = ((‖Z 0 0 - Z 1 0‖₊ : ℝ≥0) : ℝ≥0∞) := by
  have hdet : simDet (k := 1) Z = Z 1 0 - Z 0 0 := by
    rw [simDet_eq_det_diffMatrix (k := 1) Z, Matrix.det_fin_one]
    simp [diffMatrix, Matrix.of_apply, Fin.succ_zero_eq_one]
  have hbridge := abs_simDet_eq_volume_convexHull (k := 1) Z
  rw [hdet] at hbridge
  have h1f : Nat.factorial 1 = 1 := by decide
  have hcoe : (((‖Z 0 0 - Z 1 0‖₊ : ℝ≥0)) : ℝ≥0∞)
      = ENNReal.ofReal |Z 1 0 - Z 0 0| := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs,
      abs_sub_comm]
  rw [hcoe]
  have h1fc : ((Nat.factorial 1 : ℕ) : ℝ≥0∞) = 1 := by simp [h1f]
  rw [h1fc, one_mul] at hbridge
  exact hbridge.symm

/-- HI-SHARP-EQ (d=1): equality holds for every σ-finite law in dimension one. -/
public theorem oneDimS_eq_gap (ν : Measure (EuclideanSpace ℝ (Fin 1)))
    [SigmaFinite ν] (j : Fin 1) :
    S 1 ν = gap j ν := by
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  have hS : S 1 ν = ∫⁻ Z : Fin 2 → EuclideanSpace ℝ (Fin 1),
      volume (convexHull ℝ (Set.range Z))
      ∂(Measure.pi (fun _ : Fin 2 => ν)) := rfl
  have hmp := measurePreserving_piFinTwo (μ := fun _ : Fin 2 => ν)
  have hcomp := hmp.lintegral_comp (measurable_gap_integrand (0 : Fin 1))
  rw [hS]
  simp only [gap]
  rw [← hcomp]
  apply lintegral_congr_ae
  filter_upwards with Z
  simp only [MeasurableEquiv.piFinTwo_apply]
  exact oneDim_vol Z

end OneDimEq

end HypercubeInequality
