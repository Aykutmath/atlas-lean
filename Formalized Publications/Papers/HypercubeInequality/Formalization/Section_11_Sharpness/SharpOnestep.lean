module

/-
# Proposition 11.1, one-coordinate part: optimality of `(d+1)/(2d)`

The projected spike law is again a spike law in one dimension less:
pushing `vertMeas (sharpQ ε)` forward under `projDrop` merges the
last coordinate vertex with the origin.  Combined with the exact
formulas `sharpS_eq` and `sharpGap`, the one-coordinate ratio tends
to the one-coordinate constant as `ε → 0⁺`.  Hence no smaller
one-coordinate constant can hold (for `d ≥ 2`; dimension one is
equality with constant `1`).
-/

public import Section_7_Approximation.Approx
public import Section_9_Hypercube.Cube

namespace HypercubeInequality

open MeasureTheory Measure Finset Filter Topology
open scoped ENNReal NNReal BigOperators Nat

/-- The drop-last projection sends cube vertices to cube vertices. -/
public theorem projDrop_vertPt {n : ℕ} (v : Fin (n + 2) → Fin 2) :
    projDrop (vertPt v)
      = vertPt (Fin.init v) := by
  apply PiLp.ext
  intro t
  rfl

/-- Fiber weights of the projected vertex law. -/
@[expose] public noncomputable def projWgt {n : ℕ}
    (q : (Fin (n + 2) → Fin 2) → ℝ) (w : Fin (n + 1) → Fin 2) : ℝ :=
  q (Fin.snoc w 0) + q (Fin.snoc w 1)

/-- Pushforward of a vertex law under the drop-last projection. -/
public theorem map_projDrop_vertMeas {n : ℕ}
    (q : (Fin (n + 2) → Fin 2) → ℝ) (hq : ∀ v, 0 ≤ q v) :
    (vertMeas q).map (projDrop (m := n + 1)) = vertMeas (projWgt q) := by
  have hmap : ∀ (a : EuclideanSpace ℝ (Fin (n + 2))),
      (Measure.dirac a).map (projDrop (m := n + 1))
        = Measure.dirac (projDrop (m := n + 1) a) :=
    fun a => Measure.map_dirac a
  have hsum : ∀ (s : Finset (Fin (n + 2) → Fin 2))
      (f : (Fin (n + 2) → Fin 2) → Measure (EuclideanSpace ℝ (Fin (n + 2)))),
      (∑ v ∈ s, f v).map (projDrop (m := n + 1))
        = ∑ v ∈ s, (f v).map (projDrop (m := n + 1)) := by
    intro s f
    induction s using Finset.induction with
    | empty => simp [Measure.map_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Measure.map_add _ _ (measurable_projDrop (m := n + 1)), ih]
  have hequiv : ∀ (F : (Fin (n + 2) → Fin 2)
        → Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      (∑ v, F v) = ∑ w : Fin (n + 1) → Fin 2, ∑ b : Fin 2,
        F (Fin.snoc w b) := by
    intro F
    let e : (Fin (n + 2) → Fin 2) ≃ (Fin (n + 1) → Fin 2) × Fin 2 :=
      ⟨fun v => (fun t => v t.castSucc, v (Fin.last (n + 1))),
       fun p => Fin.snoc p.1 p.2,
       by
         intro v
         funext t
         rcases Fin.eq_castSucc_or_eq_last t with ⟨j, rfl⟩ | rfl
         · simp [Fin.snoc_castSucc]
         · simp [Fin.snoc_last],
       by
         intro p
         ext1
         · funext t
           simp [Fin.snoc_castSucc]
         · simp [Fin.snoc_last]⟩
    calc (∑ v, F v) = ∑ x : (Fin (n + 1) → Fin 2) × Fin 2, F (Fin.snoc x.1 x.2) :=
          (e.symm.sum_comp F).symm
      _ = ∑ w : Fin (n + 1) → Fin 2, ∑ b : Fin 2, F (Fin.snoc w b) :=
          Fintype.sum_prod_type _
  have hterm : ∀ v : Fin (n + 2) → Fin 2,
      (ENNReal.ofReal (q v) • Measure.dirac (vertPt v)).map (projDrop (m := n + 1))
        = ENNReal.ofReal (q v)
          • Measure.dirac (vertPt (Fin.init v)) := by
    intro v
    rw [Measure.map_smul _ (measurable_projDrop (m := n + 1)).aemeasurable,
      hmap, projDrop_vertPt]
  calc (vertMeas q).map (projDrop (m := n + 1))
      = ∑ v, (ENNReal.ofReal (q v) • Measure.dirac (vertPt v)).map
          (projDrop (m := n + 1)) := by
        rw [vertMeas, hsum]
    _ = ∑ v, ENNReal.ofReal (q v)
          • Measure.dirac (vertPt (Fin.init v)) :=
        Finset.sum_congr rfl (fun v _ => hterm v)
    _ = ∑ w : Fin (n + 1) → Fin 2, ∑ b : Fin 2,
          ENNReal.ofReal (q (Fin.snoc w b)) • Measure.dirac (vertPt w) := by
        exact (hequiv (fun v => ENNReal.ofReal (q v)
          • Measure.dirac (vertPt (Fin.init v)))).trans (by
          apply Finset.sum_congr rfl
          intro w _
          apply Finset.sum_congr rfl
          intro b _
          simp only [Fin.init_snoc])
    _ = ∑ w : Fin (n + 1) → Fin 2,
          ENNReal.ofReal (projWgt q w) • Measure.dirac (vertPt w) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Fin.sum_univ_two, projWgt, ENNReal.ofReal_add (hq _) (hq _),
          ← add_smul]
    _ = vertMeas (projWgt q) := rfl

/-- `snoc` injectivity in both components. -/
public theorem snoc_inj {n : ℕ} {w w' : Fin (n + 1) → Fin 2} {b b' : Fin 2}
    (h : Fin.snoc (α := fun _ => Fin 2) w b = Fin.snoc (α := fun _ => Fin 2) w' b') : w = w' ∧ b = b' := by
  constructor
  · have := congrFun h
    funext t
    have ht := this t.castSucc
    simpa [Fin.snoc_castSucc] using ht
  · have ht := congrFun h (Fin.last (n + 1))
    simpa [Fin.snoc_last] using ht

/-- Appending `0` to a coordinate vertex gives the lifted vertex. -/
public theorem snoc_sharpVert_castSucc {n : ℕ} (t : Fin (n + 1)) :
    Fin.snoc (sharpVert t) 0 = sharpVert (t.castSucc) := by
  funext s
  rcases Fin.eq_castSucc_or_eq_last s with ⟨u, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    simp [sharpVert, Pi.single_apply, Fin.castSucc_inj]
  · rw [Fin.snoc_last]
    simp [sharpVert, Fin.ne_of_lt (Fin.castSucc_lt_last t)]

/-- Appending `1` to the origin gives the last coordinate vertex. -/
public theorem snoc_zero_one {n : ℕ} :
    Fin.snoc (0 : Fin (n + 1) → Fin 2) 1 = sharpVert (Fin.last (n + 1)) := by
  funext s
  rcases Fin.eq_castSucc_or_eq_last s with ⟨u, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    simp [sharpVert, Fin.ne_of_lt (Fin.castSucc_lt_last u)]
  · rw [Fin.snoc_last]
    simp [sharpVert]

/-- Appending `0` to the origin gives the origin. -/
public theorem snoc_zero_zero {n : ℕ} :
    Fin.snoc (0 : Fin (n + 1) → Fin 2) 0 = (0 : Fin (n + 2) → Fin 2) := by
  funext s
  rcases Fin.eq_castSucc_or_eq_last s with ⟨u, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]; rfl
  · rw [Fin.snoc_last]; rfl

/-- The projected spike weights are the spike weights one dimension down. -/
public theorem projWgt_sharpQ {n : ℕ} (ε : ℝ) (w : Fin (n + 1) → Fin 2) :
    projWgt (sharpQ (m := n + 1) ε) w = sharpQ (m := n) ε w := by
  have hQ0 : ∀ b : Fin 2, w ≠ 0 → sharpQ (m := n + 1) ε (Fin.snoc w b) ≠ 0 ∨ True := by
    intro b _; exact Or.inr trivial
  rw [projWgt]
  by_cases hw0 : w = 0
  · subst hw0
    rw [snoc_zero_zero, snoc_zero_one, sharpQ_zero, sharpQ_vert]
    rw [sharpQ_zero]
    push_cast
    ring
  · by_cases hwv : ∃ t : Fin (n + 1), w = sharpVert t
    · obtain ⟨t, rfl⟩ := hwv
      rw [snoc_sharpVert_castSucc, sharpQ_vert]
      have h1 : sharpQ (m := n + 1) ε (Fin.snoc (sharpVert t) 1) = 0 := by
        apply sharpQ_eq_zero_of_off
        · intro h
          have hb := congrFun h (Fin.last (n + 1))
          rw [Fin.snoc_last] at hb
          exact (by decide : (1 : Fin 2) ≠ 0) hb
        · intro j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨s, rfl⟩ | rfl
          · rw [← snoc_sharpVert_castSucc]
            intro h
            have h2 := (snoc_inj h).2
            exact (by decide : (1 : Fin 2) ≠ 0) h2
          · rw [← snoc_zero_one]
            intro h
            have h2 := (snoc_inj h).1
            exact sharpVert_ne_zero t h2
      rw [h1, add_zero, sharpQ_vert]
    · push Not at hwv
      have hgen : ∀ b : Fin 2, sharpQ (m := n + 1) ε (Fin.snoc w b) = 0 := by
        intro b
        apply sharpQ_eq_zero_of_off
        · intro h
          apply hw0
          funext t
          have ht := congrFun h t.castSucc
          rw [Fin.snoc_castSucc] at ht
          simpa using ht
        · intro j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨s, rfl⟩ | rfl
          · rw [← snoc_sharpVert_castSucc]
            intro h
            have ⟨h1, h2⟩ := snoc_inj h
            exact hwv s h1
          · rw [← snoc_zero_one]
            intro h
            have ⟨h1, h2⟩ := snoc_inj h
            exact hw0 h1
      rw [hgen 0, hgen 1, add_zero]
      exact (sharpQ_eq_zero_of_off ε w hw0 hwv).symm

/-- The projected spike law is the spike law one dimension down. -/
public theorem proj_spike {n : ℕ} (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : (((n + 1) + 1 : ℕ) : ℝ) * ε ≤ 1) :
    (vertMeas (sharpQ (m := n + 1) ε)).map (projDrop (m := n + 1))
      = vertMeas (sharpQ (m := n) ε) := by
  rw [map_projDrop_vertMeas _ (fun v => sharpQ_nonneg ε hε0 hε1 v)]
  congr 1
  funext w
  exact projWgt_sharpQ ε w

/-- The one-coordinate ratio factor `f(ε) = (1-(n+2)ε)/((1-ε)(1-(n+1)ε))`. -/
@[expose] public noncomputable def onestepFactor {n : ℕ} (ε : ℝ) : ℝ :=
  (1 - ((n + 2 : ℕ) : ℝ) * ε) / ((1 - ε) * (1 - ((n + 1 : ℕ) : ℝ) * ε))

public theorem onestepFactor_zero {n : ℕ} : onestepFactor (n := n) 0 = 1 := by
  simp [onestepFactor]

public theorem onestepFactor_continuous {n : ℕ} :
    ContinuousAt (onestepFactor (n := n)) 0 := by
  have hg : ContinuousAt (fun ε : ℝ => 1 - ((n + 2 : ℕ) : ℝ) * ε) 0 :=
    continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hh : ContinuousAt (fun ε : ℝ =>
      (1 - ε) * (1 - ((n + 1 : ℕ) : ℝ) * ε)) 0 :=
    (continuousAt_const.sub continuousAt_id).mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
  have hne : ((1 : ℝ) - 0) * (1 - ((n + 1 : ℕ) : ℝ) * 0) ≠ 0 := by norm_num
  show ContinuousAt
    (fun ε : ℝ => (1 - ((n + 2 : ℕ) : ℝ) * ε)
      / ((1 - ε) * (1 - ((n + 1 : ℕ) : ℝ) * ε))) 0
  exact hg.div hh hne

/-- Proposition 11.1 (one-coordinate part): optimality of the
one-coordinate constant `(n+3) / (2 * (n+2))` in dimension `n+2`. -/
public theorem sharp_onestep_optimal {n : ℕ} (c : ℝ)
    (hc : c < ((n + 3 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ))) :
    ∃ ε : ℝ, 0 < ε ∧ ((n + 2 : ℕ) : ℝ) * ε < 1 ∧
      ENNReal.ofReal c * gap (Fin.last (n + 1)) (vertMeas (sharpQ (m := n + 1) ε))
        * S (n + 1) ((vertMeas (sharpQ (m := n + 1) ε)).map (projDrop (m := n + 1)))
        < S (n + 2) (vertMeas (sharpQ (m := n + 1) ε)) := by
  have hC : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)) := by positivity
  have htf : Tendsto (onestepFactor (n := n)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 := (onestepFactor_continuous (n := n)).tendsto
    rw [onestepFactor_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hgt : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c / (((n + 3 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ)))
        < onestepFactor (n := n) ε :=
    (tendsto_order.1 htf).1 _ ((div_lt_one hC).mpr hc)
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / ((n + 2 : ℕ) : ℝ) := by
    have h01 : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := by positivity
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 / ((n + 2 : ℕ) : ℝ) :=
      eventually_lt_nhds h01
    exact hev.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    eventually_of_mem self_mem_nhdsWithin (fun ε hε => hε)
  obtain ⟨ε, hε0, hcc', hεbound⟩ := (hpos.and (hgt.and hbound)).exists
  have hε1 : ((n + 2 : ℕ) : ℝ) * ε < 1 := by
    have hmpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [lt_div_iff₀ hmpos] at hεbound
    rw [mul_comm]
    exact hεbound
  have hε1' : ε < 1 := by
    have hle : ((n + 1 : ℕ) : ℝ) * ε ≤ ((n + 2 : ℕ) : ℝ) * ε := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hε0)
      push_cast
      linarith
    have hεle : ε ≤ ((n + 1 : ℕ) : ℝ) * ε :=
      le_mul_of_one_le_left (le_of_lt hε0) (by push_cast; linarith)
    exact lt_of_le_of_lt hεle (lt_of_le_of_lt hle hε1)
  have h1ε : (0 : ℝ) < 1 - ε := sub_pos.mpr hε1'
  have h1ε1 : (0 : ℝ) < 1 - ((n + 1 : ℕ) : ℝ) * ε := by
    have hle : ((n + 1 : ℕ) : ℝ) * ε ≤ ((n + 2 : ℕ) : ℝ) * ε := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hε0)
      push_cast
      linarith
    linarith
  have hYpos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) * ε)
      * ε ^ (n + 2) := by
    apply mul_pos (mul_pos (by positivity) (sub_pos.mpr hε1)) (pow_pos hε0 _)
  have hkey : c * (2 * (1 - ε)) * (((n + 2 : ℕ) : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) * ε))
      < ((n + 3 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) * ε) := by
    have h1 : c < onestepFactor (n := n) ε
        * (((n + 3 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ))) :=
      (div_lt_iff₀ hC).mp hcc'
    have hP : (0 : ℝ) < 2 * ((n + 2 : ℕ) : ℝ) * (1 - ε)
        * (1 - ((n + 1 : ℕ) : ℝ) * ε) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (by positivity)) h1ε) h1ε1
    have h2 := mul_lt_mul_of_pos_right h1 hP
    have h3 : (onestepFactor (n := n) ε
          * (((n + 3 : ℕ) : ℝ) / (2 * ((n + 2 : ℕ) : ℝ))))
          * (2 * ((n + 2 : ℕ) : ℝ) * (1 - ε) * (1 - ((n + 1 : ℕ) : ℝ) * ε))
        = ((n + 3 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) * ε) := by
      rw [onestepFactor]
      field_simp [ne_of_gt h1ε, ne_of_gt h1ε1,
        mul_ne_zero (ne_of_gt h1ε) (ne_of_gt h1ε1),
        (show ((n + 2 : ℕ) : ℝ) ≠ 0 by positivity),
        (show (2 : ℝ) * ((n + 2 : ℕ) : ℝ) ≠ 0 by positivity)]
      rw [div_self (by rw [mul_comm]; exact ne_of_gt h1ε1)]
    rw [h3] at h2
    have h4 : c * (2 * ((n + 2 : ℕ) : ℝ) * (1 - ε) * (1 - ((n + 1 : ℕ) : ℝ) * ε))
        = c * (2 * (1 - ε)) * (((n + 2 : ℕ) : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) * ε)) := by
      ring
    rwa [h4] at h2
  have hreal : c * (2 * ε * (1 - ε))
        * (((n + 2 : ℕ) : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) * ε) * ε ^ (n + 1))
      < ((n + 3 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) * ε) * ε ^ (n + 2) := by
    have hmul := mul_lt_mul_of_pos_left hkey
      (mul_pos (pow_pos hε0 (n + 1)) hε0)
    convert hmul using 1 <;> ring
  refine ⟨ε, hε0, hε1, ?_⟩
  have hSν : S (n + 2) (vertMeas (sharpQ (m := n + 1) ε))
      = ENNReal.ofReal (((n + 3 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) * ε)
        * ε ^ (n + 2)) :=
    sharpS_eq ε (le_of_lt hε0) (le_of_lt hε1)
  have hSμ : S (n + 1) ((vertMeas (sharpQ (m := n + 1) ε)).map (projDrop (m := n + 1)))
      = ENNReal.ofReal (((n + 2 : ℕ) : ℝ) * (1 - ((n + 1 : ℕ) : ℝ) * ε)
        * ε ^ (n + 1)) := by
    rw [proj_spike ε (le_of_lt hε0) (le_of_lt hε1)]
    exact sharpS_eq ε (le_of_lt hε0) (by
      have hle : ((n + 1 : ℕ) : ℝ) * ε ≤ ((n + 2 : ℕ) : ℝ) * ε := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hε0)
        push_cast
        linarith
      exact le_of_lt (lt_of_le_of_lt hle hε1))
  have hD : gap (Fin.last (n + 1)) (vertMeas (sharpQ (m := n + 1) ε))
      = ENNReal.ofReal (2 * ε * (1 - ε)) :=
    sharpGap ε (le_of_lt hε0) (le_of_lt hε1) _
  rw [hSν, hSμ, hD]
  by_cases hc0 : 0 ≤ c
  · rw [← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_mul (mul_nonneg hc0 (by positivity : (0:ℝ) ≤ 2 * ε * (1 - ε)))]
    exact (ENNReal.ofReal_lt_ofReal_iff hYpos).mpr hreal
  · rw [not_le] at hc0
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hc0), zero_mul, zero_mul]
    exact ENNReal.ofReal_pos.mpr hYpos


end HypercubeInequality
