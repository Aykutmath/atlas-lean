module

/-
# Proposition 12.1 for arbitrary coordinate subsets

For `f : Fin k → Fin d`, `coordMap f` selects the coordinates `f t`
of a point of `ℝ^d`.  The law of the coordinates indexed by a finset
`I ⊆ Fin d` (listed increasingly) is `subsetLaw ν I`, and
`subsetRatioSet ν I` is its normalized ratio.  This module proves:

* coordinate maps preserve gaps and finite moments;
* the simplex functional, hence the normalized ratio, is invariant
  under coordinate permutations (via the determinant integral);
* deleting any single coordinate cannot increase the ratio
  (permutation + the proved drop-last deletion step);
* by iteration, `0 ≤ R_I(ν) ≤ R_J(ν) ≤ 1` for nonempty `J ⊆ I`,
  with `R_{ {j} }(ν) = 1`.
-/

public import Section_12_Ratios.Ratios
public import Section_3_LocalEstimate.Local

namespace HypercubeInequality

open MeasureTheory Measure Finset Filter Topology
open scoped ENNReal NNReal BigOperators Nat

/-- Coordinate-selection map: `(coordMap f x) t = x (f t)`. -/
@[expose] public noncomputable def coordMap {d k : ℕ} (f : Fin k → Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun t => x (f t))

public theorem coordMap_apply {d k : ℕ} (f : Fin k → Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (t : Fin k) :
    coordMap f x t = x (f t) := rfl

public theorem measurable_coordMap {d k : ℕ} (f : Fin k → Fin d) :
    Measurable (coordMap f) := by
  have h : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      fun t : Fin k => x (f t)) :=
    Measurable.of_eval fun t => measurable_coord (f t)
  have ho : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    WithLp.measurable_toLp 2 (Fin k → ℝ)
  exact ho.comp h

/-- Probability laws map to probability laws under coordinate selection. -/
public theorem isProbabilityMeasure_map_coordMap {d k : ℕ} (f : Fin k → Fin d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (coordMap f)) := ⟨by
  simp only [Measure.map_apply (measurable_coordMap f) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]⟩

/-- Gaps of a coordinate-selected law are the corresponding gaps. -/
public theorem gap_coordMap {d k : ℕ} (f : Fin k → Fin d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [SFinite ν] (j : Fin k) :
    gap j (ν.map (coordMap f)) = gap (f j) ν := by
  have hmap : Measurable (Prod.map (coordMap f) (coordMap f) :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → _) :=
    (measurable_coordMap f).prodMap (measurable_coordMap f)
  simp only [gap]
  rw [map_prod_map _ _ (measurable_coordMap f) (measurable_coordMap f),
    lintegral_map (measurable_gap_integrand j) hmap]
  apply lintegral_congr_ae
  filter_upwards with p
  simp only [Prod.map_fst, Prod.map_snd, coordMap_apply]

/-- Finite moments transfer to coordinate-selected laws. -/
public theorem moment_coordMap {d k : ℕ} (f : Fin k → Fin d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (j : Fin k) :
    (∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.map (coordMap f)))
      = ∫⁻ x, ((‖x (f j)‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin k) =>
      ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (measurable_coord j).nnnorm
  rw [lintegral_map hmeas (measurable_coordMap f)]
  apply lintegral_congr_ae
  filter_upwards with x
  rw [coordMap_apply]

/-- Determinant measurability (via the permutation expansion). -/
public theorem measurable_simDet_fn {k : ℕ} :
    Measurable (fun Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k) => simDet Z) := by
  have hentry : Measurable (fun Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k) =>
      (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Z r j) c) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) := by
    apply Measurable.of_eval
    intro r
    apply Measurable.of_eval
    intro c
    induction c using Fin.cases with
    | zero =>
      simp only []
      exact measurable_const
    | succ j =>
      simp only []
      exact (measurable_coord j).comp (measurable_pi_apply r)
  have hdet : Measurable (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ =>
      M.det) := by
    simp only [Matrix.det_apply]
    measurability
  exact hdet.comp hentry

/-- The simplex functional as a determinant integral. -/
public theorem S_eq_detint (k : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) :
    S k ν = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ Z, ENNReal.ofReal |simDet Z|
      ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  have hfact0 : (((k ! : ℕ)) : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.ofReal_natCast, ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos k))
  have hfactt : (((k ! : ℕ)) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hpt : ∀ Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k),
      volume (convexHull ℝ (Set.range Z))
        = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ENNReal.ofReal |simDet Z| := by
    intro Z
    have hbr := abs_simDet_eq_volume_convexHull (k := k) Z
    calc volume (convexHull ℝ (Set.range Z))
        = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ((((k ! : ℕ)) : ℝ≥0∞)
          * volume (convexHull ℝ (Set.range Z))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hfact0 hfactt, one_mul]
      _ = ((k ! : ℕ) : ℝ≥0∞)⁻¹ * ENNReal.ofReal |simDet Z| := by
          congr 1
          exact hbr.symm
  have hmeas : Measurable (fun Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet Z|) :=
    ENNReal.measurable_ofReal.comp (measurable_simDet_fn).abs
  unfold S
  simp only [hpt]
  exact lintegral_const_mul _ hmeas

/-- Lift a coordinate permutation on `Fin k` to `Fin (k + 1)`, fixing `0`. -/
@[expose] public def permSuccEquiv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) where
  toFun c := Fin.cases 0 (fun j => (σ j).succ) c
  invFun c := Fin.cases 0 (fun j => (σ.symm j).succ) c
  left_inv c := by
    induction c using Fin.cases with
    | zero => rfl
    | succ j => simp [Fin.cases_succ]
  right_inv c := by
    induction c using Fin.cases with
    | zero => rfl
    | succ j => simp [Fin.cases_succ]

/-- Permuting coordinates does not change `|simDet|`. -/
public theorem abs_simDet_coordMap {k : ℕ} (σ : Equiv.Perm (Fin k))
    (Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k)) :
    |simDet (fun r => coordMap (⇑σ) (Z r))| = |simDet Z| := by
  have hmat : (Matrix.of (fun r c => Fin.cases (1 : ℝ)
        (fun j => coordMap (⇑σ) (Z r) j) c) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
      = (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Z r j) c)).submatrix
          id (permSuccEquiv σ) := by
    ext r c
    induction c using Fin.cases with
    | zero => simp [Matrix.submatrix, permSuccEquiv, Fin.cases_zero]
    | succ j =>
      simp [Matrix.submatrix, permSuccEquiv, Fin.cases_succ, coordMap_apply]
  have hdet : (Matrix.of (fun r c => Fin.cases (1 : ℝ)
        (fun j => coordMap (⇑σ) (Z r) j) c) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det
      = ((Equiv.Perm.sign (permSuccEquiv σ) : ℤ) : ℝ)
        * (Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Z r j) c)).det := by
    rw [hmat, ← Matrix.det_transpose,
      Matrix.transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]
  have hsign : |((Equiv.Perm.sign (permSuccEquiv σ) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (permSuccEquiv σ)) with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  calc |simDet (fun r => coordMap (⇑σ) (Z r))|
      = |(Matrix.of (fun r c => Fin.cases (1 : ℝ)
          (fun j => coordMap (⇑σ) (Z r) j) c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det| := rfl
    _ = |simDet Z| := by
        rw [hdet, abs_mul, hsign, one_mul]
        rfl

/-- The simplex functional is invariant under coordinate permutations. -/
public theorem S_coordMap_perm {k : ℕ} (σ : Equiv.Perm (Fin k))
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] :
    S k (ν.map (coordMap (⇑σ))) = S k ν := by
  have : IsProbabilityMeasure (ν.map (coordMap (⇑σ))) :=
    isProbabilityMeasure_map_coordMap _ _
  have hpi : Measure.pi (fun _ : Fin (k + 1) => ν.map (coordMap (⇑σ)))
      = (Measure.pi (fun _ : Fin (k + 1) => ν)).map
        (fun Z r => coordMap (⇑σ) (Z r)) := by
    have h := Measure.pi_map_pi (μ := fun _ : Fin (k + 1) => ν)
      (f := fun _ => coordMap (⇑σ))
      (fun i => (measurable_coordMap _).aemeasurable)
    exact h.symm
  have hmeas : Measurable (fun Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal |simDet Z|) :=
    ENNReal.measurable_ofReal.comp (measurable_simDet_fn).abs
  have hT : Measurable (fun Z : Fin (k + 1) → EuclideanSpace ℝ (Fin k) =>
      (fun r => coordMap (⇑σ) (Z r))) :=
    Measurable.of_eval fun r => (measurable_coordMap _).comp (measurable_pi_apply r)
  rw [S_eq_detint, S_eq_detint, hpi, lintegral_map hmeas hT]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with Z
  rw [abs_simDet_coordMap]

/-- The normalized ratio is invariant under coordinate permutations. -/
public theorem subsetRatio_coordMap_perm {k : ℕ} (σ : Equiv.Perm (Fin k))
    (ν : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure ν] :
    subsetRatio k (ν.map (coordMap (⇑σ))) = subsetRatio k ν := by
  have hprod : (∏ j : Fin k, gap j (ν.map (coordMap (⇑σ))))
      = ∏ j : Fin k, gap j ν := by
    rw [← Equiv.prod_comp σ (fun j => gap j ν)]
    exact Finset.prod_congr rfl (fun j _ => gap_coordMap _ _ _)
  unfold subsetRatio
  rw [S_coordMap_perm, hprod]


/-- Law of the coordinates indexed by `I`, listed in increasing order. -/
@[expose] public noncomputable def subsetLaw {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin I.card)) :=
  ν.map (coordMap ⇑(I.orderEmbOfFin rfl))

/-- Normalized ratio of the coordinate projection onto `I`. -/
@[expose] public noncomputable def subsetRatioSet {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin d)) : ℝ≥0∞ :=
  subsetRatio I.card (subsetLaw ν I)

/-- The subset ratio depends only on the range of an enumeration:
any two injective enumerations of the same coordinates give the
same ratio (they differ by a coordinate permutation). -/
public theorem subsetRatio_coordMap_range_eq {d k : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    {f g : Fin k → Fin d} (hf : Function.Injective f) (_hg : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    subsetRatio k (ν.map (coordMap f)) = subsetRatio k (ν.map (coordMap g)) := by
  have hτ : ∀ t : Fin k, ∃ s : Fin k, g s = f t := by
    intro t
    have : f t ∈ Set.range g := hrange ▸ Set.mem_range_self t
    exact this
  choose τ hτ using hτ
  have hτinj : Function.Injective τ := by
    intro a b hab
    apply hf
    rw [← hτ a, ← hτ b, hab]
  have hτbij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτinj
  let τe : Equiv.Perm (Fin k) := Equiv.ofBijective τ hτbij
  have hfun : coordMap f = coordMap (⇑τe) ∘ coordMap g := by
    funext x
    apply PiLp.ext
    intro t
    show x (f t) = x (g (τe t))
    rw [← hτ t]
    rfl
  have hprob : IsProbabilityMeasure (ν.map (coordMap g)) :=
    isProbabilityMeasure_map_coordMap _ _
  calc subsetRatio k (ν.map (coordMap f))
      = subsetRatio k ((ν.map (coordMap g)).map (coordMap (⇑τe))) := by
        rw [hfun, Measure.map_map (measurable_coordMap _) (measurable_coordMap _)]
    _ = subsetRatio k (ν.map (coordMap g)) :=
        subsetRatio_coordMap_perm τe _

/-- The subset ratio for any injective enumeration of `I`. -/
public theorem subsetRatioSet_eq {d k : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (I : Finset (Fin d)) {e : Fin k → Fin d} (he : Function.Injective e)
    (hrange : Set.range e = ↑I) :
    subsetRatioSet ν I = subsetRatio k (ν.map (coordMap e)) := by
  have hcard : I.card = k := by
    have e1 : Fin k ≃ Set.range e := Equiv.ofInjective e he
    have h1 : Fintype.card (Set.range e) = k :=
      (Fintype.card_congr e1.symm).trans (Fintype.card_fin k)
    have h2 : (Set.range e).toFinset.card = k := by
      rw [Set.toFinset_card]
      exact h1
    have hfin : (Set.range e).toFinset = I := by
      ext y
      simp only [Set.mem_toFinset, hrange, Finset.mem_coe]
    rw [hfin] at h2
    exact h2
  subst hcard
  exact subsetRatio_coordMap_range_eq ν
    (I.orderEmbOfFin rfl).injective he
    ((Finset.range_orderEmbOfFin I rfl).trans hrange.symm)

/-- Deleting one coordinate cannot increase the subset ratio. -/
public theorem subsetRatioSet_erase_le {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0)
    (I : Finset (Fin d)) (a : Fin d) (ha : a ∈ I) :
    subsetRatioSet ν I ≤ subsetRatioSet ν (I.erase a) := by
  obtain ⟨k, hk⟩ : ∃ k, I.card = k + 1 :=
    ⟨I.card - 1, (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a, ha⟩)).symm⟩
  set e : Fin (k + 1) ↪o Fin d := I.orderEmbOfFin hk with he
  have herange : Set.range ⇑e = ↑I := Finset.range_orderEmbOfFin I hk
  obtain ⟨p, hp⟩ : ∃ p : Fin (k + 1), e p = a := by
    have : a ∈ Set.range ⇑e := herange ▸ Finset.mem_coe.mpr ha
    exact this
  set σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap p (Fin.last k) with hσ
  set νe : Measure (EuclideanSpace ℝ (Fin (k + 1))) :=
    ν.map (coordMap ⇑e) with hνe
  have hprob : IsProbabilityMeasure νe := isProbabilityMeasure_map_coordMap _ _
  have hmom_e : ∀ j : Fin (k + 1),
      ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂νe ≠ ∞ := by
    intro j
    rw [hνe, moment_coordMap]
    exact hmom _
  have hpos_e : ∀ j : Fin (k + 1), gap j νe ≠ 0 := by
    intro j
    rw [hνe, gap_coordMap]
    exact hpos _
  have hprob2 : IsProbabilityMeasure (νe.map (coordMap ⇑σ)) :=
    isProbabilityMeasure_map_coordMap _ _
  have hmom2 : ∀ j : Fin (k + 1),
      ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(νe.map (coordMap ⇑σ)) ≠ ∞ := by
    intro j
    rw [moment_coordMap]
    exact hmom_e _
  have hpos2 : ∀ j : Fin (k + 1), gap j (νe.map (coordMap ⇑σ)) ≠ 0 := by
    intro j
    rw [gap_coordMap]
    exact hpos_e _
  set e'' : Fin k → Fin d := fun t => e (σ t.castSucc) with he''
  have he''inj : Function.Injective e'' :=
    e.injective.comp ((EquivLike.injective σ).comp (Fin.castSucc_injective k))
  have hfun : projDrop (m := k) ∘ coordMap ⇑σ ∘ coordMap ⇑e
      = coordMap e'' := by
    funext x
    apply PiLp.ext
    intro t
    rfl
  have hrange'' : Set.range e'' = ↑(I.erase a) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      have hne : σ t.castSucc ≠ p := by
        intro hcon
        have h1 : t.castSucc = Fin.last k := by
          calc t.castSucc = σ (σ t.castSucc) := by
                rw [hσ]
                exact (Equiv.swap_apply_self p (Fin.last k) t.castSucc).symm
            _ = σ p := congrArg σ hcon
            _ = Fin.last k := by rw [hσ, Equiv.swap_apply_left]
        exact (Fin.ne_of_lt (Fin.castSucc_lt_last t)) h1
      have hmem : e (σ t.castSucc) ∈ I := by
        have h : e (σ t.castSucc) ∈ Set.range ⇑e := Set.mem_range_self _
        rw [herange] at h
        exact Finset.mem_coe.mp h
      have hne2 : e (σ t.castSucc) ≠ a := by
        rw [← hp]
        exact fun h => hne (e.injective h)
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne2, Finset.mem_coe.mp hmem⟩)
    · intro hy
      have hyI : y ∈ I := Finset.mem_of_mem_erase hy
      have hya : y ≠ a := (Finset.mem_erase.mp (Finset.mem_coe.mp hy)).1
      obtain ⟨s, hs⟩ : ∃ s, e s = y := by
        have h : y ∈ Set.range ⇑e := by
          rw [herange]
          exact Finset.mem_coe.mpr hyI
        exact h
      have hsp : s ≠ p := fun h => hya (by rw [← hs, h, hp])
      obtain ⟨t, ht⟩ : ∃ t : Fin k, σ t.castSucc = s := by
        by_cases hsl : s = Fin.last k
        · obtain ⟨t₀, ht₀⟩ : ∃ t : Fin k, p = t.castSucc := by
            rcases Fin.eq_castSucc_or_eq_last p with ⟨t, rfl⟩ | rfl
            · exact ⟨t, rfl⟩
            · exact absurd hsl hsp
          refine ⟨t₀, ?_⟩
          rw [hσ, ← ht₀, Equiv.swap_apply_left, hsl]
        · obtain ⟨t, rfl⟩ := (Fin.eq_castSucc_or_eq_last s).resolve_right hsl
          refine ⟨t, Equiv.swap_apply_of_ne_of_ne ?_ ?_⟩
          · exact fun h => hsp (by rw [← h])
          · exact Fin.ne_of_lt (Fin.castSucc_lt_last t)
      exact ⟨t, by show e (σ t.castSucc) = y; rw [ht, hs]⟩
  calc subsetRatioSet ν I
      = subsetRatio (k + 1) νe :=
        subsetRatioSet_eq ν I e.injective herange
    _ = subsetRatio (k + 1) (νe.map (coordMap ⇑σ)) :=
        (subsetRatio_coordMap_perm σ νe).symm
    _ ≤ subsetRatio k ((νe.map (coordMap ⇑σ)).map (projDrop (m := k))) :=
        subsetRatio_succ_le_proj k _ hmom2 hpos2
    _ = subsetRatio k (ν.map (coordMap e'')) := by
        rw [hνe, Measure.map_map (measurable_coordMap _) (measurable_coordMap _),
          Measure.map_map measurable_projDrop ((measurable_coordMap _).comp (measurable_coordMap _)), hfun]
    _ = subsetRatioSet ν (I.erase a) :=
        (subsetRatioSet_eq ν (I.erase a) he''inj hrange'').symm


/-- Iteration of the deletion step: enlarging the coordinate set
cannot increase the normalized ratio. -/
public theorem subsetRatioSet_mono {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0)
    {I J : Finset (Fin d)} (hJI : J ⊆ I) :
    subsetRatioSet ν I ≤ subsetRatioSet ν J := by
  have key : ∀ m (I J : Finset (Fin d)), I.card = m → J ⊆ I →
      subsetRatioSet ν I ≤ subsetRatioSet ν J := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro I J hcard hJI
      by_cases hIJ : J = I
      · subst hIJ
        exact le_rfl
      · have hss : J ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨hJI, hIJ⟩
        obtain ⟨a, haI, haJ⟩ := Finset.exists_of_ssubset hss
        have hlt : (I.erase a).card < m := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem haI
        exact (subsetRatioSet_erase_le ν hmom hpos I a haI).trans
          (ih (I.erase a).card hlt (I.erase a) J rfl
            (Finset.subset_erase.mpr ⟨hJI, haJ⟩))
  exact key I.card I J rfl hJI

/-- The subset ratio is at most `1` (Theorem 1.1 for the projection). -/
public theorem subsetRatioSet_le_one {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0)
    (I : Finset (Fin d)) (hI : I.Nonempty) :
    subsetRatioSet ν I ≤ 1 := by
  obtain ⟨k, hk⟩ : ∃ k, I.card = k + 1 :=
    ⟨I.card - 1, (Nat.sub_add_cancel (Finset.card_pos.mpr hI)).symm⟩
  set e : Fin (k + 1) ↪o Fin d := I.orderEmbOfFin hk with he
  have herange : Set.range ⇑e = ↑I := Finset.range_orderEmbOfFin I hk
  have hmom' : ∀ j : Fin (k + 1),
      ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂(ν.map (coordMap ⇑e)) ≠ ∞ := by
    intro j
    rw [moment_coordMap]
    exact hmom _
  have hpos' : ∀ j : Fin (k + 1), gap j (ν.map (coordMap ⇑e)) ≠ 0 := by
    intro j
    rw [gap_coordMap]
    exact hpos _
  calc subsetRatioSet ν I
      = subsetRatio (k + 1) (ν.map (coordMap ⇑e)) :=
        subsetRatioSet_eq ν I e.injective herange
    _ ≤ 1 := @subsetRatio_le_one k _ (isProbabilityMeasure_map_coordMap _ _) hmom' hpos'

/-- Singleton subsets have ratio exactly `1`. -/
public theorem subsetRatioSet_singleton {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0) (j : Fin d) :
    subsetRatioSet ν {j} = 1 := by
  have hinj : Function.Injective (fun _ : Fin 1 => j) :=
    fun a b _ => Subsingleton.elim a b
  have hrange : Set.range (fun _ : Fin 1 => j) = ↑({j} : Finset (Fin d)) := by
    rw [Set.range_const, Finset.coe_singleton]
  calc subsetRatioSet ν {j}
      = subsetRatio 1 (ν.map (coordMap (fun _ : Fin 1 => j))) :=
        subsetRatioSet_eq ν {j} hinj hrange
    _ = 1 := by
        apply @subsetRatio_one_eq_one _ (isProbabilityMeasure_map_coordMap _ _)
        · rw [gap_coordMap]
          exact hpos j
        · rw [gap_coordMap]
          exact gap_ne_top_of_moment ν j (hmom j)

/-- Proposition 12.1 (full form): for nonempty `J ⊆ I`,
`0 ≤ R_I(ν) ≤ R_J(ν) ≤ 1`. -/
public theorem subset_ratio_mono {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0)
    {I J : Finset (Fin d)} (hJI : J ⊆ I) (hJ : J.Nonempty) :
    0 ≤ subsetRatioSet ν I ∧ subsetRatioSet ν I ≤ subsetRatioSet ν J
      ∧ subsetRatioSet ν J ≤ 1 :=
  ⟨zero_le, subsetRatioSet_mono ν hmom hpos hJI,
    subsetRatioSet_le_one ν hmom hpos J hJ⟩

/-- Persistence of deficit for arbitrary supersets of coordinates. -/
public theorem subsetRatioSet_le_of_le {d : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hmom : ∀ j : Fin d, ∫⁻ x, ((‖x j‖₊ : ℝ≥0) : ℝ≥0∞) ∂ν ≠ ∞)
    (hpos : ∀ j : Fin d, gap j ν ≠ 0)
    {I J : Finset (Fin d)} (hJI : J ⊆ I) (c : ℝ≥0∞)
    (hc : subsetRatioSet ν J ≤ c) :
    subsetRatioSet ν I ≤ c :=
  (subsetRatioSet_mono ν hmom hpos hJI).trans hc


end HypercubeInequality
