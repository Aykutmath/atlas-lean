module

/-
# Ordered-tuple counting (HI-COUNT1, HI-COUNT2, HI-IID)

Paper Section 4: ordered `(d+1)`-tuples vs increasing sets.  The engine
is a bijection between injective tuples `Fin K → Fin N` and pairs of a
card-`K` set with a permutation; each increasing set contributes `K!`
ordered tuples of the same weight and absolute determinant, while
non-injective tuples contribute determinant zero (repeated rows).
-/

public import Mathlib
public import Section_3_LocalEstimate.Local

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

section Engine

variable {K N : ℕ}

/-- Forward map: a card-`K` set plus a permutation gives an injective tuple. -/
@[expose] public noncomputable def tupleForward
    (x : { T : Finset (Fin N) // T.card = K } × Equiv.Perm (Fin K)) :
    { f : Fin K → Fin N // Function.Injective f } :=
  ⟨(x.1.1.orderEmbOfFin x.1.2) ∘ (x.2),
    (x.1.1.orderEmbOfFin x.1.2).injective.comp x.2.injective⟩

/-- The range of a forward tuple is its set. -/
public theorem tupleForward_range (T : Finset (Fin N)) (h : T.card = K)
    (σ : Equiv.Perm (Fin K)) :
    Set.range (⇑(T.orderEmbOfFin h) ∘ ⇑σ) = ↑T := by
  rw [Set.range_comp]
  have hσ : Set.range (⇑σ) = Set.univ :=
    (Set.range_eq_univ).mpr σ.surjective
  rw [hσ, Set.image_univ, Finset.range_orderEmbOfFin]

/-- `tupleForward` is injective: the set is the range, the permutation the order. -/
public theorem tupleForward_injective :
    Function.Injective (@tupleForward K N) := by
  rintro ⟨⟨T₁, h₁⟩, σ₁⟩ ⟨⟨T₂, h₂⟩, σ₂⟩ heq
  simp only [tupleForward, Subtype.mk.injEq] at heq
  have hT : T₁ = T₂ := by
    apply Finset.coe_inj.mp
    have e1 := tupleForward_range T₁ h₁ σ₁
    have e2 := tupleForward_range T₂ h₂ σ₂
    rw [← e1, ← e2]
    exact congrArg Set.range heq
  subst hT
  have hh : h₁ = h₂ := rfl
  subst hh
  have hσ : σ₁ = σ₂ := by
    apply Equiv.ext
    intro k
    apply (T₁.orderEmbOfFin h₁).injective
    have hck := congrFun heq k
    simpa using hck
  exact Prod.ext rfl hσ

/-- `tupleForward` is surjective: every injective tuple is an ordered set. -/
public theorem tupleForward_surjective :
    Function.Surjective (@tupleForward K N) := by
  rintro ⟨f, hf⟩
  classical
  set T : Finset (Fin N) := Finset.image f Finset.univ with hTdef
  have hcard : T.card = K := by
    rw [hTdef, Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_fin]
  have hex : ∀ k, ∃ j, T.orderEmbOfFin hcard j = f k := by
    intro k
    have hmem : f k ∈ (↑T : Set (Fin N)) :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    rw [← Finset.range_orderEmbOfFin T hcard] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj⟩
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro a b hab
    apply hf
    rw [← hg a, ← hg b, hab]
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.mp hginj
  exact ⟨⟨⟨T, hcard⟩, Equiv.ofBijective g hgbij⟩, Subtype.ext (funext hg)⟩

/-- Tuples ↔ (set, permutation) equivalence. -/
@[expose] public noncomputable def tupleEquiv :
    ({ T : Finset (Fin N) // T.card = K } × Equiv.Perm (Fin K)) ≃
      { f : Fin K → Fin N // Function.Injective f } :=
  Equiv.ofBijective _ ⟨tupleForward_injective, tupleForward_surjective⟩

/-- Each card-`K` set contributes `K!` ordered tuples. -/
public theorem counting_engine (G : (Fin K → Fin N) → ℝ)
    (hvan : ∀ f, ¬Function.Injective f → G f = 0)
    (hinv : ∀ e : Fin K → Fin N, ∀ σ : Equiv.Perm (Fin K),
      G (e ∘ ⇑σ) = G e) :
    ∑ f, G f = (K ! : ℝ)
      * ∑ T : { T : Finset (Fin N) // T.card = K },
        G ⇑(T.1.orderEmbOfFin T.2) := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun f : Fin K → Fin N => Function.Injective f) G
  have hzero : (∑ i : { x : Fin K → Fin N // ¬Function.Injective x }, G ↑i) = 0 :=
    Finset.sum_eq_zero (fun f _ => hvan f.1 f.2)
  rw [hzero, add_zero] at hsplit
  have hreidx : (∑ f : { f : Fin K → Fin N // Function.Injective f }, G ↑f)
      = ∑ x : ({ T : Finset (Fin N) // T.card = K } × Equiv.Perm (Fin K)),
        G ↑((tupleEquiv (K := K) (N := N)) x) :=
    (Equiv.sum_comp _ _).symm
  rw [← hsplit, hreidx, Fintype.sum_prod_type]
  have hinner : ∀ T : { T : Finset (Fin N) // T.card = K },
      (∑ σ : Equiv.Perm (Fin K),
        G ↑((tupleEquiv (K := K) (N := N)) (T, σ)))
      = (K ! : ℝ) * G ⇑(T.1.orderEmbOfFin T.2) := by
    intro T
    have hpt : ∀ σ : Equiv.Perm (Fin K),
        (↑((tupleEquiv (K := K) (N := N)) (T, σ)) : Fin K → Fin N)
          = ⇑(T.1.orderEmbOfFin T.2) ∘ ⇑σ := fun σ => rfl
    simp only [hpt]
    have hconst : ∀ σ : Equiv.Perm (Fin K),
        G (⇑(T.1.orderEmbOfFin T.2) ∘ ⇑σ) = G ⇑(T.1.orderEmbOfFin T.2) :=
      fun σ => hinv _ σ
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun T _ => hinner T), ← Finset.mul_sum]

/-- Counting engine for extended-nonnegative summands. -/
public theorem counting_engine_ennreal (G : (Fin K → Fin N) → ℝ≥0∞)
    (hvan : ∀ f, ¬Function.Injective f → G f = 0)
    (hinv : ∀ e : Fin K → Fin N, ∀ σ : Equiv.Perm (Fin K),
      G (e ∘ ⇑σ) = G e) :
    ∑ f, G f = ((((K ! : ℕ))) : ℝ≥0∞)
      * ∑ T : { T : Finset (Fin N) // T.card = K },
        G ⇑(T.1.orderEmbOfFin T.2) := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun f : Fin K → Fin N => Function.Injective f) G
  have hzero : (∑ i : { x : Fin K → Fin N // ¬Function.Injective x }, G ↑i) = 0 :=
    Finset.sum_eq_zero (fun f _ => hvan f.1 f.2)
  rw [hzero, add_zero] at hsplit
  have hreidx : (∑ f : { f : Fin K → Fin N // Function.Injective f }, G ↑f)
      = ∑ x : ({ T : Finset (Fin N) // T.card = K } × Equiv.Perm (Fin K)),
        G ↑((tupleEquiv (K := K) (N := N)) x) :=
    (Equiv.sum_comp _ _).symm
  rw [← hsplit, hreidx, Fintype.sum_prod_type]
  have hinner : ∀ T : { T : Finset (Fin N) // T.card = K },
      (∑ σ : Equiv.Perm (Fin K),
        G ↑((tupleEquiv (K := K) (N := N)) (T, σ)))
      = ((((K ! : ℕ))) : ℝ≥0∞) * G ⇑(T.1.orderEmbOfFin T.2) := by
    intro T
    have hpt : ∀ σ : Equiv.Perm (Fin K),
        (↑((tupleEquiv (K := K) (N := N)) (T, σ)) : Fin K → Fin N)
          = ⇑(T.1.orderEmbOfFin T.2) ∘ ⇑σ := fun σ => rfl
    simp only [hpt]
    have hconst : ∀ σ : Equiv.Perm (Fin K),
        G (⇑(T.1.orderEmbOfFin T.2) ∘ ⇑σ) = G ⇑(T.1.orderEmbOfFin T.2) :=
      fun σ => hinv _ σ
    simp only [hconst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun T _ => hinner T), ← Finset.mul_sum]

/-- Subtype sums over card-`K` sets are `powersetCard` sums. -/
public theorem sum_subtype_card_eq_powersetCard (F : Finset (Fin N) → ℝ) :
    (∑ T : { T : Finset (Fin N) // T.card = K }, F T.1)
      = ∑ T ∈ Finset.powersetCard K Finset.univ, F T := by
  classical
  have h : (∑ T ∈ Finset.powersetCard K (Finset.univ : Finset (Fin N)), F T)
      = ∑ T : { T : Finset (Fin N) // T.card = K }, F T.1 :=
    Finset.sum_subtype _ (fun T => ⟨fun hm => (Finset.mem_powersetCard.mp hm).2,
      fun hc => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hc⟩⟩) _
  exact h.symm

/-- Subtype sums over card-`K` sets are `powersetCard` sums (extended). -/
public theorem sum_subtype_card_eq_powersetCard_ennreal
    (F : Finset (Fin N) → ℝ≥0∞) :
    (∑ T : { T : Finset (Fin N) // T.card = K }, F T.1)
      = ∑ T ∈ Finset.powersetCard K Finset.univ, F T := by
  classical
  have h : (∑ T ∈ Finset.powersetCard K (Finset.univ : Finset (Fin N)), F T)
      = ∑ T : { T : Finset (Fin N) // T.card = K }, F T.1 :=
    Finset.sum_subtype _ (fun T => ⟨fun hm => (Finset.mem_powersetCard.mp hm).2,
      fun hc => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hc⟩⟩) _
  exact h.symm

end Engine

section OrderedA

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- Ordered-tuple `A` matrix: rows `(B, 1, Y)` along the tuple. -/
@[expose] public noncomputable def ordMatA (f : Fin (m + 2) → Fin N) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of (fun r c =>
    Fin.cases (B (f r))
      (fun j => Fin.cases (1 : ℝ) (fun t => Yatom (f r) t) j) c)

/-- Ordered-tuple weight `∏ p`. -/
@[expose] public noncomputable def ordWeight (f : Fin (m + 2) → Fin N) : ℝ :=
  ∏ r, p (f r)

/-- Ordered-tuple summand `w(f) |A(f)|`. -/
@[expose] public noncomputable def ordTermA (f : Fin (m + 2) → Fin N) : ℝ :=
  ordWeight p f * |Matrix.det (ordMatA Yatom B f)|

/-- The ordered matrix on an increasing tuple is the `A_T` matrix. -/
public theorem ordMatA_eq_detATMat (T : Finset (Fin N)) (hT : T.card = m + 2) :
    ordMatA Yatom B ⇑(T.orderEmbOfFin hT) = detATMat Yatom B T hT := rfl

/-- The ordered weight on an increasing tuple is the atom weight. -/
public theorem ordWeight_eq_atomWeight (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    ordWeight p ⇑(T.orderEmbOfFin hT) = atomWeight p T := by
  have hinj : Function.Injective ⇑(T.orderEmbOfFin hT) :=
    (T.orderEmbOfFin hT).injective
  have himg : Finset.image ⇑(T.orderEmbOfFin hT) Finset.univ = T := by
    apply Finset.coe_inj.mp
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.range_orderEmbOfFin]
  have hpi : (∏ i ∈ Finset.image ⇑(T.orderEmbOfFin hT) Finset.univ, p i)
      = ∏ r, p ((T.orderEmbOfFin hT) r) :=
    Finset.prod_image (fun x _ y _ hxy => hinj hxy)
  have himg2 : (∏ i ∈ Finset.image ⇑(T.orderEmbOfFin hT) Finset.univ, p i)
      = atomWeight p T := by
    simp only [himg, atomWeight]
  simp only [ordWeight]
  rw [← hpi]
  exact himg2

/-- Non-injective tuples contribute zero (repeated rows). -/
public theorem ordTermA_vanish (f : Fin (m + 2) → Fin N)
    (hf : ¬Function.Injective f) : ordTermA p Yatom B f = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
  have hrow : ordMatA Yatom B f a = ordMatA Yatom B f b := by
    funext c
    simp only [ordMatA, Matrix.of_apply]
    rw [hab]
  have hdet : Matrix.det (ordMatA Yatom B f) = 0 :=
    Matrix.det_zero_of_row_eq hne hrow
  simp [ordTermA, hdet]

/-- Reordering a tuple permutes the matrix rows. -/
public theorem ordMatA_comp_perm (e : Fin (m + 2) → Fin N)
    (σ : Equiv.Perm (Fin (m + 2))) :
    ordMatA Yatom B (e ∘ ⇑σ) = (ordMatA Yatom B e).submatrix ⇑σ id := by
  ext r c
  simp only [ordMatA, Matrix.of_apply, Matrix.submatrix_apply,
    Function.comp_apply, id_eq]

/-- The ordered summand is invariant under reordering. -/
public theorem ordTermA_perm (e : Fin (m + 2) → Fin N)
    (σ : Equiv.Perm (Fin (m + 2))) :
    ordTermA p Yatom B (e ∘ ⇑σ) = ordTermA p Yatom B e := by
  have hw : ordWeight p (e ∘ ⇑σ) = ordWeight p e := by
    simp only [ordWeight]
    exact Equiv.prod_comp σ (fun i => p (e i))
  have hsign : |((σ.sign : ℤˣ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
  have hdet : |Matrix.det (ordMatA Yatom B (e ∘ ⇑σ))|
      = |Matrix.det (ordMatA Yatom B e)| := by
    rw [ordMatA_comp_perm, Matrix.det_permute, abs_mul, hsign, one_mul]
  simp only [ordTermA, hw, hdet]

/-- The ordered summand on an increasing tuple is the set summand. -/
public theorem ordTermA_eq_setTerm (T : Finset (Fin N))
    (hT : T.card = m + 2) :
    ordTermA p Yatom B ⇑(T.orderEmbOfFin hT)
      = atomWeight p T * |detAT' Yatom B T| := by
  simp only [ordTermA, ordWeight_eq_atomWeight p T hT,
    detAT'_eq Yatom B T hT, ordMatA_eq_detATMat, detAT]

/-- Subtype ordered sums are `powersetCard` weighted sums (A-side). -/
public theorem bridge_ordered_A :
    (∑ T : { T : Finset (Fin N) // T.card = m + 2 },
      ordTermA p Yatom B ⇑(T.1.orderEmbOfFin T.2))
    = ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
      atomWeight p T * |detAT' Yatom B T| := by
  have hF := sum_subtype_card_eq_powersetCard (K := m + 2) (N := N)
    (fun T => atomWeight p T * |detAT' Yatom B T|)
  rw [← hF]
  apply Finset.sum_congr rfl
  rintro ⟨T, hT⟩ -
  exact ordTermA_eq_setTerm p Yatom B T hT

/-- HI-COUNT1: `E|A| = (d+1)! ∑_T w_T |A_T|`. -/
public theorem count_ordered_A :
    (∑ f : Fin (m + 2) → Fin N, ordTermA p Yatom B f)
      = ((m + 2)! : ℝ) * ∑ T ∈ Finset.powersetCard (m + 2) Finset.univ,
        atomWeight p T * |detAT' Yatom B T| := by
  classical
  have heng := counting_engine (K := m + 2) (N := N) (ordTermA p Yatom B)
    (fun f hf => ordTermA_vanish p Yatom B f hf)
    (fun e σ => ordTermA_perm p Yatom B e σ)
  rw [heng, bridge_ordered_A]

end OrderedA

section OrderedD

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m))

/-- Ordered-tuple `D` matrix: rows `(1, Y)` along the tuple. -/
@[expose] public noncomputable def ordMatD (g : Fin (m + 1) → Fin N) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of (fun r c => Fin.cases (1 : ℝ) (fun j => Yatom (g r) j) c)

/-- Ordered-tuple weight `∏ p` (`D`-side). -/
@[expose] public noncomputable def ordWeightD (g : Fin (m + 1) → Fin N) : ℝ :=
  ∏ s, p (g s)

/-- Ordered-tuple summand `w(G) |D(G)|`. -/
@[expose] public noncomputable def ordTermD (g : Fin (m + 1) → Fin N) : ℝ :=
  ordWeightD p g * |Matrix.det (ordMatD Yatom g)|

/-- The ordered `D` determinant on an increasing tuple is `D(U)`. -/
public theorem det_ordMatD_eq_detOf (U : Finset (Fin N))
    (h : U.card = m + 1) :
    Matrix.det (ordMatD Yatom ⇑(U.orderEmbOfFin h))
      = detOf Yatom U h := rfl

/-- The ordered weight on an increasing tuple is the atom weight (`D`-side). -/
public theorem ordWeightD_eq_atomWeight (U : Finset (Fin N))
    (h : U.card = m + 1) :
    ordWeightD p ⇑(U.orderEmbOfFin h) = atomWeight p U := by
  have hinj : Function.Injective ⇑(U.orderEmbOfFin h) :=
    (U.orderEmbOfFin h).injective
  have himg : Finset.image ⇑(U.orderEmbOfFin h) Finset.univ = U := by
    apply Finset.coe_inj.mp
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.range_orderEmbOfFin]
  have hpi : (∏ i ∈ Finset.image ⇑(U.orderEmbOfFin h) Finset.univ, p i)
      = ∏ s, p ((U.orderEmbOfFin h) s) :=
    Finset.prod_image (fun x _ y _ hxy => hinj hxy)
  have himg2 : (∏ i ∈ Finset.image ⇑(U.orderEmbOfFin h) Finset.univ, p i)
      = atomWeight p U := by
    simp only [himg, atomWeight]
  simp only [ordWeightD]
  rw [← hpi]
  exact himg2

/-- Non-injective tuples contribute zero (`D`-side). -/
public theorem ordTermD_vanish (g : Fin (m + 1) → Fin N)
    (hg : ¬Function.Injective g) : ordTermD p Yatom g = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hg
  have hrow : ordMatD Yatom g a = ordMatD Yatom g b := by
    funext c
    simp only [ordMatD, Matrix.of_apply]
    rw [hab]
  have hdet : Matrix.det (ordMatD Yatom g) = 0 :=
    Matrix.det_zero_of_row_eq hne hrow
  simp [ordTermD, hdet]

/-- Reordering a tuple permutes the `D`-matrix rows. -/
public theorem ordMatD_comp_perm (e : Fin (m + 1) → Fin N)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ordMatD Yatom (e ∘ ⇑σ) = (ordMatD Yatom e).submatrix ⇑σ id := by
  ext r c
  simp only [ordMatD, Matrix.of_apply, Matrix.submatrix_apply,
    Function.comp_apply, id_eq]

/-- The ordered `D` summand is invariant under reordering. -/
public theorem ordTermD_perm (e : Fin (m + 1) → Fin N)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ordTermD p Yatom (e ∘ ⇑σ) = ordTermD p Yatom e := by
  have hw : ordWeightD p (e ∘ ⇑σ) = ordWeightD p e := by
    simp only [ordWeightD]
    exact Equiv.prod_comp σ (fun i => p (e i))
  have hsign : |((σ.sign : ℤˣ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]
  have hdet : |Matrix.det (ordMatD Yatom (e ∘ ⇑σ))|
      = |Matrix.det (ordMatD Yatom e)| := by
    rw [ordMatD_comp_perm, Matrix.det_permute, abs_mul, hsign, one_mul]
  simp only [ordTermD, hw, hdet]

/-- The ordered `D` summand on an increasing tuple is the set summand. -/
public theorem ordTermD_eq_setTerm (U : Finset (Fin N))
    (h : U.card = m + 1) :
    ordTermD p Yatom ⇑(U.orderEmbOfFin h)
      = atomWeight p U * |detOf' Yatom U| := by
  simp only [ordTermD, ordWeightD_eq_atomWeight p U h,
    detOf'_eq Yatom U h, det_ordMatD_eq_detOf]

/-- Subtype ordered sums are `powersetCard` weighted sums (`D`-side). -/
public theorem bridge_ordered_D :
    (∑ U : { U : Finset (Fin N) // U.card = m + 1 },
      ordTermD p Yatom ⇑(U.1.orderEmbOfFin U.2))
    = ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
      atomWeight p U * |detOf' Yatom U| := by
  have hF := sum_subtype_card_eq_powersetCard (K := m + 1) (N := N)
    (fun U => atomWeight p U * |detOf' Yatom U|)
  rw [← hF]
  apply Finset.sum_congr rfl
  rintro ⟨U, hU⟩ -
  exact ordTermD_eq_setTerm p Yatom U hU

/-- HI-COUNT2a: `E|D| = d! ∑_U w_U |D(U)|`. -/
public theorem count_ordered_D :
    (∑ g : Fin (m + 1) → Fin N, ordTermD p Yatom g)
      = ((m + 1)! : ℝ) * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
        atomWeight p U * |detOf' Yatom U| := by
  classical
  have heng := counting_engine (K := m + 1) (N := N) (ordTermD p Yatom)
    (fun g hg => ordTermD_vanish p Yatom g hg)
    (fun e σ => ordTermD_perm p Yatom e σ)
  rw [heng, bridge_ordered_D]

end OrderedD

section Omission

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m))

/-- Expected omitted-`D` mass at position `r`. -/
@[expose] public noncomputable def omitSum (r : Fin (m + 2)) : ℝ :=
  ∑ F : Fin (m + 2) → Fin N,
    ordWeight p F * |Matrix.det (ordMatD Yatom (F ∘ r.succAbove))|

/-- Splitting the ordered weight at the omitted position. -/
public theorem ordWeight_insertNth (r : Fin (m + 2)) (i : Fin N)
    (G : Fin (m + 1) → Fin N) :
    ordWeight p (Fin.insertNth (α := fun _ => Fin N) r i G)
      = p i * ordWeightD p G := by
  simp only [ordWeight, ordWeightD]
  rw [Fin.prod_univ_succAbove _ r, Fin.insertNth_apply_same]
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  rw [Fin.insertNth_apply_succAbove]

/-- Omitting after inserting recovers the subtuple. -/
public theorem insertNth_comp_succAbove (r : Fin (m + 2)) (i : Fin N)
    (G : Fin (m + 1) → Fin N) :
    (Fin.insertNth (α := fun _ => Fin N) r i G) ∘ r.succAbove = G := by
  funext s
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin N) r i G s

/-- Per-fiber value of the omitted sum. -/
public theorem omitSum_fiber (r : Fin (m + 2)) (i : Fin N)
    (G : Fin (m + 1) → Fin N) :
    ordWeight p (Fin.insertNth (α := fun _ => Fin N) r i G)
        * |Matrix.det (ordMatD Yatom
          ((Fin.insertNth (α := fun _ => Fin N) r i G) ∘ r.succAbove))|
      = p i * ordTermD p Yatom G := by
  rw [ordWeight_insertNth, insertNth_comp_succAbove]
  simp only [ordTermD]
  ring

/-- HI-COUNT2b: every omission position carries the same mass `E|D|`. -/
public theorem omitSum_eq (r : Fin (m + 2)) (hsum : ∑ i, p i = 1) :
    omitSum p Yatom r
      = ∑ G : Fin (m + 1) → Fin N, ordTermD p Yatom G := by
  classical
  have hErw : (∑ F : Fin (m + 2) → Fin N,
        ordWeight p F * |Matrix.det (ordMatD Yatom (F ∘ r.succAbove))|)
      = ∑ q : Fin N × (∀ s : Fin (m + 1), (fun _ => Fin N) (r.succAbove s)),
        ordWeight p ((Fin.insertNthEquiv (n := m + 1) (fun _ => Fin N) r) q)
          * |Matrix.det (ordMatD Yatom
            (((Fin.insertNthEquiv (n := m + 1) (fun _ => Fin N) r) q)
              ∘ r.succAbove))| :=
    (Equiv.sum_comp (Fin.insertNthEquiv (n := m + 1) (fun _ => Fin N) r) _).symm
  have hcollapse : (∑ i : Fin N, ∑ G : Fin (m + 1) → Fin N,
        p i * ordTermD p Yatom G)
      = ∑ G : Fin (m + 1) → Fin N, ordTermD p Yatom G := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]
  simp only [omitSum]
  rw [hErw, Fintype.sum_prod_type, ← hcollapse]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro G _
  exact omitSum_fiber p Yatom r i G

end Omission

section IID

variable {m N : ℕ} (p : Fin N → ℝ)
  (Yatom : Fin N → EuclideanSpace ℝ (Fin m)) (B : Fin N → ℝ)

/-- HI-IID (Cor 4.2, Bernoulli determinant inequality):
`E|A| ≤ p̄(1-p̄) E∑_r |D_r|`. -/
public theorem bernoulli_det_inequality (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (hbin : ∀ i, B i = 0 ∨ B i = 1) :
    (∑ F : Fin (m + 2) → Fin N, ordTermA p Yatom B F)
      ≤ pbar p B * (1 - pbar p B)
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := by
  have hW := weighted_bernoulli_inequality p Yatom B hpos hsum hbin
  have hfact : ((m + 2)! : ℝ)
      = ((m + 2 : ℕ) : ℝ) * ((m + 1)! : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.cast_mul]
  have hK : (0 : ℝ) ≤ ((m + 2)! : ℝ) := Nat.cast_nonneg _
  have hW2 := mul_le_mul_of_nonneg_left hW hK
  have hO : (∑ r : Fin (m + 2), omitSum p Yatom r)
      = ((m + 2 : ℕ) : ℝ)
        * ∑ G : Fin (m + 1) → Fin N, ordTermD p Yatom G := by
    simp only [omitSum_eq p Yatom _ hsum]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hRHS : ((m + 2)! : ℝ)
        * (pbar p B * (1 - pbar p B)
          * ∑ U ∈ Finset.powersetCard (m + 1) Finset.univ,
            atomWeight p U * |detOf' Yatom U|)
      = pbar p B * (1 - pbar p B)
        * (∑ r : Fin (m + 2), omitSum p Yatom r) := by
    rw [hfact, hO, count_ordered_D p Yatom]
    ring
  rw [(count_ordered_A p Yatom B).symm, hRHS] at hW2
  exact hW2

end IID

end HypercubeInequality
