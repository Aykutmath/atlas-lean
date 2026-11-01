import Section_10_Zonoid.Cor101.Definitions
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Ordered tuples and maximal minors

The ordering factor in the zonotope volume formula is proved by counting all
bijections from `Fin n` onto each `n`-element set of generator labels.
-/

open MeasureTheory Set Module
open scoped ENNReal Pointwise BigOperators

noncomputable section
namespace Cor101.Zonotope

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

omit [Fintype ι] in
lemma injective_iff_image_card (f : Fin n → ι) :
    Function.Injective f ↔ (Finset.univ.image f).card = n := by
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.coe_univ, Set.injOn_univ] using
    (Finset.card_image_iff (s := Finset.univ) (f := f)).symm

/-- An enumeration is exactly a bijection onto its finite image. -/
def enumerationEquiv (s : Finset ι) (hs : s.card = n) :
    (Fin n ≃ s) ≃ {f : Fin n → ι // Finset.univ.image f = s} where
  toFun e := ⟨fun i => e i, by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩⟩
  invFun f := Equiv.ofBijective
    (fun i => (⟨f.val i, by simpa only [f.property] using (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩ : f.val i ∈ Finset.univ.image f.val)⟩ : s))
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      rintro ⟨x, hx⟩
      rw [← f.property] at hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩,
      by simpa using hs.symm⟩)
  left_inv e := by ext i; rfl
  right_inv f := by ext i; rfl

lemma card_enumerations (s : Finset ι) (hs : s.card = n) :
    (Finset.univ.filter (fun f : Fin n → ι => Finset.univ.image f = s)).card =
      n.factorial := by
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (by simpa using hs)).symm
  calc
    _ = Fintype.card {f : Fin n → ι // Finset.univ.image f = s} := by
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin n ≃ s) := (Fintype.card_congr (enumerationEquiv s hs)).symm
    _ = n.factorial := by simpa using Fintype.card_equiv e

/-- Every symmetric weight on injective tuples counts each `n`-element set
exactly `n!` times. Repeated-label tuples may be present but have zero weight. -/
theorem sum_tuples_eq_factorial_smul {M : Type*} [AddCommMonoid M]
    (W : (Fin n → ι) → M) (G : Finset ι → M)
    (hrepeat : ∀ f, ¬ Function.Injective f → W f = 0)
    (himage : ∀ f, Function.Injective f → W f = G (Finset.univ.image f)) :
    ∑ f, W f = n.factorial • ∑ s ∈ (Finset.univ : Finset ι).powersetCard n, G s := by
  classical
  have hfilter : ∑ f ∈ Finset.univ.filter (Function.Injective : (Fin n → ι) → Prop), W f =
      ∑ f, W f := Finset.sum_filter_of_ne (fun f _ hf => by
        by_contra hn; exact hf (hrepeat f hn))
  rw [← hfilter]
  have hmaps : ∀ f ∈ Finset.univ.filter (Function.Injective : (Fin n → ι) → Prop),
      Finset.univ.image f ∈ (Finset.univ : Finset ι).powersetCard n := by
    intro f hf
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (injective_iff_image_card f).mp (Finset.mem_filter.mp hf).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps W, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsc : s.card = n := (Finset.mem_powersetCard.mp hs).2
  have hsame : (Finset.univ.filter (Function.Injective : (Fin n → ι) → Prop)).filter
      (fun f => Finset.univ.image f = s) =
      Finset.univ.filter (fun f : Fin n → ι => Finset.univ.image f = s) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hf
      exact ⟨(injective_iff_image_card f).mpr (hf ▸ hsc), hf⟩
  rw [hsame]
  calc
    _ = ∑ _f ∈ Finset.univ.filter (fun f : Fin n → ι => Finset.univ.image f = s), G s := by
      apply Finset.sum_congr rfl
      intro f hf
      have hfs := (Finset.mem_filter.mp hf).2
      rw [himage f ((injective_iff_image_card f).mpr (hfs ▸ hsc)), hfs]
    _ = n.factorial • G s := by rw [Finset.sum_const, card_enumerations s hsc]

/-- The ordinary Euclidean volume of an `n`-generator parallelotope is its
absolute determinant, with no linear-independence assumption. -/
theorem volume_parallelepiped_eq_det (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    volume (parallelepiped v) =
      ENNReal.ofReal |(Matrix.of (fun i j => v i j)).det| := by
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume,
    Measure.addHaar_parallelepiped, Basis.det_apply]
  congr 2
  rw [← Matrix.det_transpose]
  congr 1

omit [Fintype ι] [DecidableEq ι] in
lemma volume_parallelepiped_comp_eq_zero (v : ι → EuclideanSpace ℝ (Fin n))
    (f : Fin n → ι) (hf : ¬ Function.Injective f) :
    volume (parallelepiped (v ∘ f)) = 0 := by
  rw [volume_parallelepiped_eq_det]
  obtain ⟨i, j, hij, heq⟩ := Function.not_injective_iff.mp hf
  have hd : (Matrix.of (fun i j => (v ∘ f) i j)).det = 0 :=
    Matrix.det_zero_of_row_eq heq (by
      change (fun k => v (f i) k) = (fun k => v (f j) k)
      rw [hij])
  rw [hd, abs_zero, ENNReal.ofReal_zero]

omit [Fintype ι] in
lemma parallelepiped_comp_eq_sum_image {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ι → E) (f : Fin n → ι) (hf : Function.Injective f) :
    parallelepiped (v ∘ f) = ∑ i ∈ Finset.univ.image f, segment ℝ 0 (v i) := by
  rw [parallelepiped_eq_sum_segment, Finset.sum_image (fun i _ j _ hij => hf hij)]
  rfl

/-- The sum of volumes of all maximal generator parallelotopes is exactly
 the ordered absolute-minor sum divided by `n!`. -/
theorem sum_subsets_volume_eq_ordered_determinant
    (v : ι → EuclideanSpace ℝ (Fin n)) :
    (∑ s ∈ (Finset.univ : Finset ι).powersetCard n,
      volume (∑ i ∈ s, segment ℝ 0 (v i))) =
      ENNReal.ofReal ((∑ f : Fin n → ι,
        |(Matrix.of (fun i j => v (f i) j)).det|) / (n.factorial : ℝ)) := by
  have h := sum_tuples_eq_factorial_smul
    (fun f : Fin n → ι => volume (parallelepiped (v ∘ f)))
    (fun s : Finset ι => volume (∑ i ∈ s, segment ℝ 0 (v i)))
    (volume_parallelepiped_comp_eq_zero v)
    (fun f hf => congrArg volume (parallelepiped_comp_eq_sum_image v f hf))
  simp_rw [volume_parallelepiped_eq_det] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun f _ => abs_nonneg _), nsmul_eq_mul] at h
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.factorial_pos n),
    ENNReal.ofReal_natCast]
  apply (ENNReal.eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)
    (ENNReal.natCast_ne_top n.factorial)).mpr
  exact h.symm

end Cor101.Zonotope
