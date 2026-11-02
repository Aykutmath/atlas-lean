/-
Gaussian null sets, almost-sure spanning, and rank events.

A nonzero multivariate polynomial vanishes only on a Gaussian null set
(proved by induction on the dimension with Fubini sections), first for
`Fin m`, then for any finite index type by reindexing, and finally for
the paper's nested sample law by uncurrying transport. Hence Gaussian
samples span almost surely and the sample Gram matrix is positive
definite almost surely. No measurability of the existential fitting
events is needed.

Mathematical source: paper.tex, Sections 2 and 12.
-/
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.ExactFit
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory Finset

/-- Singletons are null for the standard one-dimensional Gaussian law. -/
theorem gaussianReal_singleton_null (c : ℝ) :
    gaussianReal 0 1 {c} = 0 := by
  have habs := gaussianReal_absolutelyContinuous (0 : ℝ) (show (1 : NNReal) ≠ 0 from one_ne_zero)
  exact habs Real.volume_singleton

/-- Finite sets are null for the standard one-dimensional Gaussian law. -/
theorem gaussianReal_finite_null {s : Set ℝ} (hs : s.Finite) :
    gaussianReal 0 1 s = 0 := by
  obtain ⟨F, rfl⟩ := hs.exists_finset_coe
  have hunion : (↑F : Set ℝ) = ⋃ b ∈ F, ({b} : Set ℝ) := by
    ext x
    simp
  rw [hunion, measure_biUnion_finset _ _]
  · simp [gaussianReal_singleton_null]
  · intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro x hx hxt
    simp only [Set.mem_singleton_iff] at hx hxt
    exact hab (hx.symm.trans hxt)
  · intro b _
    have hsing : ({b} : Set ℝ) = {x | x = b} := by
      ext x
      exact Set.mem_singleton_iff
    rw [hsing]
    exact measurableSet_eq_fun measurable_id measurable_const

/-- Polynomial evaluation is continuous in the point. -/
theorem mvPolynomial_eval_continuous {σ : Type*} (p : MvPolynomial σ ℝ) :
    Continuous (fun x : σ → ℝ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact continuous_const
  | add p q hp hq =>
    simp only [MvPolynomial.eval_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (continuous_apply n)

/-- The zero set of a nonzero univariate real polynomial is finite. -/
theorem polynomial_zeroSet_finite {Q : Polynomial ℝ} (hQ : Q ≠ 0) :
    {x | Q.eval x = 0}.Finite := by
  have hset : {x | Q.eval x = 0} = ↑(Q.roots.toFinset) := by
    ext x
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    rfl
  rw [hset]
  exact Finset.finite_toSet _

/-- The zero set of a nonzero univariate real polynomial is Gaussian null. -/
theorem polynomial_zeroSet_null {Q : Polynomial ℝ} (hQ : Q ≠ 0) :
    gaussianReal 0 1 {x | Q.eval x = 0} = 0 :=
  gaussianReal_finite_null (polynomial_zeroSet_finite hQ)

/-- Polynomial evaluation is measurable in the point (needs no topological
instances on the index type). -/
theorem mvPolynomial_eval_measurable {σ : Type*} (p : MvPolynomial σ ℝ) :
    Measurable (fun x : σ → ℝ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact measurable_const
  | add p q hp hq =>
    simp only [MvPolynomial.eval_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (measurable_pi_apply n)

/-- Measurability of a multivariate polynomial zero set. -/
theorem mvPolynomial_zeroSet_measurable {σ : Type*} (p : MvPolynomial σ ℝ) :
    MeasurableSet {x : σ → ℝ | MvPolynomial.eval x p = 0} :=
  measurableSet_eq_fun (mvPolynomial_eval_measurable p) measurable_const

/-- Head/tail splitting at index zero as a measurable equivalence. -/
def piHeadTail (m : ℕ) : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0

theorem piHeadTail_fst (m : ℕ) (x : Fin (m + 1) → ℝ) :
    (piHeadTail m x).1 = x 0 := by
  show ((Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) 0).symm x).1 = x 0
  rw [Fin.insertNthEquiv_zero]
  rfl

theorem piHeadTail_snd (m : ℕ) (x : Fin (m + 1) → ℝ) :
    (piHeadTail m x).2 = Fin.tail x := by
  show ((Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) 0).symm x).2 = Fin.tail x
  rw [Fin.insertNthEquiv_zero]
  rfl

theorem measurePreserving_piHeadTail (m : ℕ) :
    MeasurePreserving (piHeadTail m)
      (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
  have h := measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => gaussianReal 0 1) (0 : Fin (m + 1))
  unfold piHeadTail
  exact h

/-- Tail/head splitting (swapped order) for Fubini sections over the tail. -/
def piTailHead (m : ℕ) : (Fin (m + 1) → ℝ) ≃ᵐ (Fin m → ℝ) × ℝ :=
  (piHeadTail m).trans MeasurableEquiv.prodComm

theorem piTailHead_apply (m : ℕ) (x : Fin (m + 1) → ℝ) :
    piTailHead m x = (Fin.tail x, x 0) := by
  have he : piHeadTail m x = (x 0, Fin.tail x) := by
    have h1 := piHeadTail_fst m x
    have h2 := piHeadTail_snd m x
    rw [← h1, ← h2]
  show Prod.swap (piHeadTail m x) = (Fin.tail x, x 0)
  rw [he]
  rfl

theorem measurePreserving_piTailHead (m : ℕ) :
    MeasurePreserving (piTailHead m)
      (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine ⟨(piTailHead m).measurable, ?_⟩
  have hmp := measurePreserving_piHeadTail m
  have hcomp : ⇑(piTailHead m) = Prod.swap ∘ ⇑(piHeadTail m) := rfl
  rw [hcomp, ← Measure.map_map measurable_swap (piHeadTail m).measurable, hmp.map_eq]
  exact Measure.prod_swap

/-- A nonzero multivariate polynomial vanishes only on a Gaussian null set. -/
theorem mvPolynomial_zeroSet_null_pi (m : ℕ) :
    ∀ (p : MvPolynomial (Fin m) ℝ), p ≠ 0 →
    Measure.pi (fun _ : Fin m => gaussianReal 0 1)
      {x | MvPolynomial.eval x p = 0} = 0 := by
  induction m with
  | zero =>
    intro p hp
    rw [MvPolynomial.eq_C_of_isEmpty p]
    have hcoeff : p.coeff 0 ≠ 0 := by
      intro hz
      apply hp
      rw [MvPolynomial.eq_C_of_isEmpty p, hz]
      exact map_zero _
    simp only [MvPolynomial.eval_C]
    have hempty : {x : Fin 0 → ℝ | p.coeff 0 = 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun _ h => hcoeff h)
    rw [hempty, measure_empty]
  | succ m IH =>
    intro p hp
    have hQne : MvPolynomial.finSuccEquiv ℝ m p ≠ 0 := by
      intro hz
      apply hp
      have hinj := (MvPolynomial.finSuccEquiv ℝ m).toEquiv.injective
      refine hinj ?_
      show (MvPolynomial.finSuccEquiv ℝ m) p = (MvPolynomial.finSuccEquiv ℝ m) 0
      rw [hz]
      simp
    obtain ⟨k₀, hk₀⟩ : ∃ k, (MvPolynomial.finSuccEquiv ℝ m p).coeff k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hQne
      rw [Polynomial.ext_iff]
      intro k
      simp [hall k]
    have hIH := IH _ hk₀
    set Z : Set (Fin (m + 1) → ℝ) := {x | MvPolynomial.eval x p = 0} with hZ
    have hWmeas : MeasurableSet ((piTailHead m) '' Z) := by
      have himg : (piTailHead m) '' Z = (piTailHead m).symm ⁻¹' Z := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          show (piTailHead m).symm ((piTailHead m) x) ∈ Z
          have hsym : (piTailHead m).toEquiv.symm ((piTailHead m).toEquiv x) = x :=
            Equiv.symm_apply_apply _ _
          rw [show (piTailHead m).symm ((piTailHead m) x) =
            (piTailHead m).toEquiv.symm ((piTailHead m).toEquiv x) from rfl, hsym]
          exact hx
        · intro hy
          refine ⟨(piTailHead m).symm y, hy, ?_⟩
          have happ : (piTailHead m).toEquiv ((piTailHead m).toEquiv.symm y) = y :=
            Equiv.apply_symm_apply _ _
          show (piTailHead m) ((piTailHead m).symm y) = y
          rw [show (piTailHead m) ((piTailHead m).symm y) =
            (piTailHead m).toEquiv ((piTailHead m).toEquiv.symm y) from rfl]
          exact happ
      rw [himg]
      exact (piTailHead m).symm.measurable (mvPolynomial_zeroSet_measurable p)
    have hWchar : ∀ (x' : Fin m → ℝ) (t : ℝ),
        (x', t) ∈ (piTailHead m) '' Z ↔
          MvPolynomial.eval (Fin.cons t x') p = 0 := by
      intro x' t
      constructor
      · rintro ⟨x, hx, hxx'⟩
        have happ := piTailHead_apply m x
        rw [hxx'] at happ
        have hx0 : t = x 0 := (Prod.mk.injEq ..).mp happ |>.2
        have hxt : x' = Fin.tail x := (Prod.mk.injEq ..).mp happ |>.1
        have hxeq : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
        rw [hxeq, ← hx0, ← hxt] at hx
        exact hx
      · intro heval
        refine ⟨Fin.cons t x', heval, ?_⟩
        simp only [piTailHead_apply, Fin.tail_cons, Fin.cons_zero]
    have hZW : Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1) Z =
        ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (gaussianReal 0 1)) ((piTailHead m) '' Z) := by
      have hmp := measurePreserving_piTailHead m
      rw [← hmp.map_eq,
        Measure.map_apply (piTailHead m).measurable hWmeas,
        Set.preimage_image_eq _ (piTailHead m).injective]
    have hprod : ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (gaussianReal 0 1)) ((piTailHead m) '' Z) = 0 := by
      rw [Measure.prod_apply hWmeas,
        lintegral_eq_zero_iff (measurable_measure_prodMk_left hWmeas)]
      have hmem : {x' : Fin m → ℝ | x' ∉
          {x' | MvPolynomial.eval x' ((MvPolynomial.finSuccEquiv ℝ m p).coeff k₀) = 0}} ∈
          MeasureTheory.ae (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
        rw [mem_ae_iff]
        have hcompl : {x' : Fin m → ℝ | x' ∉
            {x' | MvPolynomial.eval x' ((MvPolynomial.finSuccEquiv ℝ m p).coeff k₀) = 0}}ᶜ =
            {x' | MvPolynomial.eval x' ((MvPolynomial.finSuccEquiv ℝ m p).coeff k₀) = 0} := by
          ext x'
          simp
        rw [hcompl]
        exact hIH
      have hae : ∀ᵐ x' ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1),
          x' ∉ {x' | MvPolynomial.eval x'
            ((MvPolynomial.finSuccEquiv ℝ m p).coeff k₀) = 0} := hmem
      filter_upwards [hae] with x' hx'
      simp only [Pi.zero_apply]
      have hmapne : (MvPolynomial.finSuccEquiv ℝ m p).map
          (MvPolynomial.eval x') ≠ 0 := by
        intro hz
        apply hx'
        have hcc := congrArg (fun Q => Polynomial.coeff Q k₀) hz
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcc
        exact hcc
      have hsec : Prod.mk x' ⁻¹' ((piTailHead m) '' Z) =
          {t | ((MvPolynomial.finSuccEquiv ℝ m p).map
            (MvPolynomial.eval x')).eval t = 0} := by
        ext t
        simp only [Set.mem_preimage]
        rw [hWchar, MvPolynomial.eval_eq_eval_mv_eval']
        exact Iff.rfl
      rw [hsec]
      exact polynomial_zeroSet_null hmapne
    rw [hZW]
    exact hprod

/-
### Reindexing to arbitrary finite index types

The engine above is stated for `Fin m`. Transport along `Fintype.equivFin`
via `measurePreserving_piCongrLeft`, pushing the polynomial forward with
`MvPolynomial.rename` (using `eval_rename` for the preimage identity).
-/

/-- Null-set lemma for Gaussian products over an arbitrary finite index type. -/
theorem mvPolynomial_zeroSet_null_pi_fintype {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    Measure.pi (fun _ : σ => gaussianReal 0 1)
      {x : σ → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : σ => ℝ) e.symm)
      (Measure.pi fun _ : Fin (Fintype.card σ) => gaussianReal 0 1)
      (Measure.pi fun _ : σ => gaussianReal 0 1) :=
    measurePreserving_piCongrLeft (fun _ : σ => gaussianReal 0 1) e.symm
  have hφapply : ∀ y : Fin (Fintype.card σ) → ℝ,
      MeasurableEquiv.piCongrLeft (fun _ : σ => ℝ) e.symm y = y ∘ ⇑e := by
    intro y
    ext s
    have hs : s = e.symm (e s) := (e.symm_apply_apply s).symm
    rw [hs, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      Function.comp_apply, e.apply_symm_apply]
  set q : MvPolynomial (Fin (Fintype.card σ)) ℝ := MvPolynomial.rename (⇑e) p with hq
  have hqne : q ≠ 0 := by
    intro hz
    apply hp
    have hinj : Function.Injective (MvPolynomial.rename (⇑e) :
        MvPolynomial σ ℝ → MvPolynomial (Fin (Fintype.card σ)) ℝ) :=
      MvPolynomial.rename_injective _ e.injective
    apply hinj
    rw [hq] at hz
    rw [hz, map_zero]
  have hmeas : MeasurableSet {x : σ → ℝ | MvPolynomial.eval x p = 0} :=
    mvPolynomial_zeroSet_measurable p
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : σ => ℝ) e.symm) ⁻¹'
        {x : σ → ℝ | MvPolynomial.eval x p = 0}
      = {y : Fin (Fintype.card σ) → ℝ | MvPolynomial.eval y q = 0} := by
    ext y
    simp only [Set.mem_preimage]
    show MvPolynomial.eval (MeasurableEquiv.piCongrLeft (fun _ : σ => ℝ) e.symm y) p = 0
      ↔ MvPolynomial.eval y q = 0
    rw [hφapply y, hq, MvPolynomial.eval_rename]
  have hnull := mvPolynomial_zeroSet_null_pi (Fintype.card σ) q hqne
  have hmap := hmp.map_eq
  have h1 : Measure.pi (fun _ : σ => gaussianReal 0 1)
        {x : σ → ℝ | MvPolynomial.eval x p = 0}
      = (Measure.pi fun _ : Fin (Fintype.card σ) => gaussianReal 0 1)
        ((MeasurableEquiv.piCongrLeft (fun _ : σ => ℝ) e.symm) ⁻¹'
          {x : σ → ℝ | MvPolynomial.eval x p = 0}) := by
    rw [← hmap, Measure.map_apply hmp.measurable hmeas]
  rw [h1, hpre]
  exact hnull

/-
### Uncurrying transport: nested products vs sigma-indexed products

The paper's sample law is a nested product (`Fin n` outer, `Fin d` inner).
The uncurrying map to the flat sigma-indexed product is measure preserving,
proved via `Measure.pi_eq`: the preimage of a flat cylinder is a nested
cylinder, and both sides factor by `Measure.pi_pi` plus `Fintype.prod_sigma`.
-/

/-- Uncurrying from the nested Gaussian product to the flat sigma-indexed
Gaussian product is measure preserving. -/
theorem measurePreserving_piCurry_symm_gaussian (n d : ℕ) :
    MeasurePreserving ⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1)
      (Measure.pi fun _ : Σ _ : Fin n, Fin d => gaussianReal 0 1) := by
  refine ⟨(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm.measurable, ?_⟩
  have hmap : Measure.map
        ⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = Measure.pi fun _ : Σ _ : Fin n, Fin d => gaussianReal 0 1 := by
    refine (Measure.pi_eq (μ := fun _ : Σ _ : Fin n, Fin d => gaussianReal 0 1) ?h).symm
    intro s hs
    have hpi : MeasurableSet (Set.pi Set.univ s) := by
      have hcount : (Set.univ : Set (Σ _ : Fin n, Fin d)).Countable :=
        Set.finite_univ.countable
      rw [measurableSet_pi hcount]
      exact Or.inl (fun i _ => hs i)
    have hpre : ⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm ⁻¹'
          (Set.pi Set.univ s)
        = Set.pi Set.univ (fun i : Fin n => Set.pi Set.univ (fun j : Fin d => s ⟨i, j⟩)) := by
      ext y
      simp only [Set.mem_preimage, MeasurableEquiv.coe_piCurry_symm, Set.mem_pi, Set.mem_univ,
        true_imp_iff, Sigma.forall]
      exact Iff.rfl
    rw [Measure.map_apply
      (MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm.measurable hpi, hpre]
    simp only [Measure.pi_pi]
    exact (Fintype.prod_sigma
      (fun p : Σ _ : Fin n, Fin d => gaussianReal 0 1 (s p))).symm
  exact hmap

/-- Null-set lemma for the paper's sample law: a nonzero polynomial in the
sample entries vanishes only on a `gaussianSampleLaw`-null set. -/
theorem mvPolynomial_zeroSet_null_sample (d n : ℕ) (p : MvPolynomial (Fin n × Fin d) ℝ)
    (hp : p ≠ 0) :
    gaussianSampleLaw d n
      {x : Sample d n | MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) p = 0} = 0 := by
  have hmp := measurePreserving_piCurry_symm_gaussian n d
  let eS : (Σ _ : Fin n, Fin d) ≃ Fin n × Fin d :=
    Equiv.sigmaEquivProd (Fin n) (Fin d)
  set q : MvPolynomial (Σ _ : Fin n, Fin d) ℝ := MvPolynomial.rename (⇑eS.symm) p with hq
  have hqne : q ≠ 0 := by
    intro hz
    apply hp
    have hinj : Function.Injective (MvPolynomial.rename (⇑eS.symm) :
        MvPolynomial (Fin n × Fin d) ℝ → MvPolynomial (Σ _ : Fin n, Fin d) ℝ) :=
      MvPolynomial.rename_injective _ eS.symm.injective
    apply hinj
    rw [hq] at hz
    rw [hz, map_zero]
  have hnull := mvPolynomial_zeroSet_null_pi_fintype q hqne
  have hcont : Continuous (fun x : Sample d n =>
      MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) p) := by
    refine (mvPolynomial_eval_continuous p).comp ?_
    exact continuous_pi_iff.mpr
      (fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hpre : ⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm ⁻¹'
        {y : (Σ _ : Fin n, Fin d) → ℝ | MvPolynomial.eval y q = 0}
      = {x : Sample d n | MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) p = 0} := by
    ext x
    simp only [Set.mem_preimage]
    show MvPolynomial.eval (⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm x) q = 0
      ↔ MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) p = 0
    rw [hq, MvPolynomial.eval_rename]
    have hpt : (⇑(MeasurableEquiv.piCurry (fun _ : Fin n => fun _ : Fin d => ℝ)).symm x ∘
        ⇑eS.symm) = fun ij : Fin n × Fin d => x ij.1 ij.2 := by
      ext ⟨i, j⟩
      rfl
    rw [hpt]
  have hmap := hmp.map_eq
  have h1 : gaussianSampleLaw d n
        {x : Sample d n | MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) p = 0}
      = (Measure.pi fun _ : Σ _ : Fin n, Fin d => gaussianReal 0 1)
        {y : (Σ _ : Fin n, Fin d) → ℝ | MvPolynomial.eval y q = 0} := by
    show (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1) _ = _
    rw [← hpre, ← hmap,
      Measure.map_apply hmp.measurable (mvPolynomial_zeroSet_measurable q)]
  rw [h1]
  exact hnull

/-
### The minor determinant polynomial and almost-sure spanning

When `d ≤ n`, the determinant of the top `d × d` minor is a nonzero polynomial
in the sample entries (it evaluates to 1 at the identity point). Hence the
minor is nonsingular a.s., the samples span a.s., and the Gram matrix is
positive definite a.s. (via `ExactFit.gram_posDef_iff_span_eq_top`).
-/

/-- The top `d × d` minor of the sample matrix, as a matrix over the reals. -/
def minorMatrix {d n : ℕ} (x : Sample d n) (h : d ≤ n) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of (fun a b : Fin d => x (Fin.castLE h a) b)

/-- The minor determinant as a polynomial in the sample entries. -/
def minorDetPoly {d n : ℕ} (h : d ≤ n) : MvPolynomial (Fin n × Fin d) ℝ :=
  Matrix.det (Matrix.of (fun a b : Fin d => MvPolynomial.X (Fin.castLE h a, b)))

/-- The minor determinant polynomial is nonzero: it sends the identity point to 1. -/
theorem minorDetPoly_ne_zero {d n : ℕ} (h : d ≤ n) : minorDetPoly h ≠ 0 := by
  set pt : Fin n × Fin d → ℝ := fun ij => if ij.1.val = ij.2.val then 1 else 0 with hpt
  have heval : MvPolynomial.eval pt (minorDetPoly h) = 1 := by
    unfold minorDetPoly
    rw [RingHom.map_det]
    have hmat : (MvPolynomial.eval pt).mapMatrix
          (Matrix.of (fun a b : Fin d => MvPolynomial.X (Fin.castLE h a, b))) = 1 := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        MvPolynomial.eval_X, hpt, Matrix.one_apply, Fin.val_castLE]
      by_cases hab : a = b
      · subst hab; simp
      · have hne : (↑a : ℕ) ≠ ↑b := fun h => hab (Fin.ext h)
        rw [ite_eq_right hab, ite_eq_right hne]
    rw [hmat, Matrix.det_one]
  intro hz
  rw [hz, map_zero] at heval
  exact zero_ne_one heval

/-- Evaluating the minor polynomial at a sample recovers the minor determinant. -/
theorem eval_minorDetPoly {d n : ℕ} (x : Sample d n) (h : d ≤ n) :
    MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) (minorDetPoly h)
      = Matrix.det (minorMatrix x h) := by
  unfold minorDetPoly minorMatrix
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [Matrix.map_apply, MvPolynomial.eval_X]

/-- The top minor is nonsingular almost surely. -/
theorem minor_det_ne_zero_ae {d n : ℕ} (h : d ≤ n) :
    ∀ᵐ x ∂gaussianSampleLaw d n, Matrix.det (minorMatrix x h) ≠ 0 := by
  have hnull := mvPolynomial_zeroSet_null_sample d n (minorDetPoly h) (minorDetPoly_ne_zero h)
  have hmem : {x : Sample d n | Matrix.det (minorMatrix x h) ≠ 0} ∈
      ae (gaussianSampleLaw d n) := by
    rw [mem_ae_iff]
    have hset : {x : Sample d n | Matrix.det (minorMatrix x h) ≠ 0}ᶜ
        = {x : Sample d n |
          MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) (minorDetPoly h) = 0} := by
      ext x
      simp only [Set.mem_compl_iff]
      show ¬ Matrix.det (minorMatrix x h) ≠ 0
        ↔ MvPolynomial.eval (fun ij : Fin n × Fin d => x ij.1 ij.2) (minorDetPoly h) = 0
      rw [not_not, eval_minorDetPoly]
    rw [hset]
    exact hnull
  exact hmem

/-- Gaussian samples span the ambient space almost surely (when `0 < d ≤ n`). -/
theorem span_eq_top_ae {d n : ℕ} (hd : 0 < d) (h : d ≤ n) :
    ∀ᵐ x ∂gaussianSampleLaw d n, Submodule.span ℝ (Set.range x) = ⊤ := by
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  filter_upwards [minor_det_ne_zero_ae h] with x hx
  have hLI : LinearIndependent ℝ (Matrix.row (minorMatrix x h)) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hx
  have hspan : Submodule.span ℝ (Set.range (Matrix.row (minorMatrix x h))) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (Module.finrank_pi ℝ).symm
  have hsub : Set.range (Matrix.row (minorMatrix x h)) ⊆ Set.range x := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Fin.castLE h a, rfl⟩
  have htop : (⊤ : Submodule ℝ (Vector d)) ≤ Submodule.span ℝ (Set.range x) := by
    have hle : Submodule.span ℝ (Set.range (Matrix.row (minorMatrix x h)))
        ≤ Submodule.span ℝ (Set.range x) :=
      Submodule.span_le.mpr (fun _ hy => Submodule.subset_span (hsub hy))
    rwa [hspan] at hle
  exact top_le_iff.mp htop

/-- The sample Gram matrix is positive definite almost surely. -/
theorem gram_posDef_ae {d n : ℕ} (hd : 0 < d) (h : d ≤ n) :
    ∀ᵐ x ∂gaussianSampleLaw d n, (gram x).PosDef := by
  filter_upwards [span_eq_top_ae hd h] with x hx
  exact (gram_posDef_iff_span_eq_top x).mpr hx
