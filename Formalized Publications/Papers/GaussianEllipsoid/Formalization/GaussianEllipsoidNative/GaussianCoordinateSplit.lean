import GaussianDisjointSamples

/-!
Exact transport from the original standard Gaussian observations to the
independent left/right coordinate blocks used by the rectangular bilinear map.
Source: paper.tex, introductory below-threshold coordinate split (lines 350–363).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.ProjectedClusters

/-- Extract two coordinate blocks from each original scalar Gaussian sample. -/
def splitCoordinateEntries {d h : ℕ} (n : ℕ) (eA eB : Fin h ↪ Fin d)
    (x : GaussianEntries n d) : GaussianEntries n h × GaussianEntries n h :=
  (fun ia => x (ia.1, eA ia.2), fun ib => x (ib.1, eB ib.2))

theorem measurable_splitCoordinateEntries {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) : Measurable (splitCoordinateEntries n eA eB) :=
  (measurable_pi_iff.mpr (fun ia => measurable_pi_apply (ia.1, eA ia.2))).prodMk
    (measurable_pi_iff.mpr (fun ib => measurable_pi_apply (ib.1, eB ib.2)))

/-- The two extracted coordinate families have the exact tensor Gaussian law.
Disjointness is a literal property of the coordinate injections; no independence
or pushforward-law assumption is introduced. -/
theorem splitCoordinateEntries_preserving {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (hd : ∀ a b, eA a ≠ eB b) :
    MeasurePreserving (splitCoordinateEntries n eA eB)
      (gaussianProductLaw (Fin n × Fin d)) (tensorGaussianLaw n h) := by
  let fA : Fin n × Fin h → Fin n × Fin d := fun ia => (ia.1, eA ia.2)
  let fB : Fin n × Fin h → Fin n × Fin d := fun ib => (ib.1, eB ib.2)
  have hA : Function.Injective fA := by
    intro a b hab
    exact Prod.ext (congrArg (fun z : Fin n × Fin d => z.1) hab)
      (eA.injective (congrArg Prod.snd hab))
  have hB : Function.Injective fB := by
    intro a b hab
    exact Prod.ext (congrArg (fun z : Fin n × Fin d => z.1) hab)
      (eB.injective (congrArg Prod.snd hab))
  have hAB : ∀ a b, fA a ≠ fB b := by
    intro a b hab
    exact hd a.2 b.2 (congrArg Prod.snd hab)
  let f : (Fin n × Fin h) ⊕ (Fin n × Fin h) → Fin n × Fin d := Sum.elim fA fB
  have hsel : MeasurePreserving
      (fun x : GaussianEntries n d => fun i => x (f i))
      (gaussianProductLaw (Fin n × Fin d))
      (gaussianProductLaw ((Fin n × Fin h) ⊕ (Fin n × Fin h))) :=
    ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i)),
      gaussianProductLaw_map_subfamily f (hA.sumElim hB hAB)⟩
  exact (measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin n × Fin h) ⊕ (Fin n × Fin h) => gaussianReal 0 1)).comp hsel

theorem gaussianProductLaw_map_splitCoordinateEntries {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (hd : ∀ a b, eA a ≠ eB b) :
    (gaussianProductLaw (Fin n × Fin d)).map (splitCoordinateEntries n eA eB) =
      tensorGaussianLaw n h :=
  (splitCoordinateEntries_preserving n eA eB hd).map_eq

/-- The same extraction from original observations represented as genuine
Euclidean vectors. -/
def splitCoordinateRows {d h : ℕ} (n : ℕ) (eA eB : Fin h ↪ Fin d)
    (x : Fin n → Euclid d) : GaussianEntries n h × GaussianEntries n h :=
  splitCoordinateEntries n eA eB (rowsToEntries n d x)

theorem measurable_splitCoordinateRows {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) : Measurable (splitCoordinateRows n eA eB) :=
  (measurable_splitCoordinateEntries n eA eB).comp (measurable_rowsToEntries n d)

/-- Actual iid N(0,I_d) observation vectors yield the tensor Gaussian law
under any two disjoint deterministic coordinate embeddings. -/
theorem splitCoordinateRows_preserving {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (hd : ∀ a b, eA a ≠ eB b) :
    MeasurePreserving (splitCoordinateRows n eA eB)
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d)))
      (tensorGaussianLaw n h) :=
  (splitCoordinateEntries_preserving n eA eB hd).comp (rowsToEntries_preserving n d)

theorem euclideanRowsLaw_map_splitCoordinateRows {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (hd : ∀ a b, eA a ≠ eB b) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).map
      (splitCoordinateRows n eA eB) = tensorGaussianLaw n h :=
  (splitCoordinateRows_preserving n eA eB hd).map_eq

@[simp] theorem splitCoordinateRows_fst {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (x : Fin n → Euclid d) (i : Fin n) (a : Fin h) :
    (splitCoordinateRows n eA eB x).1 (i,a) = x i (eA a) := rfl

@[simp] theorem splitCoordinateRows_snd {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (x : Fin n → Euclid d) (i : Fin n) (b : Fin h) :
    (splitCoordinateRows n eA eB x).2 (i,b) = x i (eB b) := rfl

@[simp] theorem splitCoordinateRows_entriesToRows {d h : ℕ} (n : ℕ)
    (eA eB : Fin h ↪ Fin d) (x : GaussianEntries n d) :
    splitCoordinateRows n eA eB (entriesToRows n d x) =
      splitCoordinateEntries n eA eB x := rfl

@[simp] theorem selectSample_splitCoordinateEntries {n p d h : ℕ}
    (e : Fin p ↪ Fin n) (eA eB : Fin h ↪ Fin d) (x : GaussianEntries n d) :
    selectSample e (splitCoordinateEntries n eA eB x) =
      splitCoordinateEntries p eA eB (selectEntries e x) := rfl

end GaussianEllipsoid.ProjectedClusters
