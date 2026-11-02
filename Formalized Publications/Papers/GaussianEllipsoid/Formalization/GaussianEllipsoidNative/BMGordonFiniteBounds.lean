import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Lattice

noncomputable section
open MeasureTheory
namespace BMGordon

variable {I J Ω : Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

def finiteValue (f : I → J → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i =>
    Finset.univ.sup' Finset.univ_nonempty (fun j => f i j ω))

theorem finiteValue_attained (f : I → J → Ω → ℝ) (ω : Ω) :
    ∃ i j, finiteValue f ω = f i j ω := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => Finset.univ.sup' Finset.univ_nonempty (fun j => f i j ω))
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => f i j ω)
  exact ⟨i,j,hi.trans hj⟩

theorem finiteValue_abs_le (f : I → J → Ω → ℝ) (b : Ω → ℝ)
    (hb : ∀ i j ω, |f i j ω| ≤ b ω) (ω : Ω) : |finiteValue f ω| ≤ b ω := by
  obtain ⟨i,j,hij⟩ := finiteValue_attained f ω
  rw [hij]
  exact hb i j ω

theorem finiteValue_continuous [TopologicalSpace Ω] (f : I → J → Ω → ℝ)
    (hf : ∀ i j, Continuous (f i j)) : Continuous (finiteValue f) := by
  apply Continuous.finset_inf'_apply
  intro i _
  apply Continuous.finset_sup'_apply
  intro j _
  exact hf i j

theorem finiteValue_integrable [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) (f : I → J → Ω → ℝ) (b : Ω → ℝ)
    (hf : ∀ i j, Continuous (f i j)) (hbint : Integrable b μ)
    (hb : ∀ i j ω, |f i j ω| ≤ b ω) : Integrable (finiteValue f) μ := by
  apply hbint.mono' (finiteValue_continuous f hf).aestronglyMeasurable
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using finiteValue_abs_le f b hb ω

end BMGordon
