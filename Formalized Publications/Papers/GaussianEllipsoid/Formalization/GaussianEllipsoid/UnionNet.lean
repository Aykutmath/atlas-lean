/-
Union-net escape module (UC7 slices C.2+C.3): per-net-point escape margins
plus Lipschitz transfer imply global escape, with the union bound over the
`Fin N` net stated explicitly.

STANDALONE VARIANT (Mathlib-only imports): the project-importing variant
was blocked because the project's own oleans are unbuilt and the repo is
read-only, so this file proves the full composition from Mathlib grounds
with zero sorries/axioms. Instantiation mapping to the real sources:

- `union_net_theorem` below with `val := conicMargin x` and
  `s := {S | S.PosSemidef ∧ frobeniusNorm S = 1}` is exactly the
  composition `conicInf_ge_net_min_of_abs_cover` + per-center margins
  (`sInf (val '' s) = conicInf d n x` by the unfold in
  `GaussianEllipsoid/ConicNets.lean`, lines 104-110).
- `escape_margin_notMem` is `EscapePieces.notMem_of_escapeMargin`,
  re-proved inline (same 5-line proof).
- Per-net-point probabilistic margins come from
  `gaussianConcShiftedUpper_of_lower`
  (`GaussianEllipsoid/GaussConcentration.lean`) upstream; the union
  bound lifting them to the whole net is proved here.

Net cardinality/packing enters ONLY as explicit cover/card hypotheses
(`Fin N` index, `N • p` bound, `hcover` premises). No volume comparison,
no net-existence argument, and no Gaussian input is proved here.

Mathematical source: paper.tex, ll.3465-3568 (escape inequality),
ll.3607-3640 (union over row sets), ll.3795-3810 (nets-entropy),
ll.4191-4210 (net approximation / Lipschitz transfer).
-/
import GaussianEllipsoid.EscapePieces
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory Finset

/-! ### Union bound over a `Fin N` net -/

/-- Union bound over a finite net indexed by `Fin N`: per-point failure
probabilities `≤ p` give total failure `≤ N • p`. Net cardinality enters
only as the explicit factor `N`. Proved by `Finset` induction via
`measure_union_le` (no measurability side conditions needed). -/
theorem prob_iUnion_le_card_smul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (E : Fin N → Set Ω) {p : ENNReal}
    (h : ∀ k, P (E k) ≤ p) :
    P (⋃ k, E k) ≤ N • p := by
  have key : ∀ s : Finset (Fin N),
      P (⋃ k ∈ s, E k) ≤ ∑ k ∈ s, P (E k) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s has ih =>
      have hun : (⋃ k ∈ insert a s, E k) = E a ∪ ⋃ k ∈ s, E k := by
        ext ω
        simp
      rw [hun, Finset.sum_insert has]
      exact le_trans (measure_union_le _ _) (add_le_add le_rfl ih)
  have hunion : (⋃ k, E k)
      = ⋃ k ∈ (Finset.univ : Finset (Fin N)), E k := by
    ext ω
    simp
  rw [hunion]
  calc P (⋃ k ∈ (Finset.univ : Finset (Fin N)), E k)
      ≤ ∑ k ∈ (Finset.univ : Finset (Fin N)), P (E k) := key Finset.univ
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin N)), p :=
        Finset.sum_le_sum (fun k _ => h k)
    _ = N • p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Net failure-event bound: packaging of `prob_iUnion_le_card_smul`. -/
theorem union_net_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (bad : Fin N → Set Ω) {p : ENNReal}
    (h : ∀ k, P (bad k) ≤ p) :
    P (⋃ k, bad k) ≤ N • p :=
  prob_iUnion_le_card_smul P bad h

/-- Complement form: if each net point is good except with probability
`≤ p`, all net points are simultaneously good except with `≤ N • p`. -/
theorem union_net_good_compl {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (g : Fin N → Set Ω) {p : ENNReal}
    (h : ∀ k, P (g k)ᶜ ≤ p) :
    P (⋂ k, g k)ᶜ ≤ N • p := by
  have hcompl : (⋂ k, g k)ᶜ = ⋃ k, (g k)ᶜ := by
    ext ω
    simp
  rw [hcompl]
  exact prob_iUnion_le_card_smul P (fun k => (g k)ᶜ) h

/-! ### Deterministic net→continuum escape -/

/-- Union-net theorem: a per-net-point escape margin `m + e` at every
center plus an `e`-Lipschitz-transfer cover of the continuum yields the
global escape bound `m ≤ sInf (val '' s)`. With
`val := conicMargin x`, this is the `conicInf` global escape via
`conicInf_ge_net_min_of_abs_cover`. -/
theorem union_net_theorem {α : Type*} {s : Set α} (hne : s.Nonempty)
    {N : ℕ} (hN : 0 < N) (val : α → ℝ) (centers : Fin N → α)
    {m e : ℝ}
    (hmargin : ∀ k : Fin N, m + e ≤ val (centers k))
    (hcover : ∀ a ∈ s, ∃ k : Fin N, |val a - val (centers k)| ≤ e) :
    m ≤ sInf (val '' s) := by
  obtain ⟨k0⟩ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨kmin, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (fun k => val (centers k))
      ⟨k0, Finset.mem_univ k0⟩
  have him : (val '' s).Nonempty := hne.image val
  have hle : val (centers kmin) - e ≤ sInf (val '' s) := by
    apply le_csInf him
    rintro t ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := hcover a ha
    have hkk : val (centers kmin) ≤ val (centers k) :=
      hmin k (Finset.mem_univ k)
    have hneg : -(val a - val (centers k)) ≤ |val a - val (centers k)| :=
      neg_le_abs _
    linarith
  have hc := hmargin kmin
  linarith

/-- Union-net escape (metric-space form, C.2+C.3 combined): the net covers
`E` at radius `e` and each center keeps margin `r + e` from `x`, so `x`
escapes the `r`-neighborhood of `E` by the triangle inequality plus
`notMem_of_escapeMargin`. -/
theorem union_net_notMem {X : Type*} [PseudoMetricSpace X]
    {E : Set X} {x : X} {r e : ℝ} {N : ℕ}
    (centers : Fin N → X)
    (hcover : ∀ y ∈ E, ∃ k : Fin N, dist (centers k) y ≤ e)
    (hmargin : ∀ k : Fin N, r + e ≤ dist x (centers k)) :
    x ∉ {z | ∃ y ∈ E, dist z y < r} := by
  apply notMem_of_escapeMargin
  intro y hyE
  obtain ⟨k, hk⟩ := hcover y hyE
  have htri := dist_triangle x y (centers k)
  rw [dist_comm y (centers k)] at htri
  have hm := hmargin k
  linarith

end GaussianEllipsoid
