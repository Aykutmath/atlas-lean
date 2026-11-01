module

/-
# Lagrange-type Pythagorean identity for wedging (HI-LAGRANGE)

Elementary replacement for the exterior-algebra estimate in §3 of the paper
(`‖V ∧ w‖ ≤ ‖V‖ ‖w‖`). Mathlib's exterior algebra has no inner product on
exterior powers, so instead we prove the exact Pythagorean identity

  ‖c‖² Σ_U V_U² = Σ_T A_T² + Σ_W B_W²

where `A_T = Σ_{i ∈ T} σ(T,i) V_{T∖i} c_i` (the "wedge" coefficients) and
`B_W = Σ_{i ∉ W} σ(W∪i,i) V_{W∪i} c_i` (the "interior product" coefficients),
with `σ(S,i) = ∏_{j ∈ S} (if i < j then -1 else 1)`.

Dropping the nonnegative `B` sum gives the estimate needed for the local
Bernoulli bound (Lemma 3.1), with the same sharp constant. The paper's
statements are unchanged; only the proof device differs (see bridge note in
the coverage report).

Proof idea: expand both squares. Diagonal terms (`i = j`) give
`Σ_{U ∌ i} V_U² + Σ_{U ∋ i} V_U² = Σ_U V_U²`. Off-diagonal terms (`i ≠ j`)
reindex over `(d-1)`-sets avoiding `i, j`, where the two sign products are
exact opposites (`wedgeSign_insert_insert`) and cancel.
-/

public import Mathlib

namespace HypercubeInequality

open Finset

variable {N : ℕ}

/-- Wedge-order sign of `i` relative to the finset `S`: `(-1)` to the number
of elements of `S` greater than `i`, written as a product so that factoring
out one element is definitional. -/
@[expose] public noncomputable def wedgeSign (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  ∏ j ∈ S, (if i < j then (-1 : ℝ) else 1)

/-- The wedge-order sign squares to one. -/
public theorem wedgeSign_mul_self (S : Finset (Fin N)) (i : Fin N) :
    wedgeSign S i * wedgeSign S i = 1 := by
  unfold wedgeSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  by_cases h : i < j <;> simp [h]

/-- Key sign relation: on `T = insert i (insert j X)`, the product of the two
`T`-signs is the negation of the product of the two smaller signs. This is
what makes the off-diagonal terms cancel. -/
public theorem wedgeSign_insert_insert (X : Finset (Fin N)) {i j : Fin N}
    (hij : i ≠ j) (hiX : i ∉ X) (hjX : j ∉ X) :
    wedgeSign (insert i (insert j X)) i * wedgeSign (insert i (insert j X)) j
      = -(wedgeSign (insert i X) i * wedgeSign (insert j X) j) := by
  have hT : insert i (insert j X) = insert j (insert i X) :=
    Finset.insert_comm i j X
  have hji : j ∉ insert i X := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => hij h.symm, hjX⟩
  have hij' : i ∉ insert j X := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => hij h, hiX⟩
  have e1 : wedgeSign (insert i (insert j X)) i
      = (if i < j then (-1 : ℝ) else 1) * wedgeSign (insert i X) i := by
    rw [hT, wedgeSign, wedgeSign, Finset.prod_insert hji]
  have e2 : wedgeSign (insert i (insert j X)) j
      = (if j < i then (-1 : ℝ) else 1) * wedgeSign (insert j X) j := by
    rw [wedgeSign, wedgeSign, Finset.prod_insert hij']
  rw [e1, e2]
  by_cases h : i < j
  · rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h)]
    ring
  · have h2 : j < i := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hij)
    rw [ite_eq_right h, ite_eq_left h2]
    ring

/-- Reindexing: choosing `T ∈ powersetCard (e+1) s` and `i ∈ T` is the same
as choosing `i ∈ s` and `X ∈ powersetCard e (s.erase i)`, via `X = T.erase i`
and `T = insert i X`. -/
public theorem sum_powersetCard_mem (s : Finset (Fin N)) (e : ℕ)
    (F : Finset (Fin N) → Fin N → ℝ) :
    ∑ T ∈ Finset.powersetCard (e + 1) s, ∑ i ∈ T, F T i
      = ∑ i ∈ s, ∑ X ∈ Finset.powersetCard e (s.erase i),
        F (insert i X) i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
    (fun p _ => (⟨p.2, p.1.erase p.2⟩ : Sigma fun _ : Fin N => Finset (Fin N)))
  · intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hT, hiT⟩ := hp
    have hsub : p.1 ⊆ s := (Finset.mem_powersetCard.mp hT).1
    have hcard : (p.1).card = e + 1 := (Finset.mem_powersetCard.mp hT).2
    constructor
    · exact hsub hiT
    · rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, hsub hx.2⟩
      · rw [Finset.card_erase_of_mem hiT, hcard, Nat.add_sub_cancel]
  · intro p hp q hq heq
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    rw [Finset.mem_sigma] at hp hq
    obtain ⟨hT, hiT⟩ := hp
    obtain ⟨hU, hjU⟩ := hq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨hi, hX⟩ := heq
    have e1 : p1 = insert p2 (p1.erase p2) := (Finset.insert_erase hiT).symm
    have e2 : q1 = insert q2 (q1.erase q2) := (Finset.insert_erase hjU).symm
    subst hi
    have hX' : p1.erase p2 = q1.erase p2 := eq_of_heq hX
    have hfst : p1 = q1 := by rw [e1, e2, hX']
    subst hfst
    rfl
  · intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hi_s, hX⟩ := hq
    rw [Finset.mem_powersetCard] at hX
    obtain ⟨hXsub, hXcard⟩ := hX
    have hiX : q.1 ∉ q.2 := fun h => (Finset.notMem_erase q.1 s) (hXsub h)
    refine ⟨⟨insert q.1 q.2, q.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_powersetCard]
        constructor
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hi_s
          · exact Finset.erase_subset _ _ (hXsub hx)
        · rw [Finset.card_insert_of_notMem hiX, hXcard]
      · exact Finset.mem_insert_self q.1 q.2
    · show (⟨q.1, (insert q.1 q.2).erase q.1⟩ : Sigma fun _ : Fin N => Finset (Fin N)) = q
      rw [Finset.erase_insert hiX]
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hT, hiT⟩ := hp
    show F p.1 p.2 = F (insert p.2 (p.1.erase p.2)) p.2
    rw [Finset.insert_erase hiT]

/-- Reindexing: choosing `W ∈ powersetCard e s` and `i ∈ s \ W` is the same
as choosing `i ∈ s` and `U ∈ powersetCard (e+1) s` with `i ∈ U`, via
`U = insert i W` and `W = U.erase i`. -/
public theorem sum_powersetCard_sdiff (s : Finset (Fin N)) (e : ℕ)
    (F : Finset (Fin N) → Fin N → ℝ) :
    ∑ W ∈ Finset.powersetCard e s, ∑ i ∈ s \ W, F W i
      = ∑ i ∈ s, ∑ U ∈ (Finset.powersetCard (e + 1) s).filter (fun U => i ∈ U),
        F (U.erase i) i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
    (fun p _ => (⟨p.2, insert p.2 p.1⟩ : Sigma fun _ : Fin N => Finset (Fin N)))
  · intro p hp
    rw [Finset.mem_sigma] at hp ⊢
    obtain ⟨hW, hiW⟩ := hp
    rw [Finset.mem_sdiff] at hiW
    obtain ⟨hi_s, hiW⟩ := hiW
    have hsub : p.1 ⊆ s := (Finset.mem_powersetCard.mp hW).1
    have hcard : (p.1).card = e := (Finset.mem_powersetCard.mp hW).2
    constructor
    · exact hi_s
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · constructor
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact hi_s
          · exact hsub hx
        · rw [Finset.card_insert_of_notMem hiW, hcard]
      · exact Finset.mem_insert_self p.2 p.1
  · intro p hp q hq heq
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    rw [Finset.mem_sigma] at hp hq
    obtain ⟨hW, hiW⟩ := hp
    obtain ⟨hU, hjU⟩ := hq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨hi, hX⟩ := heq
    subst hi
    have hX' : insert p2 p1 = insert p2 q1 := eq_of_heq hX
    rw [Finset.mem_sdiff] at hiW hjU
    have h1 : (insert p2 p1).erase p2 = p1 := Finset.erase_insert hiW.2
    have h2 : (insert p2 q1).erase p2 = q1 := Finset.erase_insert hjU.2
    have hfst : p1 = q1 := by rw [← h1, ← h2, hX']
    subst hfst
    rfl
  · intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hi_s, hU⟩ := hq
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hU
    obtain ⟨⟨hUsub, hUcard⟩, hiU⟩ := hU
    refine ⟨⟨q.2.erase q.1, q.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_powersetCard]
        constructor
        · intro x hx
          rw [Finset.mem_erase] at hx
          exact hUsub hx.2
        · rw [Finset.card_erase_of_mem hiU, hUcard, Nat.add_sub_cancel]
      · rw [Finset.mem_sdiff]
        exact ⟨hi_s, Finset.notMem_erase q.1 q.2⟩
    · show (⟨q.1, insert q.1 (q.2.erase q.1)⟩ : Sigma fun _ : Fin N => Finset (Fin N)) = q
      rw [Finset.insert_erase hiU]
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hW, hiW⟩ := hp
    rw [Finset.mem_sdiff] at hiW
    show F p.1 p.2 = F ((insert p.2 p.1).erase p.2) p.2
    rw [Finset.erase_insert hiW.2]

/-- Off-diagonal cancellation: the `i ≠ j` parts of the two expanded squares
sum to zero. The bijection sends `(T, i, j)` to `(W, i, j)` with
`W = (T.erase i).erase j`, under which the two summands are exact negatives
by the sign relation `wedgeSign_insert_insert`. -/
public theorem sum_offdiag_cancel {d : ℕ} (hd : 1 ≤ d)
    (V : Finset (Fin N) → ℝ) (c : Fin N → ℝ) :
    (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ, ∑ i ∈ T, ∑ j ∈ T.erase i,
      (wedgeSign T i * V (T.erase i) * c i) * (wedgeSign T j * V (T.erase j) * c j))
    + (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ, ∑ i ∈ Finset.univ \ W,
      ∑ j ∈ (Finset.univ \ W).erase i,
      (wedgeSign (insert i W) i * V (insert i W) * c i) *
        (wedgeSign (insert j W) j * V (insert j W) * c j)) = 0 := by
  rw [Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  have h : (∑ q ∈ ((Finset.powersetCard (d + 1) Finset.univ).sigma fun T => T).sigma
          (fun p => p.1.erase p.2),
          (wedgeSign q.1.1 q.1.2 * V (q.1.1.erase q.1.2) * c q.1.2) *
            (wedgeSign q.1.1 q.2 * V (q.1.1.erase q.2) * c q.2))
      = ∑ q ∈ ((Finset.powersetCard (d - 1) Finset.univ).sigma
          fun W => Finset.univ \ W).sigma (fun p => (Finset.univ \ p.1).erase p.2),
        -(((wedgeSign (insert q.1.2 q.1.1) q.1.2 * V (insert q.1.2 q.1.1) * c q.1.2) *
          (wedgeSign (insert q.2 q.1.1) q.2 * V (insert q.2 q.1.1) * c q.2))) := by
    apply Finset.sum_bij (fun p _ =>
      (⟨⟨(p.1.1.erase p.1.2).erase p.2, p.1.2⟩, p.2⟩ :
        Sigma fun _ : Sigma fun _ : Finset (Fin N) => Fin N => Fin N))
    · intro p hp
      rw [Finset.mem_sigma] at hp ⊢
      obtain ⟨hp1, hjTe⟩ := hp
      rw [Finset.mem_sigma] at hp1
      obtain ⟨hT, hiT⟩ := hp1
      have hsub : p.1.1 ⊆ Finset.univ := (Finset.mem_powersetCard.mp hT).1
      have hcard : (p.1.1).card = d + 1 := (Finset.mem_powersetCard.mp hT).2
      have hjT : p.2 ∈ p.1.1 := (Finset.mem_erase.mp hjTe).2
      have hji : p.2 ≠ p.1.2 := (Finset.mem_erase.mp hjTe).1
      constructor
      · rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_powersetCard]
          constructor
          · intro x hx
            rw [Finset.mem_erase] at hx
            rw [Finset.mem_erase] at hx
            exact hsub hx.2.2
          · rw [Finset.card_erase_of_mem hjTe, Finset.card_erase_of_mem hiT, hcard]
            omega
        · rw [Finset.mem_sdiff]
          constructor
          · exact hsub hiT
          · intro hcon
            have hmem : p.1.2 ∈ p.1.1.erase p.1.2 :=
              (Finset.mem_erase.mp hcon).2
            exact (Finset.notMem_erase p.1.2 p.1.1) hmem
      · rw [Finset.mem_erase]
        constructor
        · exact hji
        · rw [Finset.mem_sdiff]
          constructor
          · exact hsub hjT
          · exact Finset.notMem_erase p.2 ((p.1.1.erase p.1.2))
    · intro p hp q hq heq
      obtain ⟨⟨pT, pi⟩, pj⟩ := p
      obtain ⟨⟨qT, qi⟩, qj⟩ := q
      rw [Finset.mem_sigma] at hp hq
      obtain ⟨hp1, hjTe⟩ := hp
      obtain ⟨hq1, hjUe⟩ := hq
      rw [Finset.mem_sigma] at hp1 hq1
      obtain ⟨hT, hiT⟩ := hp1
      obtain ⟨hU, hjU⟩ := hq1
      simp only [Sigma.mk.injEq] at heq
      obtain ⟨heq1, heqj⟩ := heq
      obtain ⟨heqW, heqi⟩ := heq1
      have heqj' : pj = qj := eq_of_heq heqj
      have heqi' : pi = qi := eq_of_heq heqi
      subst heqj'
      subst heqi'
      have hX' : (pT.erase pi).erase pj = (qT.erase pi).erase pj := heqW
      have eT : pT = insert pi (insert pj ((pT.erase pi).erase pj)) := by
        have h1 : pT.erase pi = insert pj ((pT.erase pi).erase pj) :=
          (Finset.insert_erase hjTe).symm
        have h2 : pT = insert pi (pT.erase pi) := (Finset.insert_erase hiT).symm
        rw [← h1, ← h2]
      have eU : qT = insert pi (insert pj ((qT.erase pi).erase pj)) := by
        have h1 : qT.erase pi = insert pj ((qT.erase pi).erase pj) :=
          (Finset.insert_erase hjUe).symm
        have h2 : qT = insert pi (qT.erase pi) := (Finset.insert_erase hjU).symm
        rw [← h1, ← h2]
      have hfst : pT = qT := by rw [eT, eU, hX']
      subst hfst
      rfl
    · intro q hq
      rw [Finset.mem_sigma] at hq
      obtain ⟨hq1, hjUe⟩ := hq
      rw [Finset.mem_sigma] at hq1
      obtain ⟨hW, hiW⟩ := hq1
      rw [Finset.mem_sdiff] at hiW
      obtain ⟨hi_s, hiW⟩ := hiW
      rw [Finset.mem_erase] at hjUe
      obtain ⟨hji, hjW⟩ := hjUe
      rw [Finset.mem_sdiff] at hjW
      obtain ⟨hj_s, hjW⟩ := hjW
      have hsub : q.1.1 ⊆ Finset.univ := (Finset.mem_powersetCard.mp hW).1
      have hcard : (q.1.1).card = d - 1 := (Finset.mem_powersetCard.mp hW).2
      have hij : q.1.2 ≠ q.2 := fun h => hji h.symm
      have hjS : q.2 ∉ insert q.1.2 q.1.1 := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hji, hjW⟩
      have hiS : q.1.2 ∉ insert q.2 q.1.1 := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hij, hiW⟩
      refine ⟨⟨⟨insert q.1.2 (insert q.2 q.1.1), q.1.2⟩, q.2⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        constructor
        · rw [Finset.mem_sigma]
          constructor
          · rw [Finset.mem_powersetCard]
            constructor
            · intro x hx
              simp only [Finset.mem_insert] at hx
              rcases hx with rfl | rfl | hx
              · exact hi_s
              · exact hj_s
              · exact hsub hx
            · rw [Finset.card_insert_of_notMem hiS,
                Finset.card_insert_of_notMem hjW, hcard,
                Nat.sub_add_cancel hd]
          · exact Finset.mem_insert_self q.1.2 (insert q.2 q.1.1)
        · rw [Finset.mem_erase]
          constructor
          · exact hji
          · exact Finset.mem_insert_of_mem
              (Finset.mem_insert_self q.2 q.1.1)
      · show (⟨⟨((insert q.1.2 (insert q.2 q.1.1)).erase q.1.2).erase q.2,
          q.1.2⟩, q.2⟩ :
          Sigma fun _ : Sigma fun _ : Finset (Fin N) => Fin N => Fin N) = q
        rw [Finset.erase_insert hiS, Finset.erase_insert hjW]
    · intro p hp
      rw [Finset.mem_sigma] at hp
      obtain ⟨hp1, hjTe⟩ := hp
      rw [Finset.mem_sigma] at hp1
      obtain ⟨hT, hiT⟩ := hp1
      have hjT : p.2 ∈ p.1.1 := (Finset.mem_erase.mp hjTe).2
      have hji : p.2 ≠ p.1.2 := (Finset.mem_erase.mp hjTe).1
      have hij : p.1.2 ≠ p.2 := fun h => hji h.symm
      set W : Finset (Fin N) := (p.1.1.erase p.1.2).erase p.2 with hWdef
      have hiW : p.1.2 ∉ W := by
        rw [hWdef]
        intro h
        exact (Finset.notMem_erase p.1.2 p.1.1)
          ((Finset.mem_erase.mp h).2)
      have hjW : p.2 ∉ W := by
        rw [hWdef]
        exact Finset.notMem_erase p.2 (p.1.1.erase p.1.2)
      have hTeq : p.1.1 = insert p.1.2 (insert p.2 W) := by
        have h1 : p.1.1.erase p.1.2 = insert p.2 W :=
          (Finset.insert_erase hjTe).symm
        have h2 : p.1.1 = insert p.1.2 (p.1.1.erase p.1.2) :=
          (Finset.insert_erase hiT).symm
        rw [h2, h1]
      have hE1 : p.1.1.erase p.1.2 = insert p.2 W :=
        (Finset.insert_erase hjTe).symm
      have hE2 : p.1.1.erase p.2 = insert p.1.2 W := by
        have hcomm : insert p.1.2 (insert p.2 W) = insert p.2 (insert p.1.2 W) :=
          Finset.insert_comm p.1.2 p.2 W
        have hjS : p.2 ∉ insert p.1.2 W := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hji, hjW⟩
        rw [hTeq, hcomm]
        exact Finset.erase_insert hjS
      have hσ : wedgeSign p.1.1 p.1.2 * wedgeSign p.1.1 p.2
          = -(wedgeSign (insert p.1.2 W) p.1.2 * wedgeSign (insert p.2 W) p.2) := by
        rw [hTeq]
        exact wedgeSign_insert_insert W hij hiW hjW
      have hV1 : V (p.1.1.erase p.1.2) = V (insert p.2 W) := by rw [hE1]
      have hV2 : p.1.1.erase p.2 = insert p.1.2 W := hE2
      show (wedgeSign p.1.1 p.1.2 * V (p.1.1.erase p.1.2) * c p.1.2) *
          (wedgeSign p.1.1 p.2 * V (p.1.1.erase p.2) * c p.2)
        = -(((wedgeSign (insert p.1.2 W) p.1.2 * V (insert p.1.2 W) * c p.1.2) *
          (wedgeSign (insert p.2 W) p.2 * V (insert p.2 W) * c p.2)))
      have e1 : (wedgeSign p.1.1 p.1.2 * V (p.1.1.erase p.1.2) * c p.1.2) *
            (wedgeSign p.1.1 p.2 * V (p.1.1.erase p.2) * c p.2)
          = (wedgeSign p.1.1 p.1.2 * wedgeSign p.1.1 p.2) *
            ((V (p.1.1.erase p.1.2) * V (p.1.1.erase p.2)) * (c p.1.2 * c p.2)) := by
        ring
      have e2 : (wedgeSign (insert p.1.2 W) p.1.2 * V (insert p.1.2 W) * c p.1.2) *
            (wedgeSign (insert p.2 W) p.2 * V (insert p.2 W) * c p.2)
          = (wedgeSign (insert p.1.2 W) p.1.2 * wedgeSign (insert p.2 W) p.2) *
            ((V (insert p.1.2 W) * V (insert p.2 W)) * (c p.1.2 * c p.2)) := by
        ring
      rw [e1, e2, hσ, hV1, hV2]
      ring
  rw [h, ← Finset.sum_add_distrib]
  simp

/-- Lagrange-type Pythagorean identity for wedging (elementary form).
For `V` on `d`-sets and `c` on points, the squared norm of `c` times the
squared norm of `V` equals the sum of the squared "wedge" coefficients plus
the sum of the squared "interior product" coefficients. Dropping the second
sum gives `‖V ∧ c‖ ≤ ‖V‖ ‖c‖`, the estimate behind Lemma 3.1. -/
public theorem wedge_pythagoras {d : ℕ} (hd : 1 ≤ d)
    (V : Finset (Fin N) → ℝ) (c : Fin N → ℝ) :
    (∑ i, (c i)^2) * (∑ U ∈ Finset.powersetCard d Finset.univ, (V U)^2)
      = (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
            (∑ i ∈ T, wedgeSign T i * V (T.erase i) * c i)^2)
        + (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
            (∑ i ∈ Finset.univ \ W,
              wedgeSign (insert i W) i * V (insert i W) * c i)^2) := by
  have hexpand1 : ∀ T : Finset (Fin N),
      (∑ i ∈ T, wedgeSign T i * V (T.erase i) * c i)^2
      = (∑ i ∈ T, (c i)^2 * (V (T.erase i))^2)
        + (∑ i ∈ T, ∑ j ∈ T.erase i,
            (wedgeSign T i * V (T.erase i) * c i) *
              (wedgeSign T j * V (T.erase j) * c j)) := by
    intro T
    rw [pow_two, Finset.sum_mul_sum]
    trans ∑ i ∈ T, ((wedgeSign T i * V (T.erase i) * c i) *
        (wedgeSign T i * V (T.erase i) * c i)
        + (∑ j ∈ T.erase i, (wedgeSign T i * V (T.erase i) * c i) *
          (wedgeSign T j * V (T.erase j) * c j)))
    · apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.add_sum_erase T _ hi).symm
    · rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hσ : wedgeSign T i * wedgeSign T i = 1 := wedgeSign_mul_self T i
        calc (wedgeSign T i * V (T.erase i) * c i) *
              (wedgeSign T i * V (T.erase i) * c i)
            = (wedgeSign T i * wedgeSign T i) *
              ((V (T.erase i) * V (T.erase i)) * (c i * c i)) := by ring
          _ = (c i)^2 * (V (T.erase i))^2 := by rw [hσ]; ring
  have hexpand2 : ∀ W : Finset (Fin N),
      (∑ i ∈ Finset.univ \ W,
        wedgeSign (insert i W) i * V (insert i W) * c i)^2
      = (∑ i ∈ Finset.univ \ W, (c i)^2 * (V (insert i W))^2)
        + (∑ i ∈ Finset.univ \ W, ∑ j ∈ (Finset.univ \ W).erase i,
            (wedgeSign (insert i W) i * V (insert i W) * c i) *
              (wedgeSign (insert j W) j * V (insert j W) * c j)) := by
    intro W
    rw [pow_two, Finset.sum_mul_sum]
    trans ∑ i ∈ Finset.univ \ W,
      ((wedgeSign (insert i W) i * V (insert i W) * c i) *
        (wedgeSign (insert i W) i * V (insert i W) * c i)
        + (∑ j ∈ (Finset.univ \ W).erase i,
          (wedgeSign (insert i W) i * V (insert i W) * c i) *
          (wedgeSign (insert j W) j * V (insert j W) * c j)))
    · apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.add_sum_erase _ _ hi).symm
    · rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hσ : wedgeSign (insert i W) i * wedgeSign (insert i W) i = 1 :=
          wedgeSign_mul_self _ _
        calc (wedgeSign (insert i W) i * V (insert i W) * c i) *
              (wedgeSign (insert i W) i * V (insert i W) * c i)
            = (wedgeSign (insert i W) i * wedgeSign (insert i W) i) *
              ((V (insert i W) * V (insert i W)) * (c i * c i)) := by ring
          _ = (c i)^2 * (V (insert i W))^2 := by rw [hσ]; ring
  have hR1 : (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
        (∑ i ∈ T, wedgeSign T i * V (T.erase i) * c i)^2)
      = (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
          ∑ i ∈ T, (c i)^2 * (V (T.erase i))^2)
        + (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
          ∑ i ∈ T, ∑ j ∈ T.erase i,
          (wedgeSign T i * V (T.erase i) * c i) *
            (wedgeSign T j * V (T.erase j) * c j)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun T _ => hexpand1 T)
  have hR2 : (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
        (∑ i ∈ Finset.univ \ W,
          wedgeSign (insert i W) i * V (insert i W) * c i)^2)
      = (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
          ∑ i ∈ Finset.univ \ W, (c i)^2 * (V (insert i W))^2)
        + (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
          ∑ i ∈ Finset.univ \ W, ∑ j ∈ (Finset.univ \ W).erase i,
          (wedgeSign (insert i W) i * V (insert i W) * c i) *
            (wedgeSign (insert j W) j * V (insert j W) * c j)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun W _ => hexpand2 W)
  have hD1 : (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
        ∑ i ∈ T, (c i)^2 * (V (T.erase i))^2)
      = ∑ i ∈ Finset.univ, ∑ X ∈ Finset.powersetCard d (Finset.univ.erase i),
        (c i)^2 * (V X)^2 := by
    rw [sum_powersetCard_mem]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro X hX
    rw [Finset.mem_powersetCard] at hX
    have hiX : i ∉ X := fun h => (Finset.notMem_erase i Finset.univ) (hX.1 h)
    rw [Finset.erase_insert hiX]
  have hD2 : (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
        ∑ i ∈ Finset.univ \ W, (c i)^2 * (V (insert i W))^2)
      = ∑ i ∈ Finset.univ,
        ∑ U ∈ (Finset.powersetCard d Finset.univ).filter (fun U => i ∈ U),
        (c i)^2 * (V U)^2 := by
    rw [sum_powersetCard_sdiff, Nat.sub_add_cancel hd]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.mem_filter] at hU
    rw [Finset.insert_erase hU.2]
  have hD : (∑ i ∈ Finset.univ,
        ∑ X ∈ Finset.powersetCard d (Finset.univ.erase i), (c i)^2 * (V X)^2)
      + (∑ i ∈ Finset.univ,
        ∑ U ∈ (Finset.powersetCard d Finset.univ).filter (fun U => i ∈ U),
        (c i)^2 * (V U)^2)
      = (∑ i, (c i)^2) * (∑ U ∈ Finset.powersetCard d Finset.univ, (V U)^2) := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hsplit : (∑ U ∈ (Finset.powersetCard d Finset.univ).filter
          (fun U => i ∈ U), (V U)^2)
        + (∑ X ∈ Finset.powersetCard d (Finset.univ.erase i), (V X)^2)
        = ∑ U ∈ Finset.powersetCard d Finset.univ, (V U)^2 := by
      have h0 := Finset.sum_filter_add_sum_filter_not
        (Finset.powersetCard d Finset.univ) (fun U => i ∈ U) (fun U => (V U)^2)
      rw [show (Finset.powersetCard d Finset.univ).filter (fun U => ¬ i ∈ U)
          = Finset.powersetCard d (Finset.univ.erase i) from ?_] at h0
      · exact h0
      · ext U
        rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard,
          Finset.subset_erase]
        constructor
        · rintro ⟨⟨hsub, hcard⟩, hni⟩
          exact ⟨⟨hsub, hni⟩, hcard⟩
        · rintro ⟨⟨hsub, hni⟩, hcard⟩
          exact ⟨⟨hsub, hcard⟩, hni⟩
    calc (∑ X ∈ Finset.powersetCard d (Finset.univ.erase i), (c i)^2 * (V X)^2)
          + (∑ U ∈ (Finset.powersetCard d Finset.univ).filter
            (fun U => i ∈ U), (c i)^2 * (V U)^2)
        = (c i)^2 * ((∑ X ∈ Finset.powersetCard d (Finset.univ.erase i), (V X)^2)
          + (∑ U ∈ (Finset.powersetCard d Finset.univ).filter
            (fun U => i ∈ U), (V U)^2)) := by
            rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ = (c i)^2 * (∑ U ∈ Finset.powersetCard d Finset.univ, (V U)^2) := by
          congr 1
          rw [add_comm]
          exact hsplit
  have hO : (∑ T ∈ Finset.powersetCard (d + 1) Finset.univ,
        ∑ i ∈ T, ∑ j ∈ T.erase i,
        (wedgeSign T i * V (T.erase i) * c i) *
          (wedgeSign T j * V (T.erase j) * c j))
      + (∑ W ∈ Finset.powersetCard (d - 1) Finset.univ,
        ∑ i ∈ Finset.univ \ W, ∑ j ∈ (Finset.univ \ W).erase i,
        (wedgeSign (insert i W) i * V (insert i W) * c i) *
          (wedgeSign (insert j W) j * V (insert j W) * c j)) = 0 :=
    sum_offdiag_cancel hd V c
  rw [hR1, hR2, hD1, hD2]
  linear_combination -hD - hO

end HypercubeInequality
