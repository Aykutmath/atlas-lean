import Section_10_Zonoid.Hypercube.Geometry

/- Exact positive/negative mass convention of source line 186. -/

noncomputable section

namespace Hypercube.Geometry

theorem max_zero_eq_half_abs_add (a : Real) :
    max a 0 = (|a| + a) / 2 := by
  by_cases ha : 0 <= a
  next => rw [max_eq_left ha, abs_of_nonneg ha]; ring
  next =>
    have hn : a <= 0 := le_of_not_ge ha
    rw [max_eq_right hn, abs_of_nonpos hn]
    ring

theorem positive_cofactor_mass_eq_radonMass {m : Nat}
    (w : Fin (m + 2) -> Point m) :
    Finset.sum Finset.univ (fun i => max (cofactor w i) 0) = radonMass w := by
  simp_rw [max_zero_eq_half_abs_add]
  rw [<- Finset.sum_div, Finset.sum_add_distrib, cofactor_sum_zero, add_zero]
  unfold radonMass
  ring

theorem negative_cofactor_mass_eq_radonMass {m : Nat}
    (w : Fin (m + 2) -> Point m) :
    Finset.sum Finset.univ (fun i => max (-cofactor w i) 0) = radonMass w := by
  simp_rw [max_zero_eq_half_abs_add, abs_neg]
  rw [<- Finset.sum_div, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    cofactor_sum_zero, neg_zero, add_zero]
  unfold radonMass
  ring

end Hypercube.Geometry
