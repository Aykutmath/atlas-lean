/-
Discharge of `dsNetCard` (DSCovariance net premise) from the volumetric
net construction (VolNets): the unit ball in `Vector d` admits an
eps-net of cardinality `≤ ⌈(1+2/eps)^d⌉`.
-/
import GaussianEllipsoid.DSCovariance
import GaussianEllipsoid.VolNets

namespace GaussianEllipsoid

theorem dsNetCard_of_volnets : dsNetCard := by
  intro d eps heps
  obtain ⟨T, hball, hnet, hcard⟩ :=
    exists_net_euclidNorm d 1 eps (show (0 : ℝ) ≤ 1 by norm_num) heps
  classical
  let e : ↥T ≃ Fin T.card :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])
  refine ⟨T.card, fun k => (e.symm k).val, ?_, ?_, ?_⟩
  · have hform : (1 : ℝ) + 2 * 1 / eps = 1 + 2 / eps := by ring
    rw [hform] at hcard
    exact_mod_cast hcard
  · intro k
    exact hball _ (e.symm k).property
  · intro u hu
    obtain ⟨c, hcT, hlt⟩ := hnet u hu
    refine ⟨e ⟨c, hcT⟩, ?_⟩
    show euclidNorm (u - (e.symm (e ⟨c, hcT⟩)).val) ≤ eps
    have hsym : e.symm (e ⟨c, hcT⟩) = (⟨c, hcT⟩ : ↥T) :=
      Equiv.symm_apply_apply e ⟨c, hcT⟩
    have hval : ((e.symm (e ⟨c, hcT⟩)).val) = c := by rw [hsym]
    rw [hval]
    exact le_of_lt hlt

end GaussianEllipsoid
