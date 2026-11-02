import BMNormalizedStein

/-! New reconstruction of the literal normalized row polynomial. The missing
PaperRowSecondStein namespace is supplied here as explicitly new support. -/
noncomputable section
open BMQuadraticStein MvPolynomial
open scoped BigOperators
namespace PaperRowSecondStein
variable {d : ℕ}

def rowPoly (R : Matrix (Fin d) (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  (1 / Real.sqrt 2) • centeredQuadratic R

end PaperRowSecondStein
namespace PaperCavityEndpointBridge
open PaperRowSecondStein
variable {d : ℕ}

theorem eval_rowPoly (R : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    eval w (rowPoly R) =
      ((∑ i, ∑ j, R i j * (w i * w j)) - Matrix.trace R) / Real.sqrt 2 := by
  rw [rowPoly, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_centeredQuadratic]
  ring

#print axioms eval_rowPoly
end PaperCavityEndpointBridge
