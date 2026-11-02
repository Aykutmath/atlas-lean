import ActualSpectralPeeling
import UCGaussianRowBridge

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace UCEscape

lemma sourceFrobenius_opMatrix {d : ℕ} (T : Op d) :
    sourceFrobenius (opMatrix T) = operatorFrobenius T := by
  ext j i
  rfl

lemma opMatrix_sourceFrobenius {d : ℕ} (A : GaussianEllipsoid.Square d) :
    opMatrix (frobeniusOperator (sourceFrobenius A)) = A := by
  rw [opMatrix, operatorFrobenius_frobeniusOperator]
  rfl

lemma frobeniusNorm_opMatrix {d : ℕ} (T : Op d) :
    frobeniusNorm (opMatrix T) = ‖operatorFrobenius T‖ := by
  rw [← sourceFrobenius_norm, sourceFrobenius_opMatrix]

lemma matrixOpNorm_opMatrix {d : ℕ} (T : Op d) :
    matrixOpNorm (opMatrix T) = ‖T‖ := by
  change ‖(Matrix.toEuclideanLin (opMatrix T)).toContinuousLinearMap‖ = ‖T‖
  rw [opMatrix_toEuclideanLin]
  rfl

lemma opMatrix_add {d : ℕ} (T U : Op d) : opMatrix (T+U) = opMatrix T+opMatrix U := by
  ext i j
  rfl

lemma opMatrix_smul {d : ℕ} (c : ℝ) (T : Op d) : opMatrix (c • T) = c • opMatrix T := by
  ext i j
  rfl

lemma opMatrix_comp {d : ℕ} (T U : Op d) : opMatrix (T.comp U) = opMatrix T*opMatrix U := by
  simp only [opMatrix_eq_toMatrix]
  change LinearMap.toMatrix _ _ (T.toLinearMap.comp U.toLinearMap) = _
  exact LinearMap.toMatrix_comp
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis T.toLinearMap U.toLinearMap

lemma opMatrix_zero (d : ℕ) : opMatrix (0 : Op d) = 0 := by
  ext i j
  rfl

/-- Paper-faithful adaptive spectral peeling in the exact source project's
matrix and norm definitions, with K chosen before dimension and matrix. -/
theorem exists_project_spectral_peeling {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ K : ℕ, (1-τ^2)^K ≤ δ^2 ∧
      ∀ (d : ℕ) (A : GaussianEllipsoid.Square d), A.PosSemidef → frobeniusNorm A = 1 →
        ∃ H R : GaussianEllipsoid.Square d,
          H.PosSemidef ∧ R.PosSemidef ∧ A=H+R ∧ H*R=0 ∧ H.rank ≤ K ∧
          frobeniusNorm H^2+frobeniusNorm R^2=1 ∧
          (frobeniusNorm R ≤ δ ∨
            ∃ ρ : ℝ, ∃ D : GaussianEllipsoid.Square d,
              δ < ρ ∧ R=ρ • D ∧ D.PosSemidef ∧ H*D=0 ∧
              frobeniusNorm D=1 ∧ matrixOpNorm D ≤ τ) := by
  obtain ⟨K,hK,hpeel⟩ := BMGeometry.exists_uniform_normalized_spectral_peeling hτ hδ
  refine ⟨K,hK,?_⟩
  intro d A hA hF
  let T := frobeniusOperator (sourceFrobenius A)
  have hT : IsPSD T := (sourceFrobenius_psd A).mpr hA
  have hn : ‖operatorFrobenius T‖ = 1 := by
    change ‖operatorFrobenius (frobeniusOperator (sourceFrobenius A))‖ = 1
    rw [operatorFrobenius_frobeniusOperator, sourceFrobenius_norm, hF]
  obtain ⟨H,R,hH,hR,hdec,hcomp,_hrange,_hinner,_hrank,hmrank,henergy,hstop⟩ := hpeel d T hT hn
  refine ⟨opMatrix H,opMatrix R,(opMatrix_posSemidef_iff H).mpr hH,
    (opMatrix_posSemidef_iff R).mpr hR,?_,?_,hmrank,?_,?_⟩
  · have h := congrArg opMatrix hdec
    change opMatrix (frobeniusOperator (sourceFrobenius A)) = opMatrix (H+R) at h
    rw [opMatrix_sourceFrobenius, opMatrix_add] at h
    exact h
  · rw [← opMatrix_comp, hcomp, opMatrix_zero]
  · simpa only [frobeniusNorm_opMatrix] using henergy
  · rcases hstop with hsmall | ⟨ρ,D,hρ,hdec,hD,hzero,hunit,hdiff⟩
    · left
      simpa only [frobeniusNorm_opMatrix] using hsmall
    · right
      refine ⟨ρ,opMatrix D,hρ,?_,(opMatrix_posSemidef_iff D).mpr hD,?_,?_,?_⟩
      · rw [hdec, opMatrix_smul]
      · rw [← opMatrix_comp, hzero, opMatrix_zero]
      · simpa only [frobeniusNorm_opMatrix] using hunit
      · simpa only [matrixOpNorm_opMatrix] using hdiff

#print axioms exists_project_spectral_peeling
end UCEscape
