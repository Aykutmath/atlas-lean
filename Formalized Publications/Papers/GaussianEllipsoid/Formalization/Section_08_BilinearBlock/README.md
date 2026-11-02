# Section 8 (BilinearBlock)

Paper-order entrypoint: the Lean modules behind this section's inventory rows. Namespaces and theorem names are unchanged; only the package prefix is new.

## Lemma 8.1 — Lemma 8.1 (Arbitrary-center determinant small ball).

- `GaussianEllipsoid.SmallBall.paper_half_determinant_small_ball` in [GaussianEllipsoidNative/PaperHalfSmallBall.lean](../GaussianEllipsoidNative/PaperHalfSmallBall.lean)
- `GaussianTensorMoments.paper_original_half_determinant_small_ball` in [GaussianEllipsoidNative/PaperOriginalHalfSmallBall.lean](../GaussianEllipsoidNative/PaperOriginalHalfSmallBall.lean)

## Lemma 8.2 — Lemma 8.2 (Operator norm bound for the bilinear measurement matrix).

- `GaussianTensorMoments.gaussianBilinearOperator_aspect_norm_tail` in [GaussianEllipsoidNative/PaperBilinearAspect.lean](../GaussianEllipsoidNative/PaperBilinearAspect.lean)
- `GaussianTensorMoments.gaussianBilinearOperator_arbitrary_aspect_tendsto_zero` in [GaussianEllipsoidNative/PaperBilinearAspect.lean](../GaussianEllipsoidNative/PaperBilinearAspect.lean)
- `GaussianTensorMoments.paperBilinearOperator_entries` in [GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean](../GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean)
- `GaussianTensorMoments.paperBilinearOperator_bad_probability_eq` in [GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean](../GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean)
- `GaussianTensorMoments.paper_bilinear_operator_arbitrary_aspect` in [GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean](../GaussianEllipsoidNative/PaperBilinearOriginalBlocks.lean)

## display line 2671 — Normalized complex factors and fixed-sign independent product states

- `AHHGaussian.normalizedFactor_expected_norm_sq` in [GaussianEllipsoidNative/AHHGaussianLaw.lean](../GaussianEllipsoidNative/AHHGaussianLaw.lean)
- `AHHGaussian.fourGaussianLaw_first_factor_expected_norm_sq` in [GaussianEllipsoidNative/AHHGaussianModelBridge.lean](../GaussianEllipsoidNative/AHHGaussianModelBridge.lean)
- `AHHGaussian.fourGaussianLaw_second_factor_expected_norm_sq` in [GaussianEllipsoidNative/AHHGaussianModelBridge.lean](../GaussianEllipsoidNative/AHHGaussianModelBridge.lean)
- `AHHGaussian.actualProductStates_joint_law` in [GaussianEllipsoidNative/AHHGaussianRowLaw.lean](../GaussianEllipsoidNative/AHHGaussianRowLaw.lean)
- `AHHGaussian.actualProductStates_independent` in [GaussianEllipsoidNative/AHHGaussianRowLaw.lean](../GaussianEllipsoidNative/AHHGaussianRowLaw.lean)
- `AHHGaussian.actualProductStates_eq_productState` in [GaussianEllipsoidNative/AHHGaussianModelBridge.lean](../GaussianEllipsoidNative/AHHGaussianModelBridge.lean)

## display line 2696 — Exact tensor expansion

- `AHHAlgebraBridges.tensor_expansion` in [GaussianEllipsoidNative/AHHAlgebraBridges.lean](../GaussianEllipsoidNative/AHHAlgebraBridges.lean)

## display line 2704 — Four-sign Hermitian cancellation

- `AHHAlgebraBridges.four_sign_projector_sum` in [GaussianEllipsoidNative/AHHAlgebraBridges.lean](../GaussianEllipsoidNative/AHHAlgebraBridges.lean)

## display line 2709 — PSD domination

- `AHHAlgebraBridges.real_projector_le_four_sign_sum` in [GaussianEllipsoidNative/AHHAlgebraBridges.lean](../GaussianEllipsoidNative/AHHAlgebraBridges.lean)

## display line 2731 — Sharp upper expectation edge

- `AHHGaussian.paperGaussian_expectation_upper_edge` in [GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean](../GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean)
- `AHHGaussian.normalizedGaussian_all_signs_expectation_upper_edge` in [GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean](../GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean)
- `AHHRadial.normalizedHaar_expectation_upper_edge` in [GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean](../GaussianEllipsoidNative/AHHNormalizedExpectationEndpoint.lean)
- `AHHGaussian.bounded_ratio_expected_norm_via_augmentation` in [GaussianEllipsoidNative/AHHAugmentationBridge.lean](../GaussianEllipsoidNative/AHHAugmentationBridge.lean)

## display line 2737 — Exact AHH equation (11)

- `AHHRadial.spherePowerEntropyBound_general` in [GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean](../GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean)
- `AHHRadial.spherePowerEntropyBound_family` in [GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean](../GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean)
- `AHHRadial.sphere_moments_unconditional` in [GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean](../GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean)
- `AHHRadial.actual_equation11` in [GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean](../GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean)
- `AHHRadial.paper_equation11` in [GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean](../GaussianEllipsoidNative/AHHExactEquation11Unconditional.lean)

## display line 2750 — Constant-threshold complex covariance tail

- `AHHGaussian.paper_fixed_sign_complex_covariance_tail` in [GaussianEllipsoidNative/AHHGaussianTail.lean](../GaussianEllipsoidNative/AHHGaussianTail.lean)
- `AHHGaussian.all_sign_complexCovariance_norm_tail` in [GaussianEllipsoidNative/AHHGaussianTail.lean](../GaussianEllipsoidNative/AHHGaussianTail.lean)
- `AHHGaussian.paper_half_dimension_fixed_sign_tail` in [GaussianEllipsoidNative/AHHGaussianTail.lean](../GaussianEllipsoidNative/AHHGaussianTail.lean)

## display line 2759 — Pathwise Euclidean-to-Frobenius operator comparison

- `AHHAlgebraBridges.pathwise_real_bilinear_to_complex` in [GaussianEllipsoidNative/AHHPathwiseBilinear.lean](../GaussianEllipsoidNative/AHHPathwiseBilinear.lean)
- `AHHAlgebraBridges.pathwise_four_sign_bound` in [GaussianEllipsoidNative/AHHPathwiseBilinear.lean](../GaussianEllipsoidNative/AHHPathwiseBilinear.lean)
- `AHHAlgebraBridges.pathwise_four_sign_renamed_constant` in [GaussianEllipsoidNative/AHHPathwiseBilinear.lean](../GaussianEllipsoidNative/AHHPathwiseBilinear.lean)
- `AHHAlgebraBridges.paperBilinearOperator_four_complex_bound` in [GaussianEllipsoidNative/AHHOriginalBlocksBridge.lean](../GaussianEllipsoidNative/AHHOriginalBlocksBridge.lean)
- `AHHAlgebraBridges.paperBilinearOperator_four_sign_bound_all_d` in [GaussianEllipsoidNative/AHHOriginalBlocksBridge.lean](../GaussianEllipsoidNative/AHHOriginalBlocksBridge.lean)
