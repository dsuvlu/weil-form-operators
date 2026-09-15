# Mathematical statements and their checked declarations

The article uses the exact Lean source tree distributed in this directory:
131 implementation modules and `Riemann.lean`. The manifest SHA-256 is
`1888958bbc5492250c8a7fc9dd0161f09ba44c717ae29ea8095262b0fa825a68`.
`SNAPSHOT.json` identifies its pinned configuration. `README.md` gives the
standalone build and audit commands; `audit/distribution/` records the export build and axiom checks.

The archived independent build and complete transitive-axiom audit accompany
this distribution in `audit/archived/`. The archive is preserved verbatim;
historical paths in its logs identify the original build environment and are
not required by the standalone build. The allowed axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Mathematical convention

The physical finite-window carrier is a closed support subspace of mathlib
`Lp ℂ 2 volume` on R. Fourier coefficients use the genuine normalized functions
`L^(-1/2)exp(2πint/L)`, with all signed indices from −N to N. Inner products
conjugate the first slot. Translation acts backward and is killed at the terminal
endpoint. The absorbing generator is +d/dt on its actual absolutely continuous
terminal-zero domain; the finite periodic derivative is −i d/dt. The current is
a domain-defined linear map, and its negative Hermitian pairing is a form. An
ambient bounded current or a globally defined unbounded adjoint is not inserted.

## Exact correspondence table

The paths below are relative to `Riemann/`. Short names have the
namespace of their module unless explicitly qualified.

| Article object/result | Exact frozen implementation/declarations | Match and hypothesis boundary |
|---|---|---|
| Killed finite shifts and arithmetic algebra | `Analysis/FiniteWindow/KilledShiftHilbert.lean`; `PrimeHilbert.lean`: `primeOperator`, `primeInverse`, `primeOperator_euler_product`, `prime_negative_logarithmic_derivative`, `hasDerivAt_primeOperator` | Actual Hilbert shifts, nilpotent arithmetic and real-parameter operator derivative. Generic finite arithmetic supports complex coefficients, but the concrete Hilbert parameter family is real. |
| Absorbing generator and all-complex finite Volterra inverse | `Analysis/FiniteWindow/GeneratorOperator.lean`, `GeneratorDomain.lean`, `LiteralVolterra.lean` | Actual closed densely defined generator, absolutely continuous representatives/terminal condition and inverse relations for finite-window complex b. This is not a negative-real half-line resolvent theorem. |
| Gamma factor and critical norm derivative | `Analysis/GammaKernel.lean`; `FiniteWindow/GammaOperator.lean`: `gammaOperator_half`, `hasDerivAt_gammaOperator_half`, `gammaOperator_hasDerivAt` | Exact factor `2πR_(1/2)`, real σ∈(0,1) differentiability in bounded-operator norm, from actual scalar L¹ kernels. The article's larger complex parameter domain, when stated, is justified in its written analysis, not by this exact formal theorem. |
| Combined Gamma current and C8 normalization | `FiniteWindow/GammaCurrentIdentity.lean`; `GammaBackground.lean`; `GammaBackgroundForm.lean`: `gammaCurrent_native_formula` | Genuine integrability domain; all Fourier inputs enter it by the square-root shift estimate. C4↔C8 vector formula is proved without splitting divergent terms. General bounded piecewise-C¹ domain membership is not a separate package theorem; native Fourier and generator-domain membership are. |
| Completed family and its left/right current identities | `FiniteWindow/CompletedFrame.lean`: `hasDerivAt_completedFrame_half`, `completedFrame_hasDerivAt`; `CompletedCurrentIdentity.lean`: `completedDerivative_eq_neg_frame_current`, `completedCurrent_frame_eq_neg_derivative` | Real parameter derivative. `X′f=−XJf` on the declared current domain; `JXu=−X′u` for every Hilbert source, with Xu domain membership proved. No ambient inverse is used. |
| Completed range and actual source inverse | `FiniteWindow/CompletedFrame.lean`: `range_completedFrame`, `mem_completedFrame_range_iff_ac`, `completedSource`, `completedSource_unique`, `completedFrame_nativeCompletedSource` | Actual injectivity and terminal-zero derivative-domain range for L>0. Native endpoint-zero columns have literal sources. The paper's projected-range surjectivity and displayed quantitative constrained Rayleigh gap are not labeled exact compiled statements here. |
| Complete finite arithmetic matrix | `FiniteWindow/NativePrimeCoefficients.lean`, `NativeGammaCoefficients.lean`, `NativePolarCoefficients.lean`; `NativeCompletedCoefficients.lean`: `nativeCompletedCoefficients`, `nativeCompleted_weilOperator`, `nativeCompletedCurrent_form` | The full matrix and its diagonal are constructed from the literal three components before equality is proved. All x,y in the full complex Section N are allowed, L>0 and N≥0; no ground admission or matching premise. |
| Explicit component diagonal and odd beta | `nativePrimeCoefficients_diagonal`, `nativePrimeCoefficients_beta`, `nativeGammaCoefficients_diagonal`, `nativeGammaCoefficients_beta`, `nativeRealVolterraCoefficients_diagonal`, `nativeRealVolterraCoefficients_beta` | Actual real cosine diagonal and sine beta integrals with strict arithmetic survival. Gamma diagonal is stated in the C4 compensated normalization; the equivalent C8 vector identity is separately compiled. |
| Full simple-even ground and corrected derivative | `CCM/NativeData.lean`: `fullData`, `native_ground_bright`, `native_groundWeight_pos`, `native_metric_intertwining`, `native_corrected_eigenvalue_real`; `GroundComplement.lean` | GroundAdmission requires full leastness, a one-dimensional ground and an even ground vector. The positive quotient is realized by the projected operator on the actual physical ground complement with its positive shifted-matrix inner product; no invariance of that physical complement under the corrected derivative is assumed. |
| Actual finite Fourier characteristic | `CCM/FourierIntegral.lean`: `integral_fourierFunction_centered`; `FourierCharacteristic.lean`: `native_boundaryCharacteristic_eq_integral`, `native_boundaryCharacteristic_entire`, `native_boundaryCharacteristic_nonreal`, `boundaryCharacteristic_at_mode`, `boundaryCharacteristic_outside` | Actual centered finite Fourier integral, entire extension and absence of nonreal zeros under full ground admission. Retained and exterior free-lattice values, including zero, are explicit. The closed entire function is not a singular matrix inverse evaluated at a pole. |
| Determinant correction algebra | `CCM/NativeDeterminant.lean`, `FourierResolvent.lean`, `FourierCharacteristic.lean` | Native finite determinant and resolvent identities feed the characteristic theorem. The zeta-regularized infinite free-tail determinant and chosen spectral cut in Appendix A remain a source theorem of CCM, not a compiled zeta-regularization theorem. |
| Critical completed half-line operator | `Analysis/HalfLine/CompletedOperator.lean`, `CompletedKernel.lean`, `FiniteRestriction.lean`: `norm_completedOperator_le`, `completedOperator_extends_core`, `completedOperator_unique`, `completedOperator_finiteInclusion` | Actual signed kernel, upper bound8π/3, unique bounded extension of the ordered completed core and equality with the frozen critical finite-window family. No half-line parameter/current family. |
| Strong physical truncations | `HalfLine/FiniteRestriction.lean`: `completedOperator_supportTruncation_tendsto` | Proved along integer lengths n→∞. The article's ordinary physical support formulation has its direct argument in the text; no operator-norm convergence is claimed. |
| Raw nonclosability | `HalfLine/RawNonclosability.lean`: `rawEuler_nonclosability_witness`, `rawEuler_graphClosure_not_singleValued` | Actual whole-L² graph witness of width1, translated by integer n; includes the strip/tail. This suffices for nonclosability. The article's arbitrary fixed width d>0 is a written generalization of the witness, not this exact declaration. |
| Completion not bounded below | `HalfLine/CompletedObstruction.lean`: `completedOperator_unitExponential`, `completed_laplace_tendsto`, `completedOperator_not_boundedBelow`, `polarFactor_kills_rawGraphDefect` | Unit exponentials and Laplace dominated convergence for the actual completed kernel. Polar annihilation refers to the raw graph defect; it is not a completed-operator kernel claim. |


## Article notation and exact scope

The selected ground, brightness, shifted matrix and corrected derivative are
ξ_N,q_N,T_N,D_N′ in the article. The frozen names `groundVector`, `groundWeight`,
`shifted` and `corrected` denote those respective objects. The endpoint
functional is ev_0, its physical Riesz vector δ_N; the endpoint Riesz vector has coordinates L^(-1/2) in the
normalized Fourier basis, whereas the Dirichlet-kernel vector has coordinates 1.
Thus ev_0(f)=⟨δ_N,f⟩; D_N remains the physical derivative operator. `boundaryCharacteristic`
represents Θ_N; the actual centered Fourier integral is hatξ_N=LΘ_N.

The named declarations above concern their precise hypotheses and domains.
They do not establish the article's signed current centering, repaired arithmetic
interpolation, holomorphic half-line/full-line family, leakage and trace-class
source derivative, expanded inverse-source formula/cost estimate, or entire
zero-retaining cluster criterion. Those statements have written proofs in the
article. The regularized free-tail determinant is imported from CCM with its
specified spectral cut, rather than asserted as a checked zeta-regularization
theorem. No moving selection premise or RH conclusion is kernel-verified here.

## Exact elaborated types

`DECLARATION_TYPES.json` contains the exact archived elaborated types of the
names explicitly cited in the correspondence table. The complete archived
public inventory is `audit/archived/public-types.json`; the full compiled environment
is `audit/archived/environment-types.jsonl`. The manifest-bound receipt reports all
four transitive-axiom audits. A similarly named theorem is not substituted for
a statement with different hypotheses.
