import Riemann.Analysis.FiniteWindow.GammaBackgroundForm
import Riemann.Analysis.FiniteWindow.NativeSourceWeil
import Riemann.Analysis.GammaCutoffLimit
import Riemann.Analysis.FiniteWindow.NativePrimeCoefficients
import Riemann.Analysis.FiniteWindow.ShiftCommutation
import Riemann.Analysis.FiniteWindow.PolarKernel
import Riemann.Analysis.FiniteWindow.CompletedSourceGram
import Riemann.Analysis.FiniteWindow.CompletedCurrent
import Riemann.Arithmetic.NativeFiniteArithmetic
import Riemann.Basic.PositiveGalerkin
import Riemann.CCM.BoundaryWeyl
import Riemann.Basic.ErrorEnergy
import Riemann.Source.MinimumNorm
import Riemann.CCM.Spectrum
import Riemann.CCM.ConstantModeExample
import Riemann.CCM.GroundComplement
import Riemann.CCM.FourierCharacteristic

import Riemann.Basic.MatrixPencilCalculus
import Riemann.Basic.PhysicalMass
import Riemann.Basic.PositiveCompression
import Riemann.Basic.PositivePencilDiagonalization
import Riemann.Basic.PositiveSchur
import Riemann.Basic.PositiveSchurTransitivity
import Riemann.CCM.BoundarySchur
import Riemann.CCM.InverseEnergy
import Riemann.CCM.InverseEnergyCapacity
import Riemann.CCM.InverseEnergyIntegration
import Riemann.CCM.InverseEnergyTrace
import Riemann.CCM.NativeCapacity
import Riemann.CCM.PositiveOddCapacity
import Riemann.Capacity.BoundaryCorrection
import Riemann.Capacity.FullDecomposition
import Riemann.Capacity.HighGraph
import Riemann.Capacity.ScalarLogBounds
import Riemann.Capacity.SoftMean
import Riemann.Capacity.SoftMeanGeometry
import Riemann.Basic.PositiveSchurCoordinates
import Riemann.CCM.NativeGraph
import Riemann.Capacity.RankOneCoupling

import Riemann.CCM.NativeInverseEnergy

import Riemann.Basic.RealMatrixComplexification
import Riemann.CCM.CharacteristicSlope
import Riemann.CCM.FiniteCapacityDictionary
import Riemann.CCM.InverseEnergyCharacteristic
import Riemann.CCM.LatticeTail
import Riemann.CCM.NativeHighCoordinateDictionary
import Riemann.CCM.NativeHighCoordinateEquiv
import Riemann.CCM.NativeHighLowChart
import Riemann.CCM.NativeLatticeMean
import Riemann.CCM.NativeSourceEnergyEquiv
import Riemann.CCM.OddGroundResponse

import Riemann.Analysis.FiniteWindow.KilledShiftAlgebra
import Riemann.Analysis.FiniteWindow.LiteralVolterra
import Riemann.Analysis.FiniteWindow.NativeFourierIsometry
import Riemann.Analysis.FiniteWindow.GammaOperator
import Riemann.Analysis.FiniteWindow.KernelConvolution
import Riemann.Analysis.FiniteWindow.SourceGramDerivative
import Riemann.Analysis.HalfLine.ArithmeticKernel
import Riemann.Analysis.HalfLine.CompactBox
import Riemann.Analysis.HalfLine.CompletedCore
import Riemann.Analysis.HalfLine.CompletedKernel
import Riemann.Analysis.HalfLine.CompletedObstruction
import Riemann.Analysis.HalfLine.CompletedOperator
import Riemann.Analysis.HalfLine.Exponential
import Riemann.Analysis.HalfLine.FiniteRestriction
import Riemann.Analysis.HalfLine.FiniteSupport
import Riemann.Analysis.HalfLine.Hilbert
import Riemann.Analysis.HalfLine.InverseSqrtSum
import Riemann.Analysis.HalfLine.Kernel
import Riemann.Analysis.HalfLine.KernelTranslation
import Riemann.Analysis.HalfLine.LaplaceObstruction
import Riemann.Analysis.HalfLine.RawBoxArithmetic
import Riemann.Analysis.HalfLine.RawBoxConvergence
import Riemann.Analysis.HalfLine.RawBoxScalar
import Riemann.Analysis.HalfLine.RawEuler
import Riemann.Analysis.HalfLine.RawNonclosability
import Riemann.Analysis.HalfLine.Volterra
/-!
# Stable finite foundations

The default target imports the complete project. Exact theorem provenance and
scope are recorded in PROVENANCE.md; native divided-difference entry geometry is connected to the finite entire
characteristic under full simple-even ground admission. Analytic evaluation
of the Weil coefficients and all moving limits remain outside this kernel.
-/
