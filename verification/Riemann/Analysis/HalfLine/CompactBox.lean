import Riemann.Analysis.HalfLine.Exponential
import Riemann.Analysis.HalfLine.FiniteSupport
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Compact boxes for the raw Euler graph

The closed interval representative makes both arithmetic endpoints inclusive.
Its ambient support is contained in the strictly larger window `[0,T+2)`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace NNReal ENNReal Topology
namespace Riemann.Analysis.HalfLine

lemma norm_sq_eq_integral (f : Hilbert) :
    ‖f‖ ^ 2 = ∫ t, ‖(f : Ambient) t‖ ^ 2 :=
  ambient_norm_sq (f : Ambient)

def boxFunction (T : ℝ) : ℝ → ℂ :=
  (Icc T (T+1)).indicator (fun _ => (Real.exp (-T/2) : ℂ))

lemma boxFunction_memLp (T : ℝ) : MemLp (boxFunction T) 2 volume :=
  memLp_indicator_const 2 measurableSet_Icc _ (Or.inr measure_Icc_lt_top.ne)

def boxVector (T : ℝ) (hT : 0 ≤ T) : Hilbert := by
  let f : Ambient := (boxFunction_memLp T).toLp (boxFunction T)
  refine ⟨f, (mem_supported_iff f).2 ?_⟩
  apply Lp.ext
  filter_upwards [cut_ae f, MemLp.coeFn_toLp (boxFunction_memLp T)] with t hc hf
  rw [hc]
  by_cases ht : t ∈ Ici (0 : ℝ)
  · simp [ht]
  · rw [indicator_of_notMem ht, hf]
    simp only [boxFunction, indicator_of_notMem (show t ∉ Icc T (T+1) from
      fun h => ht (hT.trans h.1))]

theorem boxVector_ae (T : ℝ) (hT : 0 ≤ T) :
    ((boxVector T hT : Ambient) : ℝ → ℂ) =ᵐ[volume] boxFunction T :=
  MemLp.coeFn_toLp (boxFunction_memLp T)

theorem boxVector_supported (T : ℝ) (hT : 0 ≤ T) :
    (boxVector T hT : Ambient) ∈ FiniteWindow.supported (T+2) := by
  apply (FiniteWindow.mem_supported_iff _ _).2
  apply Lp.ext
  filter_upwards [FiniteWindow.cut_ae (T+2) (boxVector T hT), boxVector_ae T hT]
    with t hc hf
  rw [hc]
  by_cases ht : t ∈ Ico 0 (T+2)
  · simp [ht]
  · rw [indicator_of_notMem ht, hf]
    simp only [boxFunction, indicator_of_notMem (show t ∉ Icc T (T+1) from
      fun h => ht ⟨hT.trans h.1, by linarith [h.2]⟩)]

theorem boxVector_mem_compactSupport (T : ℝ) (hT : 0 ≤ T) :
    boxVector T hT ∈ compactSupport :=
  ⟨T+2, by linarith, boxVector_supported T hT⟩

/-- The raw domain element, with an actual finite support proof. -/
def box (T : ℝ) (hT : 0 ≤ T) : compactSupport :=
  ⟨boxVector T hT, boxVector_mem_compactSupport T hT⟩

theorem norm_boxVector_sq (T : ℝ) (hT : 0 ≤ T) :
    ‖boxVector T hT‖ ^ 2 = Real.exp (-T) := by
  rw [norm_sq_eq_integral]
  calc
    _ = ∫ t, (Icc T (T+1)).indicator (fun _ => Real.exp (-T)) t := by
      apply integral_congr_ae
      filter_upwards [boxVector_ae T hT] with t hf
      rw [hf]
      by_cases ht : t ∈ Icc T (T+1)
      · simp only [boxFunction, indicator_of_mem ht, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
        congr 1
        ring
      · simp [boxFunction, ht]
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, integral_const]
      simp

lemma norm_boxVector (T : ℝ) (hT : 0 ≤ T) :
    ‖boxVector T hT‖ = Real.exp (-T/2) := by
  have h := norm_boxVector_sq T hT
  have he : Real.exp (-T/2)^2 = Real.exp (-T) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  nlinarith [norm_nonneg (boxVector T hT), Real.exp_pos (-T/2)]

end Riemann.Analysis.HalfLine
