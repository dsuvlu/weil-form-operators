import Riemann.CCM.FourierCharacteristic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! The omitted positive free lattice, with one term per pair of signed modes. -/
noncomputable section
open scoped BigOperators
open Filter
namespace Riemann.CCM.Native

/-- One positive mode contributes once; the zero mode is not used by `latticeTail`. -/
def positiveLatticeWeight (L s : ℝ) (j : ℕ) : ℝ :=
  s / (latticeFrequency L (j : ℤ) ^ 2 + s)

/-- The first omitted mode is N+1. This is the actual convergent free-lattice sum. -/
def latticeTail (L : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, positiveLatticeWeight L s (N + k + 1)

lemma imaginary_mem_integerComplement {t : ℝ} (ht : 0 < t) :
    Complex.I * (t : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have h := congrArg Complex.im hn
  simp at h
  linarith

lemma cot_pair_imaginary {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (Complex.I * (t : ℂ) / 2) * cotTerm (Complex.I * (t : ℂ)) n =
      ((t ^ 2 / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ) := by
  rw [cotTerm_identity (imaginary_mem_integerComplement ht)]
  push_cast
  have hd : (t : ℂ)^2 + ((n : ℂ)+1)^2 ≠ 0 := by
    have hp : 0 < t^2 + (n + 1 : ℝ)^2 := by positivity
    exact_mod_cast hp.ne'
  have he : (Complex.I * (t : ℂ) + ((n : ℂ)+1)) *
      (Complex.I * (t : ℂ) - ((n : ℂ)+1)) =
      -((t : ℂ)^2 + ((n : ℂ)+1)^2) := by
    linear_combination (t : ℂ)^2 * Complex.I_sq
  rw [he]
  field_simp
  simp only [Complex.I_sq]
  ring

lemma summable_dimensionless_lattice {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => t ^ 2 / (t ^ 2 + (n + 1 : ℝ) ^ 2)) := by
  apply Complex.summable_ofReal.mp
  exact ((summable_cotTerm (imaginary_mem_integerComplement ht)).mul_left
    (Complex.I * (t : ℂ) / 2)).congr (cot_pair_imaginary ht)

/-- Partial fractions of cotangent give the exact paired positive-mode sum. -/
lemma dimensionless_lattice_eq_cot {t : ℝ} (ht : 0 < t) :
    ((∑' n : ℕ, t ^ 2 / (t ^ 2 + (n + 1 : ℝ) ^ 2) : ℝ) : ℂ) =
      ((Real.pi : ℂ) * (Complex.I * (t : ℂ)) *
        Complex.cot ((Real.pi : ℂ) * (Complex.I * (t : ℂ))) - 1) / 2 := by
  rw [Complex.ofReal_tsum]
  simp_rw [← cot_pair_imaginary ht]
  rw [tsum_mul_left]
  have hc := cot_series_rep' (imaginary_mem_integerComplement ht)
  change _ = ∑' n : ℕ, cotTerm (Complex.I * (t : ℂ)) n at hc
  rw [← hc]
  have hn : Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr ht.ne')
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

lemma positiveLatticeWeight_nonneg (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    0 ≤ positiveLatticeWeight L s j := div_nonneg hs (add_nonneg (sq_nonneg _) hs)

lemma latticeTail_nonneg (L : ℝ) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ latticeTail L N s := tsum_nonneg (fun _ => positiveLatticeWeight_nonneg L hs _)

lemma positiveLatticeWeight_dimensionless {L : ℝ} (hL : 0 < L) (a : ℝ) (j : ℕ) :
    positiveLatticeWeight L (a^2) j =
      (a / (2 * Real.pi / L))^2 /
        ((a / (2 * Real.pi / L))^2 + (j : ℝ)^2) := by
  unfold positiveLatticeWeight latticeFrequency
  push_cast
  have hc : 2 * Real.pi / L ≠ 0 := ne_of_gt (div_pos (by positivity) hL)
  field_simp
  ring

lemma summable_positiveLatticeWeight {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    Summable (fun n : ℕ => positiveLatticeWeight L (a^2) (n+1)) := by
  have ht : 0 < a / (2 * Real.pi / L) := div_pos ha (div_pos (by positivity) hL)
  simpa only [positiveLatticeWeight_dimensionless hL, Nat.cast_add, Nat.cast_one] using
    summable_dimensionless_lattice ht

lemma summable_latticeTail {L a : ℝ} (hL : 0 < L) (ha : 0 < a) (N : ℕ) :
    Summable (fun k : ℕ => positiveLatticeWeight L (a^2) (N+k+1)) := by
  have h := (summable_nat_add_iff N).mpr (summable_positiveLatticeWeight hL ha)
  simpa only [Nat.add_comm N] using h

lemma latticeTail_split {L a : ℝ} (hL : 0 < L) (ha : 0 < a) (N : ℕ) :
    (∑ j ∈ Finset.range N, positiveLatticeWeight L (a^2) (j+1)) +
      latticeTail L N (a^2) = latticeTail L 0 (a^2) := by
  simpa only [latticeTail, Nat.zero_add, Nat.add_comm N] using
    (summable_positiveLatticeWeight hL ha).sum_add_tsum_nat_add N

/-- Exact free sine logarithmic derivative, before removing the retained modes. -/
lemma latticeTail_zero_eq_cot {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    (latticeTail L 0 (a^2) : ℂ) =
      (((L : ℂ) * (Complex.I * (a : ℂ)) / 2) *
        Complex.cot ((L : ℂ) * (Complex.I * (a : ℂ)) / 2) - 1) / 2 := by
  have ht : 0 < a / (2 * Real.pi / L) := div_pos ha (div_pos (by positivity) hL)
  have h := dimensionless_lattice_eq_cot ht
  have he : (Real.pi : ℂ) * (Complex.I * ((a / (2 * Real.pi / L) : ℝ) : ℂ)) =
      (L : ℂ) * (Complex.I * (a : ℂ)) / 2 := by
    push_cast
    field_simp
  rw [he] at h
  simpa only [latticeTail, Nat.zero_add, positiveLatticeWeight_dimensionless hL,
    Nat.cast_add, Nat.cast_one] using h

/-- The cotangent formula in real hyperbolic notation, with no doubled signed sum. -/
lemma latticeTail_zero_eq_hyperbolic {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    latticeTail L 0 (a^2) =
      ((L*a/2) * (Real.cosh (L*a/2) / Real.sinh (L*a/2)) - 1) / 2 := by
  have h := latticeTail_zero_eq_cot hL ha
  have he : (L : ℂ) * (Complex.I * (a : ℂ)) / 2 = ((L*a/2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I] at h
  have hi : ((L*a/2 : ℝ) : ℂ) * Complex.I *
      (Complex.cosh ((L*a/2 : ℝ) : ℂ) / (Complex.sinh ((L*a/2 : ℝ) : ℂ) * Complex.I)) =
      ((L*a/2 : ℝ) : ℂ) *
        (Complex.cosh ((L*a/2 : ℝ) : ℂ) / Complex.sinh ((L*a/2 : ℝ) : ℂ)) := by
    field_simp
  rw [hi] at h
  exact_mod_cast h

lemma reciprocal_square_le_difference {r : ℝ} (hr : 0 < r) :
    1 / (r+1)^2 ≤ 1/r - 1/(r+1) := by
  have hp : 0 < r*(r+1) := by positivity
  have hle : r*(r+1) ≤ (r+1)^2 := by nlinarith
  calc
    _ ≤ 1/(r*(r+1)) := one_div_le_one_div_of_le hp hle
    _ = _ := by field_simp; ring

lemma positiveLatticeWeight_le_telescoping {L a : ℝ} (hL : 0 < L) (N : ℕ)
    (hN : 0 < N) (k : ℕ) :
    positiveLatticeWeight L (a^2) (N+k+1) ≤
      (a / (2*Real.pi/L))^2 * (1/(N+k : ℝ) - 1/(N+k+1 : ℝ)) := by
  rw [positiveLatticeWeight_dimensionless hL]
  push_cast
  have hr : 0 < (N : ℝ)+(k : ℝ) := by exact_mod_cast (lt_of_lt_of_le hN (Nat.le_add_right N k))
  have hsq : 0 < ((N : ℝ)+(k : ℝ)+1)^2 := by positivity
  calc
    _ ≤ (a / (2*Real.pi/L))^2 / ((N : ℝ)+(k : ℝ)+1)^2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hsq (le_add_of_nonneg_left (sq_nonneg _))
    _ ≤ _ := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left (reciprocal_square_le_difference hr) (sq_nonneg (a / (2*Real.pi/L)))

/-- A sharp-order elementary tail bound at each fixed positive anchor. -/
theorem latticeTail_le {L a : ℝ} (hL : 0 < L) (N : ℕ) (hN : 0 < N) :
    latticeTail L N (a^2) ≤ a^2 * L^2 / (4*Real.pi^2*N) := by
  have hpart : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, positiveLatticeWeight L (a^2) (N+k+1)) ≤
        (a / (2*Real.pi/L))^2 / N := by
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, (a / (2*Real.pi/L))^2 *
          (1/(N+k : ℝ) - 1/(N+k+1 : ℝ)) :=
        Finset.sum_le_sum (fun k hk => positiveLatticeWeight_le_telescoping hL N hN k)
      _ = (a / (2*Real.pi/L))^2 * (1/(N : ℝ) - 1/(N+n : ℝ)) := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, add_assoc] using
          Finset.sum_range_sub' (fun k : ℕ => 1/(N+k : ℝ)) n
      _ ≤ _ := by
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left (sub_le_self (1/(N : ℝ))
          (show 0 ≤ 1/(N+n : ℝ) by positivity)) (sq_nonneg (a / (2*Real.pi/L)))
  have ht := Real.tsum_le_of_sum_range_le
    (fun k => positiveLatticeWeight_nonneg L (sq_nonneg a) (N+k+1)) hpart
  change latticeTail L N (a^2) ≤ _ at ht
  convert! ht using 1
  field_simp
  ring

/-- The anchor a=1/4 has the exact constant L²/(64π²N). -/
theorem latticeTail_quarter_le {L : ℝ} (hL : 0 < L) (N : ℕ) (hN : 0 < N) :
    latticeTail L N (1/16) ≤ L^2 / (64*Real.pi^2*N) := by
  have h := latticeTail_le (a := (1/4 : ℝ)) hL N hN
  norm_num at h
  convert! h using 1; ring

end Riemann.CCM.Native
