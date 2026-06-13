/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import Mathlib

/-! # Non-negativity of discrete relative entropy (Gibbs' inequality). -/

/-- Gibbs' inequality: the discrete relative entropy (Kullback–Leibler divergence) of a finite
probability distribution `p` with respect to a strictly positive finite distribution `q` is
non-negative. -/
theorem relEntropy_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  -- Termwise bound: `p i - q i ≤ p i * log (p i / q i)` for every `i`.
  have hterm : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h | h
    · -- `p i = 0`: the right-hand term vanishes and `p i - q i = -q i ≤ 0`.
      have hzero : p i = 0 := h.symm
      rw [hzero, zero_mul, zero_sub]
      linarith [hq i]
    · -- `0 < p i`: apply `log x ≤ x - 1` at `x = q i / p i`.
      have hpi : 0 < p i := h
      have hpne : p i ≠ 0 := hpi.ne'
      have hqp : 0 < q i / p i := div_pos (hq i) hpi
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 := Real.log_le_sub_one_of_pos hqp
      have hlogeq : Real.log (p i / q i) = -Real.log (q i / p i) := by
        rw [← Real.log_inv, inv_div]
      have hcancel : p i * (q i / p i) = q i := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpne]
      rw [hlogeq, mul_neg]
      have h2 : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog hpi.le
      rw [mul_sub, mul_one, hcancel] at h2
      linarith
  -- Sum the termwise bound: `∑ (p i - q i) = 1 - 1 = 0 ≤ ∑ p i * log (p i / q i)`.
  calc 0 = ∑ i, p i - ∑ i, q i := by rw [hp1, hq1]; norm_num
    _ = ∑ i, (p i - q i) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, p i * Real.log (p i / q i) := Finset.sum_le_sum fun i _ => hterm i

#print axioms relEntropy_nonneg
