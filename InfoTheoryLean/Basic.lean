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

/-- The equality case of Gibbs' inequality: the discrete relative entropy of `p` with respect to a
strictly positive distribution `q` vanishes if and only if `p = q`. -/
theorem relEntropy_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, p i * Real.log (p i / q i) = 0 ↔ p = q := by
  constructor
  · -- Substantive direction: a vanishing sum forces `p = q`.
    intro hsum
    -- The same termwise bound `p i - q i ≤ p i * log (p i / q i)` used in `relEntropy_nonneg`.
    have hterm : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
      intro i
      rcases eq_or_lt_of_le (hp i) with h | h
      · have hzero : p i = 0 := h.symm
        rw [hzero, zero_mul, zero_sub]
        linarith [hq i]
      · have hpi : 0 < p i := h
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
    -- Each excess term `g i := p i * log (p i / q i) - (p i - q i)` is `≥ 0` and they sum to `0`.
    have hgnonneg : ∀ i ∈ Finset.univ,
        0 ≤ p i * Real.log (p i / q i) - (p i - q i) := fun i _ => by linarith [hterm i]
    have hgsum : ∑ i, (p i * Real.log (p i / q i) - (p i - q i)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_sub_distrib, hp1, hq1]; ring
    have hgzero := (Finset.sum_eq_zero_iff_of_nonneg hgnonneg).mp hgsum
    -- Hence each term meets the bound with equality.
    have heq : ∀ i, p i * Real.log (p i / q i) = p i - q i := fun i => by
      have := hgzero i (Finset.mem_univ i); linarith
    -- Termwise equality forces `p i = q i`.
    funext i
    rcases eq_or_lt_of_le (hp i) with h | hpi
    · -- `p i = 0` would give `0 = -q i`, impossible since `q i > 0`.
      exfalso
      have hzero : p i = 0 := h.symm
      have hh := heq i
      rw [hzero, zero_mul, zero_sub] at hh
      linarith [hq i]
    · -- `0 < p i`: equality in `log x ≤ x - 1` forces `x = q i / p i = 1`.
      have hpne : p i ≠ 0 := hpi.ne'
      have hqp : 0 < q i / p i := div_pos (hq i) hpi
      have hlogeq : Real.log (p i / q i) = -Real.log (q i / p i) := by
        rw [← Real.log_inv, inv_div]
      have hcancel : p i * (q i / p i) = q i := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpne]
      have hh := heq i
      rw [hlogeq, mul_neg] at hh
      have hh2 : p i * Real.log (q i / p i) = p i * (q i / p i - 1) := by
        rw [mul_sub, mul_one, hcancel]; linarith
      have hlog1 : Real.log (q i / p i) = q i / p i - 1 := mul_left_cancel₀ hpne hh2
      -- Equality in `log x ≤ x - 1` (which is strict for `x ≠ 1`) forces `q i / p i = 1`.
      have hx1 : q i / p i = 1 := by
        by_contra hxne
        have hstrict := Real.log_lt_sub_one_of_pos hqp hxne
        linarith
      have hcancel2 : q i / p i * p i = q i := div_mul_cancel₀ (q i) hpne
      rw [hx1, one_mul] at hcancel2
      exact hcancel2
  · -- Easy direction: if `p = q`, every term is `q i * log 1 = 0`.
    intro hpq
    rw [hpq]
    apply Finset.sum_eq_zero
    intro i _
    rw [div_self (hq i).ne', Real.log_one, mul_zero]

#print axioms relEntropy_eq_zero_iff
