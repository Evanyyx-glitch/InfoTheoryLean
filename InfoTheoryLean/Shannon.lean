/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.Basic

/-!
# Shannon entropy

The Shannon entropy `H(p) = -∑ p i * log (p i)` of a finite probability distribution `p`, measured
in nats. We prove the two basic bounds:

* `entropy_nonneg` — entropy is non-negative.
* `entropy_le_log_card` — entropy is at most `log (card ι)`, with the uniform distribution attaining
  the bound. This is a direct consequence of Gibbs' inequality (`relEntropy_nonneg` from
  `InfoTheoryLean.Basic`) applied against the uniform distribution.
-/

/-- Shannon entropy of a finite distribution `p`, in nats. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
    - ∑ i, p i * Real.log (p i)

/-- The Shannon entropy of a probability distribution is non-negative. -/
theorem entropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    0 ≤ entropy p := by
  -- Each summand `p i * log (p i)` is `≤ 0`, since `0 ≤ p i ≤ 1` forces `log (p i) ≤ 0`.
  have hsum : ∑ i, p i * Real.log (p i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have hle1 : p i ≤ 1 := by
      rw [← hp1]
      exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    have hlog : Real.log (p i) ≤ 0 := Real.log_nonpos (hp i) hle1
    exact mul_nonpos_of_nonneg_of_nonpos (hp i) hlog
  unfold entropy
  linarith

/-- **Maximum entropy**: the Shannon entropy of a probability distribution on `ι` is at most
`log (card ι)`, the entropy of the uniform distribution. -/
theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card ι) := by
  set c : ℝ := (Fintype.card ι : ℝ) with hc
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hc_pos : 0 < c := by rw [hc]; exact_mod_cast hcard_pos
  have hc_ne : c ≠ 0 := hc_pos.ne'
  -- The uniform distribution `q i = c⁻¹` is a genuine probability distribution.
  have hq1 : ∑ _i : ι, c⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hc, mul_inv_cancel₀ hc_ne]
  -- Gibbs' inequality against the uniform distribution.
  have key : 0 ≤ ∑ i, p i * Real.log (p i / c⁻¹) :=
    relEntropy_nonneg p (fun _ => c⁻¹) hp (fun _ => inv_pos.mpr hc_pos) hp1 hq1
  -- Termwise: `p i * log (p i / c⁻¹) = p i * log (p i) + p i * log c`
  -- (for `p i = 0` both sides vanish; for `p i > 0` use `log_mul`).
  have hterm : ∀ i, p i * Real.log (p i / c⁻¹)
      = p i * Real.log (p i) + p i * Real.log c := by
    intro i
    rw [div_inv_eq_mul]
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_mul h.ne' hc_ne]; ring
  -- Sum the termwise identity; the `log c` part collapses via `∑ p i = 1`.
  have hrw : ∑ i, p i * Real.log (p i / c⁻¹)
      = (∑ i, p i * Real.log (p i)) + Real.log c := by
    calc ∑ i, p i * Real.log (p i / c⁻¹)
        = ∑ i, (p i * Real.log (p i) + p i * Real.log c) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, p i * Real.log (p i)) + ∑ i, p i * Real.log c := Finset.sum_add_distrib
      _ = (∑ i, p i * Real.log (p i)) + (∑ i, p i) * Real.log c := by rw [← Finset.sum_mul]
      _ = (∑ i, p i * Real.log (p i)) + Real.log c := by rw [hp1, one_mul]
  rw [hrw] at key
  unfold entropy
  linarith

#print axioms entropy_nonneg
#print axioms entropy_le_log_card
