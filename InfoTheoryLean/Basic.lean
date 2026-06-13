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

/-!
## Quadratic lower bound on `klFun` (analytic core of Pinsker's inequality)

We prove `3 * (x - 1) ^ 2 / (2 * x + 4) ≤ x * log x + 1 - x` for `x ≥ 0`.
After clearing the (positive) denominator this is `0 ≤ F x` for
`F x = (2 * x + 4) * (x * log x + 1 - x) - 3 * (x - 1) ^ 2`.
We show `F` is convex on `[0, ∞)` (its second derivative `4 * (log x - (1 - x⁻¹)) ≥ 0`) and has a
horizontal tangent at `x = 1` with `F 1 = 0`, so `F` attains its minimum value `0` there.
-/

/-- Cleared-denominator function `F x = (2x+4)·(x log x + 1 - x) - 3(x-1)²`. -/
private noncomputable def pinskerF (x : ℝ) : ℝ :=
  (2 * x + 4) * (x * Real.log x + 1 - x) - 3 * (x - 1) ^ 2

/-- First derivative of `pinskerF` (valid for `x ≠ 0`). -/
private noncomputable def pinskerDF (x : ℝ) : ℝ :=
  (4 * x + 4) * Real.log x - 8 * x + 8

/-- Second derivative of `pinskerF` (valid for `x ≠ 0`). -/
private noncomputable def pinskerD2F (x : ℝ) : ℝ :=
  4 * Real.log x + 4 * x⁻¹ - 4

private lemma hasDerivAt_pinskerF {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt pinskerF (pinskerDF x) x := by
  unfold pinskerF pinskerDF
  have hv : HasDerivAt (fun y : ℝ => y * Real.log y + 1 - y) (Real.log x + 1 - 1) x :=
    ((Real.hasDerivAt_mul_log hx).add_const 1).sub (hasDerivAt_id' x)
  have hu : HasDerivAt (fun y : ℝ => 2 * y + 4) _ x :=
    ((hasDerivAt_id' x).const_mul (2 : ℝ)).add_const 4
  have hw : HasDerivAt (fun y : ℝ => 3 * (y - 1) ^ 2) _ x :=
    (((hasDerivAt_id' x).sub_const 1).pow 2).const_mul (3 : ℝ)
  convert (hu.mul hv).sub hw using 1
  push_cast
  ring

private lemma hasDerivAt_pinskerDF {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt pinskerDF (pinskerD2F x) x := by
  unfold pinskerDF pinskerD2F
  have ha : HasDerivAt (fun y : ℝ => 4 * y + 4) _ x :=
    ((hasDerivAt_id' x).const_mul (4 : ℝ)).add_const 4
  have h : HasDerivAt (fun y : ℝ => (4 * y + 4) * Real.log y - 8 * y + 8) _ x :=
    ((ha.mul (Real.hasDerivAt_log hx)).sub ((hasDerivAt_id' x).const_mul (8 : ℝ))).add_const 8
  convert h using 1
  field_simp
  ring

private lemma continuous_pinskerF : Continuous pinskerF := by
  unfold pinskerF
  fun_prop

private lemma pinskerD2F_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ pinskerD2F x := by
  have h := Real.one_sub_inv_le_log_of_pos hx
  unfold pinskerD2F
  linarith

private lemma pinskerF_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pinskerF x := by
  -- `pinskerF` is convex on `[0, ∞)` because its second derivative is nonnegative there.
  have hconvex : ConvexOn ℝ (Set.Ici 0) pinskerF :=
    convexOn_of_hasDerivWithinAt2_nonneg (f' := pinskerDF) (f'' := pinskerD2F)
      (convex_Ici 0) continuous_pinskerF.continuousOn
      (fun y hy => by
        rw [interior_Ici] at hy
        exact (hasDerivAt_pinskerF (Set.mem_Ioi.mp hy).ne').hasDerivWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        exact (hasDerivAt_pinskerDF (Set.mem_Ioi.mp hy).ne').hasDerivWithinAt)
      (fun y hy => by
        rw [interior_Ici] at hy
        exact pinskerD2F_nonneg (Set.mem_Ioi.mp hy))
  -- The right derivative at `1` vanishes, so `1` is a global minimiser on `[0, ∞)`.
  have hrd : derivWithin pinskerF (Set.Ioi 1) 1 = 0 := by
    rw [(hasDerivAt_pinskerF one_ne_zero).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 1)]
    simp only [pinskerDF, Real.log_one]
    ring
  have hmin : IsMinOn pinskerF (Set.Ici 0) 1 :=
    hconvex.isMinOn_of_rightDeriv_eq_zero (by rw [interior_Ici]; exact Set.mem_Ioi.mpr one_pos) hrd
  have hF1 : pinskerF 1 = 0 := by simp only [pinskerF, Real.log_one]; ring
  have h := isMinOn_iff.mp hmin x (Set.mem_Ici.mpr hx)
  rwa [hF1] at h

/-- Quadratic (rational) lower bound on `klFun x = x * log x + 1 - x`, the analytic core of the
finite Pinsker inequality. The constant `3 / (2x + 4)` is tuned so that summing this bound over a
finite distribution yields Pinsker's inequality with the sharp constant `1 / 2`. -/
lemma klFun_quad_lower (x : ℝ) (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * x + 4) ≤ x * Real.log x + 1 - x := by
  have hpos : (0 : ℝ) < 2 * x + 4 := by linarith
  rw [div_le_iff₀ hpos]
  have h := pinskerF_nonneg hx
  unfold pinskerF at h
  nlinarith [h]

#print axioms klFun_quad_lower

/-!
## Pinsker's inequality for finite distributions

`(1/2) * (∑ |p i - q i|)² ≤ ∑ p i * log (p i / q i)`, assembled from the per-coordinate quadratic
bound `klFun_quad_lower` and the Engel/Titu form of Cauchy–Schwarz
(`Finset.sq_sum_div_le_sum_sq_div`) with weights `(2 p i + 4 q i) / 3`.
-/

/-- Per-coordinate bound: scaling `klFun_quad_lower` at `x = p / q` by `q`. -/
private lemma pinsker_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 * (p - q) ^ 2 / (2 * p + 4 * q) ≤ p * Real.log (p / q) + q - p := by
  have hq0 : q ≠ 0 := hq.ne'
  have hpq : 0 ≤ p / q := div_nonneg hp hq.le
  have hd1 : (0 : ℝ) < 2 * (p / q) + 4 := by linarith
  have hd2 : (0 : ℝ) < 2 * p + 4 * q := by linarith
  have hkey := klFun_quad_lower (p / q) hpq
  rw [div_le_iff₀ hd1] at hkey
  rw [div_le_iff₀ hd2]
  have e1 : q ^ 2 * (3 * (p / q - 1) ^ 2) = 3 * (p - q) ^ 2 := by
    field_simp
  have e2 : q ^ 2 * ((p / q * Real.log (p / q) + 1 - p / q) * (2 * (p / q) + 4))
      = (p * Real.log (p / q) + q - p) * (2 * p + 4 * q) := by
    field_simp
  calc 3 * (p - q) ^ 2
      = q ^ 2 * (3 * (p / q - 1) ^ 2) := e1.symm
    _ ≤ q ^ 2 * ((p / q * Real.log (p / q) + 1 - p / q) * (2 * (p / q) + 4)) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg q)
    _ = (p * Real.log (p / q) + q - p) * (2 * p + 4 * q) := e2

/-- **Pinsker's inequality** for finite probability distributions:
the squared total-variation distance is bounded by twice the relative entropy. -/
theorem pinsker {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (1 / 2) * (∑ i, |p i - q i|) ^ 2 ≤ ∑ i, p i * Real.log (p i / q i) := by
  -- Engel/Titu form of Cauchy–Schwarz with positive weights `g i = (2 p i + 4 q i) / 3`.
  have hgpos : ∀ i ∈ Finset.univ, 0 < (2 * p i + 4 * q i) / 3 := by
    intro i _
    have h1 := hp i; have h2 := hq i; positivity
  have hCS := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun i => |p i - q i|) hgpos
  -- The weights sum to `2`.
  have hsumg : ∑ i, (2 * p i + 4 * q i) / 3 = 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1]
    norm_num
  -- Each Cauchy–Schwarz term is the per-coordinate quadratic from `pinsker_term`.
  have hterm_eq : ∀ i, |p i - q i| ^ 2 / ((2 * p i + 4 * q i) / 3)
      = 3 * (p i - q i) ^ 2 / (2 * p i + 4 * q i) := by
    intro i
    have h2 : (2 * p i + 4 * q i) ≠ 0 := by have h1 := hp i; have h3 := hq i; positivity
    rw [sq_abs]
    field_simp
  -- Chain everything; the `+ q i - p i` bookkeeping cancels via `∑ q = ∑ p = 1`.
  have step1 : (∑ i, |p i - q i|) ^ 2 / 2 ≤ ∑ i, p i * Real.log (p i / q i) := by
    calc (∑ i, |p i - q i|) ^ 2 / 2
        = (∑ i, |p i - q i|) ^ 2 / (∑ i, (2 * p i + 4 * q i) / 3) := by rw [hsumg]
      _ ≤ ∑ i, |p i - q i| ^ 2 / ((2 * p i + 4 * q i) / 3) := hCS
      _ = ∑ i, 3 * (p i - q i) ^ 2 / (2 * p i + 4 * q i) :=
          Finset.sum_congr rfl (fun i _ => hterm_eq i)
      _ ≤ ∑ i, (p i * Real.log (p i / q i) + q i - p i) :=
          Finset.sum_le_sum (fun i _ => pinsker_term (hp i) (hq i))
      _ = ∑ i, p i * Real.log (p i / q i) + (∑ i, q i) - ∑ i, p i := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = ∑ i, p i * Real.log (p i / q i) := by rw [hp1, hq1]; ring
  linarith [step1]

#print axioms pinsker

/-!
## The log-sum inequality

`(∑ a i) * log ((∑ a i) / (∑ b i)) ≤ ∑ a i * log (a i / b i)` for `a ≥ 0`, `b > 0` on an arbitrary
`Finset`. This is finite Jensen applied to the convex function `x ↦ x * log x` with weights
`b i / B` and points `a i / b i` (where `B = ∑ b i`). It is the keystone behind the data-processing
inequality and joint convexity of relative entropy.
-/

/-- The **log-sum inequality**: for nonnegative `a` and positive `b` on a `Finset`,
`(∑ a i) · log ((∑ a i)/(∑ b i)) ≤ ∑ a i · log (a i / b i)`. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  · set A := ∑ i ∈ s, a i with hA
    set B := ∑ i ∈ s, b i with hB
    have hBpos : 0 < B := Finset.sum_pos hb hs
    have hBne : B ≠ 0 := hBpos.ne'
    -- The weights `b i / B` are nonnegative and sum to `1`.
    have hw1 : ∑ i ∈ s, b i / B = 1 := by
      rw [← Finset.sum_div, ← hB, div_self hBne]
    -- Finite Jensen for `φ x = x * log x` (convex on `[0, ∞)`).
    have hjensen := Real.convexOn_mul_log.map_sum_le
      (w := fun i => b i / B) (p := fun i => a i / b i)
      (fun i hi => div_nonneg (hb i hi).le hBpos.le) hw1
      (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
    simp only [smul_eq_mul] at hjensen
    -- Simplify the Jensen argument and the right-hand sum (each `b i` cancels).
    have eL : ∑ i ∈ s, b i / B * (a i / b i) = A / B := by
      rw [hA, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hbi : b i ≠ 0 := (hb i hi).ne'
      field_simp
    have eR : ∑ i ∈ s, b i / B * (a i / b i * Real.log (a i / b i))
        = (∑ i ∈ s, a i * Real.log (a i / b i)) / B := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hbi : b i ≠ 0 := (hb i hi).ne'
      field_simp
    rw [eL, eR] at hjensen
    -- `(A/B) log(A/B) ≤ (∑ …)/B`; clear the common positive denominator `B`.
    rw [div_mul_eq_mul_div] at hjensen
    rwa [div_le_div_iff_of_pos_right hBpos] at hjensen

#print axioms log_sum_inequality

/-!
## Data-processing inequality for discrete relative entropy

Under a deterministic map `f : ι → κ`, processing can only decrease relative entropy:
`∑ j, (f∗p) j · log ((f∗p) j / (f∗q) j) ≤ ∑ i, p i · log (p i / q i)`, where `f∗` is the
fiberwise pushforward. Each output term is the log-sum inequality on the fiber `f⁻¹{j}`.
-/

/-- Pushforward of `p : ι → ℝ` along `f : ι → κ`: the sum of `p` over each fiber of `f`. -/
def pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ] (f : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = j), p i

/-- **Data-processing inequality** (deterministic): the discrete relative entropy of the
pushforwards is at most that of the originals. -/
theorem relEntropy_pushforward_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    ∑ j, pushforward f p j * Real.log (pushforward f p j / pushforward f q j)
      ≤ ∑ i, p i * Real.log (p i / q i) := by
  -- Per output `j`, the log-sum inequality on the fiber `f⁻¹{j}`; sum over `j`.
  have hstep : ∑ j, pushforward f p j * Real.log (pushforward f p j / pushforward f q j)
      ≤ ∑ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), p i * Real.log (p i / q i) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact log_sum_inequality (Finset.univ.filter (fun i => f i = j)) p q
      (fun i _ => hp i) (fun i _ => hq i)
  -- Collapse the fibered double sum back to the total sum.
  rwa [Finset.sum_fiberwise Finset.univ f (fun i => p i * Real.log (p i / q i))] at hstep

#print axioms relEntropy_pushforward_le
