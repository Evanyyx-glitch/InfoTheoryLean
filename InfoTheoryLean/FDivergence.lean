/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.Basic

/-! # `f`-divergences: definition and non-negativity.

For a convex `f : ℝ → ℝ` with `f 1 = 0`, the `f`-divergence of a finite distribution `P` from a
strictly positive finite distribution `Q` is `D_f(P ‖ Q) = ∑ i, Q i · f (P i / Q i)`. It is
non-negative by convex Jensen's inequality (weights `Q i`, points `P i / Q i`), which directly
generalises Gibbs' inequality (`relEntropy_nonneg`, the case `f x = x log x`). -/

/-- The **`f`-divergence** of `P` from `Q` for a real function `f`:
`D_f(P ‖ Q) = ∑ i, Q i · f (P i / Q i)`. -/
noncomputable def fDiv {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (P Q : ι → ℝ) : ℝ :=
  ∑ i, Q i * f (P i / Q i)

/-- **Non-negativity of `f`-divergences**: for a convex `f` on `[0, ∞)` with `f 1 = 0`, the
`f`-divergence of a finite distribution `P` from a strictly positive finite distribution `Q` is
non-negative. This generalises Gibbs' inequality (`relEntropy_nonneg`). -/
theorem fDiv_nonneg {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hf1 : f 1 = 0)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ fDiv f P Q := by
  -- Convex Jensen with weights `Q i` (nonneg, summing to `1`) at points `P i / Q i ∈ [0, ∞)`.
  have hjensen := hf.map_sum_le (w := Q) (p := fun i => P i / Q i)
    (fun i _ => (hQ i).le) hQ1
    (fun i _ => Set.mem_Ici.mpr (div_nonneg (hP i) (hQ i).le))
  simp only [smul_eq_mul] at hjensen
  -- The Jensen argument collapses: `Q i * (P i / Q i) = P i`, so `∑ i, … = ∑ i, P i = 1`.
  have eL : ∑ i, Q i * (P i / Q i) = 1 := by
    rw [← hP1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hQ i).ne']
  -- Rewriting the left argument to `1` and using `f 1 = 0` gives `0 ≤ ∑ i, Q i * f (P i / Q i)`,
  -- which is `fDiv f P Q` by definition.
  rw [eL, hf1] at hjensen
  exact hjensen

#print axioms fDiv_nonneg

/-- The **`f`-divergence log-sum inequality**: for a convex `f` on `[0, ∞)`, nonnegative `a`, and
positive `b` on a `Finset`,
`(∑ b i) · f ((∑ a i)/(∑ b i)) ≤ ∑ b i · f (a i / b i)`. This is the abstract-convex-`f`
generalisation of `log_sum_inequality` (the case `f x = x · log x`) and the keystone behind the
data-processing inequality for `f`-divergences. -/
theorem fDiv_log_sum_ineq {ι : Type*} (s : Finset ι) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, b i) * f ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, b i * f (a i / b i) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  · set A := ∑ i ∈ s, a i with hA
    set B := ∑ i ∈ s, b i with hB
    have hBpos : 0 < B := Finset.sum_pos hb hs
    have hBne : B ≠ 0 := hBpos.ne'
    -- The weights `b i / B` are nonnegative and sum to `1`.
    have hw1 : ∑ i ∈ s, b i / B = 1 := by
      rw [← Finset.sum_div, ← hB, div_self hBne]
    -- Convex Jensen for `f` with weights `b i / B` and points `a i / b i ∈ [0, ∞)`.
    have hjensen := hf.map_sum_le
      (w := fun i => b i / B) (p := fun i => a i / b i)
      (fun i hi => div_nonneg (hb i hi).le hBpos.le) hw1
      (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
    simp only [smul_eq_mul] at hjensen
    -- The Jensen argument collapses to `A / B` (each `b i` cancels).
    have eL : ∑ i ∈ s, b i / B * (a i / b i) = A / B := by
      rw [hA, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hbi : b i ≠ 0 := (hb i hi).ne'
      field_simp
    -- The right-hand sum factors out the common denominator `B`.
    have eR : ∑ i ∈ s, b i / B * f (a i / b i) = (∑ i ∈ s, b i * f (a i / b i)) / B := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [div_mul_eq_mul_div]
    rw [eL, eR] at hjensen
    -- `f (A/B) ≤ (∑ …)/B`; multiply by the positive `B` and cancel to reach the goal.
    have h2 := mul_le_mul_of_nonneg_left hjensen hBpos.le
    rwa [← mul_div_assoc, mul_div_cancel_left₀ _ hBne] at h2

#print axioms fDiv_log_sum_ineq

/-!
## Stochastic-kernel (Markov) data-processing inequality for `f`-divergences

The crown of the `f`-divergence theory: for any stochastic kernel `K` (`K i j ≥ 0`,
`∑ j, K i j = 1`) and convex `f`, pushing `P, Q` through `K` cannot increase `D_f`. Each output `j`
reduces to the `f`-divergence log-sum inequality on the support `{i | K i j > 0}`, where
`(P i K i j)/(Q i K i j) = P i / Q i`. This is the abstract-convex-`f` generalisation of
`relEntropy_kernel_le` (the case `f x = x · log x`). -/

/-- Per-output bound (one column of the kernel): the `f`-divergence log-sum inequality on the
support of `K`, after cancelling `K i` in the argument of `f`. Denominator-weighted, matching the
`Q · f (P / Q)` shape of `fDiv`. -/
private lemma fDiv_kernel_term {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    (∑ i, Q i * K i) * f ((∑ i, P i * K i) / (∑ i, Q i * K i))
      ≤ ∑ i, Q i * K i * f (P i / Q i) := by
  classical
  set s := Finset.univ.filter (fun i => 0 < K i) with hs_def
  -- Off the support, `K i = 0`, so all three sums restrict to `s`.
  have hKzero : ∀ i, i ∉ s → K i = 0 := by
    intro i hi
    simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    exact le_antisymm hi (hK0 i)
  have eP : ∑ i, P i * K i = ∑ i ∈ s, P i * K i :=
    (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hKzero i hi, mul_zero])).symm
  have eQ : ∑ i, Q i * K i = ∑ i ∈ s, Q i * K i :=
    (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hKzero i hi, mul_zero])).symm
  have erhs : ∑ i, Q i * K i * f (P i / Q i)
      = ∑ i ∈ s, Q i * K i * f (P i / Q i) :=
    (Finset.sum_subset (Finset.subset_univ s)
      (fun i _ hi => by rw [hKzero i hi, mul_zero, zero_mul])).symm
  -- On the support, `Q i K i > 0`, and the argument of `f` simplifies to `P i / Q i`.
  have hb : ∀ i ∈ s, 0 < Q i * K i := by
    intro i hi
    simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact mul_pos (hQ i) hi
  have hRHS : ∑ i ∈ s, Q i * K i * f (P i * K i / (Q i * K i))
      = ∑ i ∈ s, Q i * K i * f (P i / Q i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [mul_div_mul_right _ _ hi.ne']
  have hflsi := fDiv_log_sum_ineq s f hf (fun i => P i * K i) (fun i => Q i * K i)
    (fun i _ => mul_nonneg (hP i) (hK0 i)) hb
  rw [eP, eQ, erhs, ← hRHS]
  exact hflsi

/-- **Data-processing inequality** for `f`-divergences under a stochastic kernel `K`: pushing
`P, Q` through `K` cannot increase the `f`-divergence. -/
theorem fDiv_kernel_le {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (K : ι → κ → ℝ) (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv f (fun j => ∑ i, P i * K i j) (fun j => ∑ i, Q i * K i j) ≤ fDiv f P Q := by
  simp only [fDiv]
  calc ∑ j, (∑ i, Q i * K i j) * f ((∑ i, P i * K i j) / (∑ i, Q i * K i j))
      ≤ ∑ j, ∑ i, Q i * K i j * f (P i / Q i) :=
        Finset.sum_le_sum
          (fun j _ => fDiv_kernel_term f hf (fun i => K i j) (fun i => hK0 i j) P Q hP hQ)
    _ = ∑ i, ∑ j, Q i * K i j * f (P i / Q i) := Finset.sum_comm
    _ = ∑ i, Q i * f (P i / Q i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum, hK1 i, mul_one]

#print axioms fDiv_kernel_le

/-!
## Joint convexity of the `f`-divergence

`(P, Q) ↦ ∑ i, Q i · f (P i / Q i)` is jointly convex: mixing two pairs `(P₁,Q₁)`, `(P₂,Q₂)` with
weight `lam` can only decrease the `f`-divergence of the mixture below the mixed divergences. Per
coordinate this is the two-term `f`-log-sum inequality applied to `(lam P₁, (1-lam) P₂)` over
`(lam Q₁, (1-lam) Q₂)`, with `lam` and `1 - lam` cancelling in the arguments of `f`. This is the
abstract-convex-`f` generalisation of `relEntropy_jointly_convex`. -/

/-- Two-term `f`-divergence log-sum inequality (the `Fin 2` instance of `fDiv_log_sum_ineq`).
Denominator-weighted, matching the `Q · f (P / Q)` shape of `fDiv`. -/
private lemma fDiv_two (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (x₁ x₂ y₁ y₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    (y₁ + y₂) * f ((x₁ + x₂) / (y₁ + y₂))
      ≤ y₁ * f (x₁ / y₁) + y₂ * f (x₂ / y₂) := by
  have h := fDiv_log_sum_ineq (Finset.univ : Finset (Fin 2)) f hf ![x₁, x₂] ![y₁, y₂]
    (by intro i _; fin_cases i <;> simp_all)
    (by intro i _; fin_cases i <;> simp_all)
  simpa [Fin.sum_univ_two] using h

/-- **Joint convexity** of the `f`-divergence in the pair `(P, Q)`, for a single mixing weight
`lam ∈ [0, 1]`. -/
theorem fDiv_jointly_convex {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (P₁ Q₁ P₂ Q₂ : ι → ℝ)
    (hP₁ : ∀ i, 0 ≤ P₁ i) (hQ₁ : ∀ i, 0 < Q₁ i)
    (hP₂ : ∀ i, 0 ≤ P₂ i) (hQ₂ : ∀ i, 0 < Q₂ i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fDiv f (fun i => lam * P₁ i + (1 - lam) * P₂ i) (fun i => lam * Q₁ i + (1 - lam) * Q₂ i)
      ≤ lam * fDiv f P₁ Q₁ + (1 - lam) * fDiv f P₂ Q₂ := by
  simp only [fDiv]
  rcases eq_or_lt_of_le hlam0 with hl0 | hlam_pos
  · subst hl0; simp
  · rcases eq_or_lt_of_le hlam1 with hl1 | hlam_lt
    · subst hl1; simp
    · -- Interior `0 < lam < 1`: per-coordinate two-term `f`-log-sum, then sum.
      have hlamne : lam ≠ 0 := hlam_pos.ne'
      have hμpos : 0 < 1 - lam := by linarith
      have hμne : (1 : ℝ) - lam ≠ 0 := hμpos.ne'
      have hcoord : ∀ i, (lam * Q₁ i + (1 - lam) * Q₂ i) *
            f ((lam * P₁ i + (1 - lam) * P₂ i) / (lam * Q₁ i + (1 - lam) * Q₂ i))
          ≤ lam * (Q₁ i * f (P₁ i / Q₁ i))
            + (1 - lam) * (Q₂ i * f (P₂ i / Q₂ i)) := by
        intro i
        have h := fDiv_two f hf (lam * P₁ i) ((1 - lam) * P₂ i) (lam * Q₁ i) ((1 - lam) * Q₂ i)
          (mul_nonneg hlam0 (hP₁ i)) (mul_nonneg hμpos.le (hP₂ i))
          (mul_pos hlam_pos (hQ₁ i)) (mul_pos hμpos (hQ₂ i))
        rw [mul_div_mul_left _ _ hlamne, mul_div_mul_left _ _ hμne, mul_assoc, mul_assoc] at h
        exact h
      calc (∑ i, (lam * Q₁ i + (1 - lam) * Q₂ i) *
              f ((lam * P₁ i + (1 - lam) * P₂ i) / (lam * Q₁ i + (1 - lam) * Q₂ i)))
          ≤ ∑ i, (lam * (Q₁ i * f (P₁ i / Q₁ i))
              + (1 - lam) * (Q₂ i * f (P₂ i / Q₂ i))) :=
            Finset.sum_le_sum (fun i _ => hcoord i)
        _ = lam * (∑ i, Q₁ i * f (P₁ i / Q₁ i))
              + (1 - lam) * (∑ i, Q₂ i * f (P₂ i / Q₂ i)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

#print axioms fDiv_jointly_convex

/-!
## The Kullback–Leibler instance: closing the loop with `Basic.lean`

Specialising `f x = x · log x` recovers the discrete relative entropy (Kullback–Leibler
divergence), so the abstract `f`-divergence theory subsumes the concrete results of `Basic.lean`.
The bridge identity below turns `fDiv_nonneg` into Gibbs' inequality (`relEntropy_nonneg`) as an
immediate corollary. -/

/-- **Bridge identity**: the `f`-divergence for `f x = x · log x` is exactly the discrete relative
entropy `∑ i, P i · log (P i / Q i)`. -/
theorem fDiv_mul_log_eq_relEntropy {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun x => x * Real.log x) P Q = ∑ i, P i * Real.log (P i / Q i) := by
  simp only [fDiv]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Per term: `Q i * ((P i / Q i) * log …) = P i * log …`, cancelling `Q i * (P i / Q i) = P i`.
  rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (hQ i).ne']

#print axioms fDiv_mul_log_eq_relEntropy

/-- **Gibbs' inequality as a corollary of `fDiv_nonneg`**: `f x = x · log x` is convex on `[0, ∞)`
with `f 1 = 0`, so the relative entropy is non-negative. (Stated as an `example` to avoid clashing
with `Basic.lean`'s `relEntropy_nonneg`.) -/
example {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, P i * Real.log (P i / Q i) := by
  rw [← fDiv_mul_log_eq_relEntropy P Q hQ]
  exact fDiv_nonneg _ Real.convexOn_mul_log (by simp [Real.log_one]) P Q hP hQ hP1 hQ1

/-!
## The Pearson χ²-divergence as an instance: the generality payoff

The χ²-divergence is the `f`-divergence for `f t = (t - 1)²`. Defining it through the same
`fDiv` and instantiating `fDiv_nonneg` yields its non-negativity for free — a second, structurally
different generating function handled by exactly the abstract machinery built above. -/

/-- **Bridge identity**: the `f`-divergence for `f t = (t - 1)²` is the Pearson χ²-divergence
`∑ i, (P i - Q i)² / Q i`. -/
theorem chiSq_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (t - 1) ^ 2) P Q = ∑ i, (P i - Q i) ^ 2 / Q i := by
  simp only [fDiv]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Per term: `Q i * (P i / Q i - 1)² = (P i - Q i)² / Q i`.
  have hq : Q i ≠ 0 := (hQ i).ne'
  field_simp

#print axioms chiSq_eq_fDiv

/-- **Non-negativity of the χ²-divergence** as a corollary of `fDiv_nonneg`: `f t = (t - 1)²` is
convex on `[0, ∞)` (its convexity gap is `a(1-a)(x-y)² ≥ 0`) with `f 1 = 0`. -/
theorem chiSq_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, (P i - Q i) ^ 2 / Q i := by
  -- `(t - 1)²` is convex on `[0, ∞)`, straight from the definition (the gap is `a(1-a)(x-y)²`).
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => (t - 1) ^ 2) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x _ y _ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [smul_eq_mul]
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  rw [← chiSq_eq_fDiv P Q hQ]
  exact fDiv_nonneg _ hconv (by norm_num) P Q hP hQ hP1 hQ1

#print axioms chiSq_nonneg

/-!
## The total-variation distance as an instance

The total-variation distance is the `f`-divergence for `f t = |t - 1|`, recovering the `L¹` distance
`∑ |P i − Q i|`. -/

/-- `f t = |t - 1|` is convex on `[0, ∞)` (the triangle inequality applied to the affine combination
`a(x-1) + b(y-1)`). -/
theorem convexOn_tvFun : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => |t - 1|) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  calc |a * x + b * y - 1|
      = |a * (x - 1) + b * (y - 1)| := by congr 1; linear_combination hab
    _ ≤ |a * (x - 1)| + |b * (y - 1)| := abs_add_le _ _
    _ = a * |x - 1| + b * |y - 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- **Bridge identity**: the `f`-divergence for `f t = |t - 1|` is the `L¹` (total-variation)
distance `∑ i, |P i - Q i|`. -/
theorem tv_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => |t - 1|) P Q = ∑ i, |P i - Q i| := by
  simp only [fDiv]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : Q i * (P i / Q i - 1) = P i - Q i := by
    rw [mul_sub, ← mul_div_assoc, mul_div_cancel_left₀ _ (hQ i).ne', mul_one]
  -- `Q i * |P i / Q i - 1| = |Q i · (P i / Q i - 1)| = |P i - Q i|`.
  calc Q i * |P i / Q i - 1|
      = |Q i| * |P i / Q i - 1| := by rw [abs_of_pos (hQ i)]
    _ = |Q i * (P i / Q i - 1)| := (abs_mul _ _).symm
    _ = |P i - Q i| := by rw [h1]

/-- **Non-negativity of the total-variation divergence** as a corollary of `fDiv_nonneg`. -/
theorem tv_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, |P i - Q i| := by
  rw [← tv_eq_fDiv P Q hQ]
  exact fDiv_nonneg _ convexOn_tvFun (by simp) P Q hP hQ hP1 hQ1

#print axioms convexOn_tvFun
#print axioms tv_eq_fDiv
#print axioms tv_nonneg

/-!
## The squared Hellinger distance as an instance

The squared Hellinger distance is the `f`-divergence for `f t = (√t - 1)²`, recovering
`∑ i, (√(P i) − √(Q i))²`. -/

/-- `f t = (√t - 1)²` is convex on `[0, ∞)`: it equals the affine `t + 1` plus the convex
`-2·√t` (since `√` is concave), via `(√t)² = t`. -/
theorem convexOn_hellingerFun : ConvexOn ℝ (Set.Ici 0) (fun t => (Real.sqrt t - 1) ^ 2) := by
  have h1 : ConvexOn ℝ (Set.Ici 0) ((id : ℝ → ℝ) + fun _ => 1) :=
    (convexOn_id (convex_Ici 0)).add_const 1
  have h2 := (Real.strictConcaveOn_sqrt.concaveOn.smul (by norm_num : (0 : ℝ) ≤ 2)).neg
  refine (h1.add h2).congr (fun t ht => ?_)
  have h0 : (0 : ℝ) ≤ t := Set.mem_Ici.mp ht
  simp only [Pi.add_apply, Pi.neg_apply, smul_eq_mul, id_eq]
  rw [show (Real.sqrt t - 1) ^ 2 = Real.sqrt t ^ 2 - 2 * Real.sqrt t + 1 from by ring,
      Real.sq_sqrt h0]
  ring

/-- **Bridge identity**: the `f`-divergence for `f t = (√t - 1)²` is the squared Hellinger
distance `∑ i, (√(P i) - √(Q i))²`. -/
theorem hellinger_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (Real.sqrt t - 1) ^ 2) P Q
      = ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2 := by
  simp only [fDiv]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `Q i * (√(P i / Q i) - 1)² = (√(P i) - √(Q i))²`, cancelling `Q i = (√(Q i))²`.
  rw [Real.sqrt_div (hP i) (Q i)]
  set u := Real.sqrt (P i) with hu
  set v := Real.sqrt (Q i) with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact (Real.sqrt_pos.mpr (hQ i)).ne'
  have hQv : Q i = v ^ 2 := by rw [hv]; exact (Real.sq_sqrt (hQ i).le).symm
  rw [hQv]
  field_simp

/-- **Non-negativity of the squared Hellinger distance** as a corollary of `fDiv_nonneg`. -/
theorem hellinger_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2 := by
  rw [← hellinger_eq_fDiv P Q hP hQ]
  exact fDiv_nonneg _ convexOn_hellingerFun (by simp [Real.sqrt_one]) P Q hP hQ hP1 hQ1

#print axioms convexOn_hellingerFun
#print axioms hellinger_eq_fDiv
#print axioms hellinger_nonneg
