/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.Shannon

/-! # Donsker–Varadhan inequality (easy direction).

The analytic seed of the information-theoretic generalization bound. For any function `g`, the gap
between the `Q`-mean of `g` and the log-partition function `log (∑ P · e^g)` under a reference `P`
is controlled by the relative entropy `D(Q ‖ P)`:
`(∑ Q · g) − log (∑ P · e^g) ≤ ∑ Q · log (Q / P)`.

This is Gibbs' inequality (`relEntropy_nonneg`) applied against the exponentially-tilted reference
measure `m i = P i · e^{g i} / Z`, structurally mirroring `entropy_le_log_card` in `Shannon.lean`
(Gibbs against a constructed reference + a per-term `log` split + a `∑ = 1` collapse). -/

/-- **Donsker–Varadhan inequality** (easy direction): the variational lower bound on relative
entropy. The `Q`-mean of `g` minus the log-partition function under `P` is at most `D(Q ‖ P)`. -/
theorem donsker_varadhan_le {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (g : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i)) ≤ ∑ i, Q i * Real.log (Q i / P i) := by
  -- `Finset.univ` is nonempty: otherwise `∑ P i = 0 ≠ 1`.
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hP1
    exact one_ne_zero hP1.symm
  -- The partition function `Z = ∑ P · e^g` is strictly positive.
  set Z : ℝ := ∑ i, P i * Real.exp (g i) with hZ_def
  have hZ : 0 < Z := by
    rw [hZ_def]
    exact Finset.sum_pos (fun i _ => mul_pos (hP i) (Real.exp_pos _)) hne
  -- The tilted reference `m i = P i · e^{g i} / Z` is a genuine probability distribution.
  set m : ι → ℝ := fun i => P i * Real.exp (g i) / Z with hm_def
  have hm_pos : ∀ i, 0 < m i := by
    intro i
    simp only [hm_def]
    exact div_pos (mul_pos (hP i) (Real.exp_pos _)) hZ
  have hm_sum : ∑ i, m i = 1 := by
    simp only [hm_def]
    rw [← Finset.sum_div, ← hZ_def, div_self hZ.ne']
  -- Gibbs' inequality against the tilted reference: `0 ≤ ∑ Q · log (Q / m)`.
  have hrel := relEntropy_nonneg Q m hQ hm_pos hQ1 hm_sum
  -- Per-term split of `log (Q i / m i)` using `m i = P i · e^{g i} / Z` and `log (e^{g i}) = g i`.
  have hterm : ∀ i, Q i * Real.log (Q i / m i)
      = Q i * Real.log (Q i / P i) + Q i * Real.log Z - Q i * g i := by
    intro i
    rcases (hQ i).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hPe : (0 : ℝ) < P i * Real.exp (g i) := mul_pos (hP i) (Real.exp_pos _)
      have hmval : m i = P i * Real.exp (g i) / Z := by simp only [hm_def]
      rw [hmval, Real.log_div h0.ne' (div_pos hPe hZ).ne', Real.log_div hPe.ne' hZ.ne',
          Real.log_mul (hP i).ne' (Real.exp_pos (g i)).ne', Real.log_exp,
          Real.log_div h0.ne' (hP i).ne']
      ring
  -- Sum the per-term identity; the `log Z` part collapses via `∑ Q = 1`.
  have hsum : ∑ i, Q i * Real.log (Q i / m i)
      = (∑ i, Q i * Real.log (Q i / P i)) + Real.log Z - (∑ i, Q i * g i) := by
    have hB : ∑ i, Q i * Real.log Z = Real.log Z := by
      rw [← Finset.sum_mul, hQ1, one_mul]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hB]
  rw [hsum] at hrel
  linarith

#print axioms donsker_varadhan_le

/-- **AM–GM optimisation lemma**: if `a ≤ c/λ + λ·d` for every `λ > 0`, then `a ≤ 2√(cd)`. The
right-hand side is the minimum of `λ ↦ c/λ + λ·d` over `λ > 0`, attained at `λ = √(c/d)`. This
isolates the `√` step in the sub-Gaussian decoupling argument. -/
theorem amgm_opt_le {a c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (h : ∀ lam : ℝ, 0 < lam → a ≤ c / lam + lam * d) :
    a ≤ 2 * Real.sqrt (c * d) := by
  rcases hc.eq_or_lt with rfl | hc_pos
  · -- `c = 0`: `a ≤ λ·d` for all `λ > 0`, so `a ≤ 0 = 2√(0·d)`.
    rw [zero_mul, Real.sqrt_zero, mul_zero]
    have hd0 : d ≠ 0 := hd.ne'
    refine le_of_forall_sub_le (fun ε hε => ?_)
    have hval := h (ε / d) (div_pos hε hd)
    have hsimp : (0 : ℝ) / (ε / d) + ε / d * d = ε := by
      rw [zero_div, zero_add, div_mul_eq_mul_div, mul_div_assoc, div_self hd0, mul_one]
    rw [hsimp] at hval
    linarith
  · -- `0 < c`: evaluate `h` at the minimiser `λ = √(c/d)`, where the bound is exactly `2√(cd)`.
    have hform : c / Real.sqrt (c / d) + Real.sqrt (c / d) * d = 2 * Real.sqrt (c * d) := by
      have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
      have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd
      rw [Real.sqrt_div hc_pos.le, Real.sqrt_mul hc_pos.le]
      -- Work in `u = √c`, `v = √d`; substitute `c = u·u`, `d = v·v` and clear denominators.
      set u := Real.sqrt c with hu
      set v := Real.sqrt d with hv
      have hu2 : u * u = c := by rw [hu]; exact Real.mul_self_sqrt hc_pos.le
      have hv2 : v * v = d := by rw [hv]; exact Real.mul_self_sqrt hd.le
      rw [← hu2, ← hv2]
      field_simp
      ring
    have hval := h (Real.sqrt (c / d)) (Real.sqrt_pos.mpr (div_pos hc_pos hd))
    rw [hform] at hval
    exact hval

#print axioms amgm_opt_le

/-- **Sub-Gaussian decoupling inequality** (the heart of the chapter): if `X` is sub-Gaussian under
`P` with parameter `σ` (the log-MGF bound `hsg`), then the change of mean from `P` to `Q` is
controlled by the relative entropy `D(Q ‖ P)`:
`(∑ Q · X) − (∑ P · X) ≤ √(2 σ² · D(Q ‖ P))`.

This is `donsker_varadhan_le` (a per-`λ` linear bound from the MGF) optimised over `λ > 0` via
`amgm_opt_le`. -/
theorem subgaussian_decouple {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (X : ι → ℝ) (σ : ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1)
    (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ, Real.log (∑ i, P i * Real.exp (lam * X i))
              ≤ lam * (∑ i, P i * X i) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ i, Q i * X i) - (∑ i, P i * X i)
      ≤ Real.sqrt (2 * σ ^ 2 * (∑ i, Q i * Real.log (Q i / P i))) := by
  set D := ∑ i, Q i * Real.log (Q i / P i) with hD_def
  have hD : 0 ≤ D := by rw [hD_def]; exact relEntropy_nonneg Q P hQ hP hQ1 hP1
  have hd2 : (0 : ℝ) < σ ^ 2 / 2 := by have h := pow_pos hσ 2; linarith
  -- Per-`λ` bound: Donsker–Varadhan at the tilt `λ·X`, combined with the sub-Gaussian MGF bound.
  have hbound : ∀ lam : ℝ, 0 < lam →
      (∑ i, Q i * X i) - (∑ i, P i * X i) ≤ D / lam + lam * (σ ^ 2 / 2) := by
    intro lam hlam
    have hlam0 : lam ≠ 0 := hlam.ne'
    have hdv := donsker_varadhan_le P Q (fun i => lam * X i) hP hQ hP1 hQ1
    simp only [] at hdv
    rw [← hD_def] at hdv
    have hmean : ∑ i, Q i * (lam * X i) = lam * (∑ i, Q i * X i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hmean] at hdv
    have hsg' := hsg lam
    have hval : (∑ i, Q i * X i) - (∑ i, P i * X i) ≤ (D + lam ^ 2 * σ ^ 2 / 2) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [hdv, hsg']
    have heq : (D + lam ^ 2 * σ ^ 2 / 2) / lam = D / lam + lam * (σ ^ 2 / 2) := by
      field_simp
    rw [heq] at hval
    exact hval
  -- Optimise over `λ`; the minimum value `2√(D·σ²/2)` equals `√(2σ²·D)`.
  have hfinal := amgm_opt_le hD hd2 hbound
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt : 2 * Real.sqrt (D * (σ ^ 2 / 2)) = Real.sqrt (2 * σ ^ 2 * D) := by
    have e4 : (2 : ℝ) * σ ^ 2 * D = 4 * (D * (σ ^ 2 / 2)) := by ring
    rw [e4, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]
  rw [hsqrt] at hfinal
  exact hfinal

#print axioms subgaussian_decouple

/-!
## Scalar Hoeffding inequality

The analytic core of Hoeffding's lemma: `log (1 - p + p·eʰ) - p·h ≤ h²/8` for `p ∈ [0,1]`. Proved by
the slack-function convexity method (structurally as `klFun_quad_lower` in `Basic.lean`): the slack
`φ(t) = t²/8 - (log(1-p+p·eᵗ) - p·t)` has `φ'' ≥ 0` (its bracketed term is `w(1-w) ≤ 1/4`) and a
critical point `φ'(0) = 0`, so `φ` attains its minimum value `φ(0) = 0` at `0`. -/

/-- Slack function `φ(t) = t²/8 - log(1-p+p·eᵗ) + p·t` for the scalar Hoeffding bound. -/
private noncomputable def hoeffSlack (p t : ℝ) : ℝ :=
  t ^ 2 / 8 - Real.log (1 - p + p * Real.exp t) + p * t

/-- First derivative of `hoeffSlack p`. -/
private noncomputable def hoeffSlackD (p t : ℝ) : ℝ :=
  t / 4 - p * Real.exp t / (1 - p + p * Real.exp t) + p

/-- Second derivative of `hoeffSlack p`. -/
private noncomputable def hoeffSlackD2 (p t : ℝ) : ℝ :=
  1 / 4 - p * Real.exp t * (1 - p) / (1 - p + p * Real.exp t) ^ 2

/-- The denominator `1 - p + p·eᵗ` is strictly positive for `p ∈ [0,1]`. -/
private lemma hoeff_Dpos (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 - p + p * Real.exp t := by
  rcases eq_or_lt_of_le hp0 with hp0' | hp0'
  · rw [← hp0']
    simp only [zero_mul, sub_zero, add_zero]
    exact one_pos
  · linarith [mul_pos hp0' (Real.exp_pos t)]

private lemma hasDerivAt_hoeffSlack (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (hoeffSlack p) (hoeffSlackD p t) t := by
  have hDpos : 0 < 1 - p + p * Real.exp t := hoeff_Dpos p t hp0 hp1
  unfold hoeffSlack hoeffSlackD
  have hexp : HasDerivAt (fun s => 1 - p + p * Real.exp s) (p * Real.exp t) t :=
    ((Real.hasDerivAt_exp t).const_mul p).const_add (1 - p)
  have hlog : HasDerivAt (fun s => Real.log (1 - p + p * Real.exp s))
      (p * Real.exp t / (1 - p + p * Real.exp t)) t := hexp.log hDpos.ne'
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 8) _ t := ((hasDerivAt_id' t).pow 2).div_const 8
  have hlin : HasDerivAt (fun s : ℝ => p * s) _ t := (hasDerivAt_id' t).const_mul p
  convert (hsq.sub hlog).add hlin using 1
  push_cast
  ring

private lemma hasDerivAt_hoeffSlackD (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (hoeffSlackD p) (hoeffSlackD2 p t) t := by
  have hDpos : 0 < 1 - p + p * Real.exp t := hoeff_Dpos p t hp0 hp1
  unfold hoeffSlackD hoeffSlackD2
  have hc : HasDerivAt (fun s => p * Real.exp s) (p * Real.exp t) t :=
    (Real.hasDerivAt_exp t).const_mul p
  have hexp : HasDerivAt (fun s => 1 - p + p * Real.exp s) (p * Real.exp t) t :=
    ((Real.hasDerivAt_exp t).const_mul p).const_add (1 - p)
  have hdiv : HasDerivAt (fun s => p * Real.exp s / (1 - p + p * Real.exp s))
      ((p * Real.exp t * (1 - p + p * Real.exp t) - p * Real.exp t * (p * Real.exp t))
        / (1 - p + p * Real.exp t) ^ 2) t := hc.div hexp hDpos.ne'
  have hqt : HasDerivAt (fun s : ℝ => s / 4) (1 / 4) t := (hasDerivAt_id' t).div_const 4
  convert (hqt.sub hdiv).add_const p using 1
  ring

private lemma hoeffSlackD2_nonneg (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ hoeffSlackD2 p t := by
  have hD2 : 0 < (1 - p + p * Real.exp t) ^ 2 := pow_pos (hoeff_Dpos p t hp0 hp1) 2
  unfold hoeffSlackD2
  rw [sub_nonneg, div_le_iff₀ hD2]
  nlinarith [sq_nonneg (1 - p - p * Real.exp t)]

/-- **Scalar Hoeffding inequality** (analytic core of Hoeffding's lemma): for `p ∈ [0,1]`,
`log (1 - p + p·eʰ) - p·h ≤ h² / 8`. -/
theorem hoeffding_scalar (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    Real.log (1 - p + p * Real.exp h) - p * h ≤ h ^ 2 / 8 := by
  -- `hoeffSlack p` is convex on `ℝ`, with right derivative `0` at `0`, hence minimised at `0`.
  have hconvex : ConvexOn ℝ Set.univ (hoeffSlack p) :=
    convexOn_of_hasDerivWithinAt2_nonneg (f' := hoeffSlackD p) (f'' := hoeffSlackD2 p)
      convex_univ
      (fun x _ => (hasDerivAt_hoeffSlack p x hp0 hp1).continuousAt.continuousWithinAt)
      (fun x _ => (hasDerivAt_hoeffSlack p x hp0 hp1).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_hoeffSlackD p x hp0 hp1).hasDerivWithinAt)
      (fun x _ => hoeffSlackD2_nonneg p x hp0 hp1)
  have hrd : derivWithin (hoeffSlack p) (Set.Ioi 0) 0 = 0 := by
    rw [(hasDerivAt_hoeffSlack p 0 hp0 hp1).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)]
    unfold hoeffSlackD
    rw [Real.exp_zero, show (1 : ℝ) - p + p * 1 = 1 from by ring]
    ring
  have hmin : IsMinOn (hoeffSlack p) Set.univ 0 :=
    hconvex.isMinOn_of_rightDeriv_eq_zero (by rw [interior_univ]; exact Set.mem_univ 0) hrd
  have h0 : hoeffSlack p 0 = 0 := by
    unfold hoeffSlack
    rw [Real.exp_zero, show (1 : ℝ) - p + p * 1 = 1 from by ring, Real.log_one]
    ring
  have hge := isMinOn_iff.mp hmin h (Set.mem_univ h)
  rw [h0] at hge
  unfold hoeffSlack at hge
  linarith

#print axioms hoeffding_scalar

/-- **Hoeffding's lemma**: a bounded random variable is sub-Gaussian. If `X ∈ [a, b]` `P`-a.e., then
its log-MGF is controlled by `λ·E[X] + λ²(b-a)²/8`. With `σ = (b-a)/2` this is exactly the
sub-Gaussian hypothesis `hsg` of `subgaussian_decouple` (`σ²/2 = (b-a)²/8`). -/
theorem hoeffding_mgf {ι : Type*} [Fintype ι] (P : ι → ℝ) (X : ι → ℝ) (a b : ℝ)
    (hP : ∀ i, 0 < P i) (hP1 : ∑ i, P i = 1)
    (hab : a < b) (hXa : ∀ i, a ≤ X i) (hXb : ∀ i, X i ≤ b) (lam : ℝ) :
    Real.log (∑ i, P i * Real.exp (lam * X i))
      ≤ lam * (∑ i, P i * X i) + lam ^ 2 * (b - a) ^ 2 / 8 := by
  have hba : 0 < b - a := by linarith
  have hba0 : b - a ≠ 0 := hba.ne'
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.sum_empty] at hP1
    exact one_ne_zero hP1.symm
  set μ := ∑ i, P i * X i with hμ_def
  -- The mean lies in `[a, b]`, so `p := (μ - a)/(b - a) ∈ [0, 1]`.
  have hμa : a ≤ μ := by
    rw [hμ_def]
    have ha : a = ∑ i, P i * a := by rw [← Finset.sum_mul, hP1, one_mul]
    rw [ha]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hXa i) (hP i).le)
  have hμb : μ ≤ b := by
    rw [hμ_def]
    have hb : b = ∑ i, P i * b := by rw [← Finset.sum_mul, hP1, one_mul]
    rw [hb]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hXb i) (hP i).le)
  set p := (μ - a) / (b - a) with hp_def
  have hp0 : 0 ≤ p := by rw [hp_def]; exact div_nonneg (by linarith) hba.le
  have hp1 : p ≤ 1 := by rw [hp_def, div_le_one hba]; linarith
  -- Pointwise convexity bound `e^{λx} ≤ w₁·e^{λa} + w₂·e^{λb}` for `x ∈ [a, b]`.
  have hkey : ∀ i, Real.exp (lam * X i)
      ≤ (b - X i) / (b - a) * Real.exp (lam * a) + (X i - a) / (b - a) * Real.exp (lam * b) := by
    intro i
    have hw1 : 0 ≤ (b - X i) / (b - a) := div_nonneg (by linarith [hXb i]) hba.le
    have hw2 : 0 ≤ (X i - a) / (b - a) := div_nonneg (by linarith [hXa i]) hba.le
    have hwsum : (b - X i) / (b - a) + (X i - a) / (b - a) = 1 := by
      rw [← add_div, show (b - X i) + (X i - a) = b - a from by ring, div_self hba0]
    have hconv := convexOn_exp.2 (Set.mem_univ (lam * a)) (Set.mem_univ (lam * b)) hw1 hw2 hwsum
    simp only [smul_eq_mul] at hconv
    rwa [show (b - X i) / (b - a) * (lam * a) + (X i - a) / (b - a) * (lam * b) = lam * X i from by
      field_simp; ring] at hconv
  -- Weight by `P i` and sum.
  have hsum_le : ∑ i, P i * Real.exp (lam * X i)
      ≤ ∑ i, P i * ((b - X i) / (b - a) * Real.exp (lam * a)
        + (X i - a) / (b - a) * Real.exp (lam * b)) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hkey i) (hP i).le)
  -- The weighted sums of the affine weights collapse to `b - μ` and `μ - a`.
  have hsX : ∑ i, P i * (b - X i) = b - μ := by
    have e : ∑ i, P i * (b - X i) = (∑ i, P i) * b - ∑ i, P i * X i := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hP1, one_mul, ← hμ_def]
  have hsXa : ∑ i, P i * (X i - a) = μ - a := by
    have e : ∑ i, P i * (X i - a) = (∑ i, P i * X i) - (∑ i, P i) * a := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, hP1, one_mul, ← hμ_def]
  have hRHS_eq : ∑ i, P i * ((b - X i) / (b - a) * Real.exp (lam * a)
        + (X i - a) / (b - a) * Real.exp (lam * b))
      = (1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b) := by
    have hcollect : ∑ i, P i * ((b - X i) / (b - a) * Real.exp (lam * a)
          + (X i - a) / (b - a) * Real.exp (lam * b))
        = (∑ i, P i * (b - X i)) * (Real.exp (lam * a) / (b - a))
          + (∑ i, P i * (X i - a)) * (Real.exp (lam * b) / (b - a)) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcollect, hsX, hsXa, hp_def]
    field_simp
    ring
  -- Take logs.
  have hApos : 0 < ∑ i, P i * Real.exp (lam * X i) :=
    Finset.sum_pos (fun i _ => mul_pos (hP i) (Real.exp_pos _)) hne
  have hfactor : (1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b)
      = Real.exp (lam * a) * (1 - p + p * Real.exp (lam * (b - a))) := by
    rw [show lam * b = lam * a + lam * (b - a) from by ring, Real.exp_add]
    ring
  have hinner_pos : 0 < 1 - p + p * Real.exp (lam * (b - a)) := hoeff_Dpos p (lam * (b - a)) hp0 hp1
  have hEa : 0 < Real.exp (lam * a) := Real.exp_pos _
  have hRpos : 0 < (1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b) := by
    rw [hfactor]; exact mul_pos hEa hinner_pos
  have hlog_le : Real.log (∑ i, P i * Real.exp (lam * X i))
      ≤ Real.log ((1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b)) := by
    apply (Real.log_le_log_iff hApos hRpos).mpr
    rw [← hRHS_eq]
    exact hsum_le
  have hlogR : Real.log ((1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b))
      = lam * a + Real.log (1 - p + p * Real.exp (lam * (b - a))) := by
    rw [hfactor, Real.log_mul hEa.ne' hinner_pos.ne', Real.log_exp]
  have hscalar := hoeffding_scalar p hp0 hp1 (lam * (b - a))
  have hpba : p * (b - a) = μ - a := by rw [hp_def]; field_simp
  calc Real.log (∑ i, P i * Real.exp (lam * X i))
      ≤ Real.log ((1 - p) * Real.exp (lam * a) + p * Real.exp (lam * b)) := hlog_le
    _ = lam * a + Real.log (1 - p + p * Real.exp (lam * (b - a))) := hlogR
    _ ≤ lam * a + (p * (lam * (b - a)) + (lam * (b - a)) ^ 2 / 8) := by linarith [hscalar]
    _ = lam * μ + lam ^ 2 * (b - a) ^ 2 / 8 := by
        have he : p * (lam * (b - a)) = lam * (μ - a) := by
          rw [show p * (lam * (b - a)) = lam * (p * (b - a)) from by ring, hpba]
        rw [he]; ring

#print axioms hoeffding_mgf

/-- **Mutual-information generalization bound** (Xu–Raginsky), the headline theorem: for a joint
distribution `J` on `ζ × ω` and a bounded-difference test function `X` that is sub-Gaussian under
the product of marginals, the gap between the `J`-mean of `X` and its product-of-marginals mean is
controlled by the mutual information `I(Z;W) = D(J ‖ marginal ⊗ marginal)`. This instantiates
`subgaussian_decouple` over `ζ × ω` at (joint vs product-of-marginals), where the KL term *is*
`mutualInfo J`. -/
theorem mutualInfo_generalization_bound {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (σ : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1) (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ,
        Real.log (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * Real.exp (lam * X z w))
          ≤ lam * (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt (2 * σ ^ 2 * mutualInfo J) := by
  -- `ζ` and `ω` are nonempty (else `∑∑ J = 0 ≠ 1`), so both marginals are strictly positive.
  have hζ : (Finset.univ : Finset ζ).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.sum_empty] at hJ1
    exact one_ne_zero hJ1.symm
  have hω : (Finset.univ : Finset ω).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    simp only [hc, Finset.sum_empty, Finset.sum_const_zero] at hJ1
    exact one_ne_zero hJ1.symm
  have hmZpos : ∀ z, 0 < ∑ w', J z w' := fun z => Finset.sum_pos (fun w _ => hJ z w) hω
  have hmWpos : ∀ w, 0 < ∑ z', J z' w := fun w => Finset.sum_pos (fun z _ => hJ z w) hζ
  -- Normalizations over `ζ × ω`: the product of marginals and the joint each sum to `1`.
  have hP1' : (∑ p : ζ × ω, (∑ w', J p.1 w') * (∑ z', J z' p.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ z, ∑ w, (∑ w', J z w') * (∑ z', J z' w)) = 1
    rw [← Finset.sum_mul_sum, hJ1, Finset.sum_comm, hJ1, mul_one]
  have hQ1' : (∑ p : ζ × ω, J p.1 p.2) = 1 := by
    rw [Fintype.sum_prod_type]; exact hJ1
  -- The sub-Gaussian hypothesis transported to the product index type.
  have hsg' : ∀ lam : ℝ,
      Real.log (∑ p : ζ × ω, (∑ w', J p.1 w') * (∑ z', J z' p.2) * Real.exp (lam * X p.1 p.2))
        ≤ lam * (∑ p : ζ × ω, (∑ w', J p.1 w') * (∑ z', J z' p.2) * X p.1 p.2)
          + lam ^ 2 * σ ^ 2 / 2 := by
    intro lam
    simp only [Fintype.sum_prod_type]
    exact hsg lam
  -- Decouple at (product-of-marginals as reference `P`, joint as `Q`) over `ζ × ω`.
  have hmain := subgaussian_decouple
    (fun p : ζ × ω => (∑ w', J p.1 w') * (∑ z', J z' p.2))
    (fun p : ζ × ω => J p.1 p.2)
    (fun p : ζ × ω => X p.1 p.2)
    σ
    (fun p => mul_pos (hmZpos p.1) (hmWpos p.2))
    (fun p => (hJ p.1 p.2).le)
    hP1' hQ1' hσ hsg'
  -- Convert the single sums over `ζ × ω` back to double sums; the KL term is `mutualInfo J`.
  simp only [Fintype.sum_prod_type] at hmain
  unfold mutualInfo
  exact hmain

#print axioms mutualInfo_generalization_bound

/-- **Bounded-loss mutual-information generalization bound**: the end-to-end corollary. For a
bounded test function `X ∈ [c, d]`, the sub-Gaussian hypothesis is discharged by `hoeffding_mgf`
(with `σ = (d-c)/2`), giving the named bound with the explicit constant `(d-c)²/2`. -/
theorem mutualInfo_generalization_bound_bounded {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (c d : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1)
    (hcd : c < d) (hXc : ∀ z w, c ≤ X z w) (hXd : ∀ z w, X z w ≤ d) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt ((d - c) ^ 2 / 2 * mutualInfo J) := by
  -- Product-measure facts over `ζ × ω` (as in `mutualInfo_generalization_bound`).
  have hζ : (Finset.univ : Finset ζ).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.sum_empty] at hJ1
    exact one_ne_zero hJ1.symm
  have hω : (Finset.univ : Finset ω).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    simp only [hc, Finset.sum_empty, Finset.sum_const_zero] at hJ1
    exact one_ne_zero hJ1.symm
  have hmZpos : ∀ z, 0 < ∑ w', J z w' := fun z => Finset.sum_pos (fun w _ => hJ z w) hω
  have hmWpos : ∀ w, 0 < ∑ z', J z' w := fun w => Finset.sum_pos (fun z _ => hJ z w) hζ
  have hPp_pos : ∀ p : ζ × ω, 0 < (∑ w', J p.1 w') * (∑ z', J z' p.2) :=
    fun p => mul_pos (hmZpos p.1) (hmWpos p.2)
  have hPp_sum1 : (∑ p : ζ × ω, (∑ w', J p.1 w') * (∑ z', J z' p.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    change (∑ z, ∑ w, (∑ w', J z w') * (∑ z', J z' w)) = 1
    rw [← Finset.sum_mul_sum, hJ1, Finset.sum_comm, hJ1, mul_one]
  have hσ : (0 : ℝ) < (d - c) / 2 := by linarith
  -- Sub-Gaussian hypothesis from Hoeffding's lemma on the product measure (constant matches).
  have hsg : ∀ lam : ℝ,
      Real.log (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * Real.exp (lam * X z w))
        ≤ lam * (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
          + lam ^ 2 * ((d - c) / 2) ^ 2 / 2 := by
    intro lam
    have hmgf := hoeffding_mgf
      (fun p : ζ × ω => (∑ w', J p.1 w') * (∑ z', J z' p.2))
      (fun p : ζ × ω => X p.1 p.2) c d
      hPp_pos hPp_sum1 hcd (fun p => hXc p.1 p.2) (fun p => hXd p.1 p.2) lam
    simp only [Fintype.sum_prod_type] at hmgf
    have hconst : lam ^ 2 * (d - c) ^ 2 / 8 = lam ^ 2 * ((d - c) / 2) ^ 2 / 2 := by ring
    rw [hconst] at hmgf
    exact hmgf
  have hmain := mutualInfo_generalization_bound J X ((d - c) / 2) hJ hJ1 hσ hsg
  -- Reconcile the constant inside the square root: `2·((d-c)/2)² = (d-c)²/2`.
  rw [show (2 : ℝ) * ((d - c) / 2) ^ 2 = (d - c) ^ 2 / 2 from by ring] at hmain
  exact hmain

#print axioms mutualInfo_generalization_bound_bounded
