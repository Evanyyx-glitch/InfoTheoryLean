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

/-!
## Mutual information and the chain rule `I(X;Y) = H(X) + H(Y) − H(X,Y)`

For a joint distribution `r` on `X × Y`, the mutual information equals the sum of the marginal
entropies minus the joint entropy. This is a purely algebraic identity (no normalization of `r` is
needed), obtained by splitting `log (r / (marg_X · marg_Y))` termwise.
-/

/-- Joint entropy of a distribution `r` on `X × Y`. -/
noncomputable def jointEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    - ∑ x, ∑ y, r x y * Real.log (r x y)

/-- Mutual information of a joint distribution `r` (marginals `∑_y r` and `∑_x r`). -/
noncomputable def mutualInfo {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))

/-- **Mutual information equals marginal entropies minus joint entropy**:
`I(X;Y) = H(X) + H(Y) − H(X,Y)`. -/
theorem mutualInfo_eq_entropy_add_sub_jointEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r
      = entropy (fun x => ∑ y, r x y) + entropy (fun y => ∑ x, r x y) - jointEntropy r := by
  -- Termwise split of `log (r / (marg_X · marg_Y))`.
  have hterm : ∀ x y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))
      = r x y * Real.log (r x y) - r x y * Real.log (∑ y', r x y')
        - r x y * Real.log (∑ x', r x' y) := by
    intro x y
    have hu : (∑ y', r x y') ≠ 0 := (hX x).ne'
    have hv : (∑ x', r x' y) ≠ 0 := (hY y).ne'
    rcases (hr x y).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' (mul_ne_zero hu hv), Real.log_mul hu hv]; ring
  -- Mutual information as three double sums.
  have hMI : mutualInfo r = (∑ x, ∑ y, r x y * Real.log (r x y))
      - (∑ x, ∑ y, r x y * Real.log (∑ y', r x y'))
      - (∑ x, ∑ y, r x y * Real.log (∑ x', r x' y)) := by
    unfold mutualInfo
    simp only [hterm, Finset.sum_sub_distrib]
  -- The `marg_X` double sum collapses (log is constant along `y`).
  have h2 : (∑ x, ∑ y, r x y * Real.log (∑ y', r x y'))
      = ∑ x, (∑ y, r x y) * Real.log (∑ y, r x y) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
  -- The `marg_Y` double sum collapses after swapping the order of summation.
  have h3 : (∑ x, ∑ y, r x y * Real.log (∑ x', r x' y))
      = ∑ y, (∑ x, r x y) * Real.log (∑ x, r x y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_mul]
  -- The three sums are exactly `-jointEntropy`, `-entropy_X`, `-entropy_Y` by definition.
  have hEX : entropy (fun x => ∑ y, r x y)
      = - ∑ x, (∑ y, r x y) * Real.log (∑ y, r x y) := rfl
  have hEY : entropy (fun y => ∑ x, r x y)
      = - ∑ y, (∑ x, r x y) * Real.log (∑ x, r x y) := rfl
  have hJ : jointEntropy r = - ∑ x, ∑ y, r x y * Real.log (r x y) := rfl
  rw [hMI, h2, h3, hEX, hEY, hJ]
  ring

#print axioms mutualInfo_eq_entropy_add_sub_jointEntropy

/-!
## Conditional entropy

`H(X | Y) := H(X,Y) − H(Y)`. From the chain rule we get `I(X;Y) = H(X) − H(X|Y)`, and since mutual
information is non-negative (Gibbs), conditioning reduces entropy: `H(X|Y) ≤ H(X)`.
-/

/-- Conditional entropy `H(X | Y) := H(X,Y) − H(Y)`. -/
noncomputable def condEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    jointEntropy r - entropy (fun y => ∑ x, r x y)

/-- **`I(X;Y) = H(X) − H(X|Y)`**: rearrangement of the chain rule. -/
theorem mutualInfo_eq_entropy_sub_condEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r = entropy (fun x => ∑ y, r x y) - condEntropy r := by
  simp only [condEntropy]
  rw [mutualInfo_eq_entropy_add_sub_jointEntropy r hr hX hY]
  ring

/-- **Conditioning reduces entropy**: `H(X | Y) ≤ H(X)`. Follows from `I(X;Y) ≥ 0` (Gibbs). -/
theorem condEntropy_le_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    condEntropy r ≤ entropy (fun x => ∑ y, r x y) := by
  have hmi : 0 ≤ mutualInfo r := mutualInfo_nonneg r hr hr1 hX hY
  have h1 := mutualInfo_eq_entropy_sub_condEntropy r hr hX hY
  linarith [hmi, h1]

#print axioms mutualInfo_eq_entropy_sub_condEntropy
#print axioms condEntropy_le_entropy

/-- **Subadditivity of entropy**: `H(X,Y) ≤ H(X) + H(Y)`. Again a restatement of `I(X;Y) ≥ 0`. -/
theorem jointEntropy_le_entropy_add_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    jointEntropy r ≤ entropy (fun x => ∑ y, r x y) + entropy (fun y => ∑ x, r x y) := by
  have hmi : 0 ≤ mutualInfo r := mutualInfo_nonneg r hr hr1 hX hY
  have h1 := mutualInfo_eq_entropy_add_sub_jointEntropy r hr hX hY
  linarith [hmi, h1]

#print axioms jointEntropy_le_entropy_add_entropy

/-!
## Fano's inequality — core per-distribution bound

The binary entropy function `H_b`, and the key bound driving Fano's inequality: for a finite
distribution `q` with a distinguished symbol `i₀`, the entropy is controlled by the binary entropy
of the "error mass" `δ = 1 - q i₀` plus `δ · log (card − 1)`. The proof is Gibbs' inequality
(`relEntropy_nonneg`) against the reference distribution placing mass `1 - δ` on `i₀` and spreading
`δ` uniformly over the remaining `card − 1` symbols — no grouping or indicator machinery.
-/

/-- Binary entropy of a parameter `p ∈ [0,1]`, in nats. -/
noncomputable def binEntropy (p : ℝ) : ℝ := - p * Real.log p - (1 - p) * Real.log (1 - p)

/-- **Core Fano bound.** For a finite distribution `q` with a distinguished symbol `i₀`,
`H(q) ≤ H_b(1 − q i₀) + (1 − q i₀) · log (card ι − 1)`. -/
theorem entropy_le_binEntropy_add {ι : Type*} [Fintype ι] (q : ι → ℝ) (i₀ : ι)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hi₀ : 0 < q i₀)
    (hcard : 2 ≤ Fintype.card ι) :
    entropy q ≤ binEntropy (1 - q i₀) + (1 - q i₀) * Real.log ((Fintype.card ι : ℝ) - 1) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set δ : ℝ := 1 - q i₀ with hδ
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  have hn1_pos : 0 < n - 1 := by linarith
  have hn1_ne : n - 1 ≠ 0 := hn1_pos.ne'
  have hqi₀_le_1 : q i₀ ≤ 1 := by
    rw [← hq1]; exact Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i₀)
  rcases hqi₀_le_1.eq_or_lt with h | h
  · -- `q i₀ = 1`: all other mass vanishes, so `H(q) = 0` and the bound is `0`.
    have hsum0 : ∑ i ∈ Finset.univ.erase i₀, q i = 0 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i₀), hq1, h]; ring
    have hrest : ∀ i ∈ Finset.univ.erase i₀, q i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq i)).mp hsum0
    have hent0 : entropy q = 0 := by
      unfold entropy
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = i₀
      · rw [hi, h, Real.log_one, mul_zero]
      · rw [hrest i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩), zero_mul]
    have hδ0 : δ = 0 := by rw [hδ, h]; ring
    rw [hent0, hδ0]
    simp [binEntropy]
  · -- `q i₀ < 1`: Gibbs' inequality against the reference distribution `m`.
    have hδ_pos : 0 < δ := by rw [hδ]; linarith
    have hδ_ne : δ ≠ 0 := hδ_pos.ne'
    have h1δ : 1 - δ = q i₀ := by rw [hδ]; ring
    set m : ι → ℝ := fun i => if i = i₀ then (1 - δ) else δ / (n - 1) with hm
    have hmval : ∀ i, m i = if i = i₀ then (1 - δ) else δ / (n - 1) := fun i => congrFun hm i
    have hm_pos : ∀ i, 0 < m i := by
      intro i
      rw [hmval i]
      split_ifs with hi
      · rw [h1δ]; exact hi₀
      · exact div_pos hδ_pos hn1_pos
    have hcard_real : ((Fintype.card ι - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one, hn]
    -- The `card − 1` off-diagonal masses of `m` each equal `δ/(n−1)` and sum to `δ`.
    have hconst_sum : ∑ i ∈ Finset.univ.erase i₀, m i = δ := by
      have hconst : ∀ i ∈ Finset.univ.erase i₀, m i = δ / (n - 1) :=
        fun i hi => by rw [hmval i, if_neg (Finset.ne_of_mem_erase hi)]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, nsmul_eq_mul,
          hcard_real, mul_comm (n - 1) (δ / (n - 1)), div_mul_cancel₀ δ hn1_ne]
    have hm_sum : ∑ i, m i = 1 := by
      rw [← Finset.add_sum_erase Finset.univ m (Finset.mem_univ i₀), hconst_sum, hmval i₀,
          if_pos rfl]
      ring
    -- Gibbs: `0 ≤ ∑ q · log (q / m)`.
    have hrel := relEntropy_nonneg q m hq hm_pos hq1 hm_sum
    have hterm2 : ∀ i, q i * Real.log (q i / m i)
        = q i * Real.log (q i) - q i * Real.log (m i) := by
      intro i
      rcases (hq i).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · rw [Real.log_div h0.ne' (hm_pos i).ne']; ring
    have hsum2 : ∑ i, q i * Real.log (q i / m i)
        = (∑ i, q i * Real.log (q i)) - ∑ i, q i * Real.log (m i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm2 i)
    -- The cross-entropy `∑ q · log m` evaluates to `−H_b(δ) − δ·log(n−1)`.
    have hcross : ∑ i, q i * Real.log (m i)
        = (1 - δ) * Real.log (1 - δ) + δ * (Real.log δ - Real.log (n - 1)) := by
      rw [← Finset.add_sum_erase Finset.univ (fun i => q i * Real.log (m i)) (Finset.mem_univ i₀),
          hmval i₀, if_pos rfl, ← h1δ]
      congr 1
      have hconst : ∀ i ∈ Finset.univ.erase i₀, q i * Real.log (m i)
          = q i * Real.log (δ / (n - 1)) :=
        fun i hi => by rw [hmval i, if_neg (Finset.ne_of_mem_erase hi)]
      rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul,
          Finset.sum_erase_eq_sub (Finset.mem_univ i₀), hq1, Real.log_div hδ_ne hn1_ne, ← hδ]
    have hce : -∑ i, q i * Real.log (m i) = binEntropy δ + δ * Real.log (n - 1) := by
      rw [hcross]; unfold binEntropy; ring
    rw [hsum2] at hrel
    rw [← hce]
    unfold entropy
    linarith [hrel]

#print axioms entropy_le_binEntropy_add

/-- **Concavity of binary entropy** on `[0,1]`. Writing `H_b(p) = negMulLog p + negMulLog (1 − p)`,
each summand is concave (the second via the affine reparametrisation `p ↦ 1 − p`), and a sum of
concave functions is concave. Needed for the averaging step in the conditional Fano inequality. -/
theorem concaveOn_binEntropy : ConcaveOn ℝ (Set.Icc 0 1) binEntropy := by
  -- First summand: `negMulLog` restricted from `[0, ∞)` to `[0,1]`.
  have h1 : ConcaveOn ℝ (Set.Icc 0 1) (fun p => Real.negMulLog p) :=
    Real.concaveOn_negMulLog.subset Set.Icc_subset_Ici_self (convex_Icc 0 1)
  -- Second summand: `negMulLog (1 − p)`, concave since `p ↦ 1 − p` maps `[0,1]` into `[0, ∞)`.
  have h2 : ConcaveOn ℝ (Set.Icc 0 1) (fun p => Real.negMulLog (1 - p)) := by
    refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have hx0 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    have hy0 : (0 : ℝ) ≤ 1 - y := by linarith [hy.2]
    have key := Real.concaveOn_negMulLog.2 hx0 hy0 ha hb hab
    have heq : a • (1 - x) + b • (1 - y) = 1 - (a • x + b • y) := by
      simp only [smul_eq_mul]; linear_combination hab
    rwa [heq] at key
  -- `H_b = negMulLog · + negMulLog (1 − ·)`, then add the two concavities.
  have hbin : binEntropy = (fun p => Real.negMulLog p) + fun p => Real.negMulLog (1 - p) := by
    funext p
    simp only [Pi.add_apply, Real.negMulLog, binEntropy]
    ring
  rw [hbin]
  exact h1.add h2

#print axioms concaveOn_binEntropy

/-!
## Conditional entropy as expected entropy of the conditionals

`H(X | Y) = ∑_y P(Y = y) · H(X | Y = y)`, where `H(X | Y = y)` is the entropy of the conditional
distribution `x ↦ r x y / (∑ x', r x' y)`. A pure algebraic identity given positive `Y`-marginals;
the key decomposition used to assemble the conditional Fano inequality.
-/

/-- **Conditional entropy = expected entropy of the conditionals.** -/
theorem condEntropy_eq_sum_smul_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hs : ∀ y, 0 < ∑ x, r x y) :
    condEntropy r = ∑ y, (∑ x, r x y) * entropy (fun x => r x y / (∑ x', r x' y)) := by
  -- Pull the marginal `∑ x, r x y` inside the entropy sum, cancelling the normalisation.
  have hpull : ∀ y, (∑ x, r x y) * entropy (fun x => r x y / (∑ x', r x' y))
      = - ∑ x, r x y * Real.log (r x y / (∑ x, r x y)) := by
    intro y
    have hsy : (∑ x, r x y) ≠ 0 := (hs y).ne'
    have hent : entropy (fun x => r x y / (∑ x', r x' y))
        = - ∑ x, r x y / (∑ x, r x y) * Real.log (r x y / (∑ x, r x y)) := rfl
    rw [hent, mul_neg, Finset.mul_sum, neg_inj]
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ (r x y) hsy]
  -- Split each `log (r / marg)` into `log r − log marg`.
  have hsplit : ∀ y, ∑ x, r x y * Real.log (r x y / (∑ x, r x y))
      = (∑ x, r x y * Real.log (r x y)) - (∑ x, r x y) * Real.log (∑ x, r x y) := by
    intro y
    have hsy : (∑ x, r x y) ≠ 0 := (hs y).ne'
    have hterm : ∀ x, r x y * Real.log (r x y / (∑ x, r x y))
        = r x y * Real.log (r x y) - r x y * Real.log (∑ x, r x y) := by
      intro x
      rcases (hr x y).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · rw [Real.log_div h0.ne' hsy]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.sum_mul]
  -- Per-output identity: `marg · H(conditional) = marg·log marg − ∑ r·log r`.
  have hy : ∀ y, (∑ x, r x y) * entropy (fun x => r x y / (∑ x', r x' y))
      = (∑ x, r x y) * Real.log (∑ x, r x y) - ∑ x, r x y * Real.log (r x y) := by
    intro y
    rw [hpull y, hsplit y]; ring
  -- Sum over `y`, swap the residual double sum, and match `condEntropy` definitionally.
  rw [Finset.sum_congr rfl (fun y _ => hy y), Finset.sum_sub_distrib, Finset.sum_comm,
      condEntropy]
  have hJ : jointEntropy r = - ∑ x, ∑ y, r x y * Real.log (r x y) := rfl
  have hE : entropy (fun y => ∑ x, r x y) = - ∑ y, (∑ x, r x y) * Real.log (∑ x, r x y) := rfl
  rw [hJ, hE]; ring

#print axioms condEntropy_eq_sum_smul_entropy

/-!
## Conditional Fano's inequality

For a joint law `r` on `X × X̂` (estimator `X̂` over the same alphabet `X`, with the diagonal
`y = x` the "correct" event and error probability `P_e = 1 − trace`), the conditional entropy is
controlled by `H_b(P_e) + P_e · log (card X − 1)`. Assembled from the per-output core Fano bound
(`entropy_le_binEntropy_add`), the decomposition `condEntropy_eq_sum_smul_entropy`, and Jensen's
inequality for the concave binary entropy (`concaveOn_binEntropy`).
-/

/-- **Conditional Fano's inequality.** -/
theorem condEntropy_le_binEntropy_add {X : Type*} [Fintype X]
    (r : X → X → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hdiag : ∀ y, 0 < r y y) (hcard : 2 ≤ Fintype.card X) :
    condEntropy r ≤ binEntropy (1 - ∑ x, r x x)
                    + (1 - ∑ x, r x x) * Real.log ((Fintype.card X : ℝ) - 1) := by
  -- The X̂-marginal is positive (the diagonal term alone is positive).
  have hs : ∀ y, 0 < ∑ x, r x y := fun y =>
    lt_of_lt_of_le (hdiag y) (Finset.single_le_sum (fun x _ => hr x y) (Finset.mem_univ y))
  -- The conditional `x ↦ r x y / marg` is a probability vector with positive diagonal coordinate.
  have hcn : ∀ y, ∀ x, 0 ≤ r x y / (∑ x', r x' y) := fun y x => div_nonneg (hr x y) (hs y).le
  have hcs : ∀ y, ∑ x, r x y / (∑ x', r x' y) = 1 := fun y => by
    rw [← Finset.sum_div]; exact div_self (hs y).ne'
  have hcd : ∀ y, 0 < r y y / (∑ x', r x' y) := fun y => div_pos (hdiag y) (hs y)
  -- STEP 1: conditional entropy as expected entropy of the conditionals (rung F3a).
  have hdecomp := condEntropy_eq_sum_smul_entropy r hr hs
  -- STEP 2: the core Fano bound applied per output (`i₀ = y`).
  have hper : ∀ y, entropy (fun x => r x y / (∑ x', r x' y))
      ≤ binEntropy (1 - r y y / (∑ x', r x' y))
        + (1 - r y y / (∑ x', r x' y)) * Real.log ((Fintype.card X : ℝ) - 1) :=
    fun y => entropy_le_binEntropy_add (fun x => r x y / (∑ x', r x' y)) y
      (hcn y) (hcs y) (hcd y) hcard
  -- STEP 3: weight each bound by the (nonnegative) marginal and sum.
  have h3 : condEntropy r ≤ ∑ y, (∑ x, r x y) *
      (binEntropy (1 - r y y / (∑ x', r x' y))
        + (1 - r y y / (∑ x', r x' y)) * Real.log ((Fintype.card X : ℝ) - 1)) := by
    rw [hdecomp]
    exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hper y) (hs y).le)
  -- STEP 4: the error mass collapses to `1 − trace`.
  have hPe : ∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)) = 1 - ∑ x, r x x := by
    have hterm : ∀ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)) = (∑ x, r x y) - r y y := by
      intro y
      have hsx : (∑ x, r x y) ≠ 0 := (hs y).ne'
      rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ (r y y) hsx]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_comm, hr1]
  -- STEP 5: Jensen for the concave binary entropy (weights = marginals, points in `[0,1]`).
  have hmem : ∀ y, (1 - r y y / (∑ x', r x' y)) ∈ Set.Icc (0 : ℝ) 1 := fun y =>
    ⟨by
        have hle : r y y / (∑ x', r x' y) ≤ 1 :=
          (div_le_one (hs y)).mpr (Finset.single_le_sum (fun x _ => hr x y) (Finset.mem_univ y))
        linarith,
      by have := (hcd y).le; linarith⟩
  have hw1 : ∑ y, (∑ x, r x y) = 1 := by rw [Finset.sum_comm]; exact hr1
  have hjensen : ∑ y, (∑ x, r x y) * binEntropy (1 - r y y / (∑ x', r x' y))
      ≤ binEntropy (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y))) := by
    simpa only [smul_eq_mul] using
      concaveOn_binEntropy.le_map_sum (fun y _ => (hs y).le) hw1 (fun y _ => hmem y)
  -- Split the weighted sum; the `log` block factors out via an explicit `sum_mul`.
  have hsplit : (∑ y, (∑ x, r x y) * (binEntropy (1 - r y y / (∑ x', r x' y))
          + (1 - r y y / (∑ x', r x' y)) * Real.log ((Fintype.card X : ℝ) - 1)))
      = (∑ y, (∑ x, r x y) * binEntropy (1 - r y y / (∑ x', r x' y)))
        + (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
            * Real.log ((Fintype.card X : ℝ) - 1) := by
    have hfac : (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
          * Real.log ((Fintype.card X : ℝ) - 1)
        = ∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y))
            * Real.log ((Fintype.card X : ℝ) - 1) :=
      Finset.sum_mul Finset.univ (fun y => (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
        (Real.log ((Fintype.card X : ℝ) - 1))
    rw [hfac, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  -- Assemble: split, apply Jensen to the binary-entropy block, rewrite the error mass.
  calc condEntropy r
      ≤ ∑ y, (∑ x, r x y) * (binEntropy (1 - r y y / (∑ x', r x' y))
            + (1 - r y y / (∑ x', r x' y)) * Real.log ((Fintype.card X : ℝ) - 1)) := h3
    _ = (∑ y, (∑ x, r x y) * binEntropy (1 - r y y / (∑ x', r x' y)))
          + (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
              * Real.log ((Fintype.card X : ℝ) - 1) := hsplit
    _ ≤ binEntropy (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
          + (∑ y, (∑ x, r x y) * (1 - r y y / (∑ x', r x' y)))
              * Real.log ((Fintype.card X : ℝ) - 1) := by linarith [hjensen]
    _ = binEntropy (1 - ∑ x, r x x) + (1 - ∑ x, r x x) * Real.log ((Fintype.card X : ℝ) - 1) := by
        rw [hPe]

#print axioms condEntropy_le_binEntropy_add
