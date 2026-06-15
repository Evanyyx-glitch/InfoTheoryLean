/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.Shannon

/-!
# Uniqueness of entropy: the functional-equation core

This file proves the analytic heart of the Faddeev / Shannon characterization of entropy: the only
*monotone* function `f : ℕ → ℝ` that turns multiplication into addition
(`f (m * n) = f m + f n`) is a constant multiple of the logarithm.

Mathlib does not (as of `v4.30.0`) contain this characterization — there is no Faddeev-style entropy
uniqueness theorem, and no "monotone multiplicative-to-additive ⟹ logarithm" lemma — so we prove it
from scratch.

The argument is the classical squeeze. Writing `m = ⌊k · log₂ n⌋` one has
`2 ^ m ≤ n ^ k ≤ 2 ^ (m+1)`, so monotonicity of `f` together with `f (a ^ j) = j · f a` pins
`k · f n` and `k · f 2 · log₂ n` to the same interval of length `f 2`. Hence
`|f n − f 2 · log₂ n| ≤ f 2 / k` for every `k`, and letting `k → ∞` (Archimedean) forces equality.

## Main statements

* `pow_le_pow_of_mul_log_le` — a monotonicity bridge: `p · log a ≤ q · log b` implies
  `a ^ p ≤ b ^ q` for natural numbers `a, b ≥ 1`.
* `additive_mono_eq_log` — a monotone additive-over-multiplication `f : ℕ → ℝ` equals
  `(f 2 / log 2) · log n` on every `n ≥ 1`.
-/

/-- If `p * log a ≤ q * log b` for naturals `a, b ≥ 1`, then `a ^ p ≤ b ^ q`.

This is the bridge between the real inequalities coming from floors of logarithms and the
natural-number powers that the monotone function `f` is actually evaluated on. -/
theorem pow_le_pow_of_mul_log_le {a b p q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : (p : ℝ) * Real.log a ≤ (q : ℝ) * Real.log b) : a ^ p ≤ b ^ q := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a from ha)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b from hb)
  have hap : (0 : ℝ) < (a : ℝ) ^ p := by positivity
  have hbq : (0 : ℝ) < (b : ℝ) ^ q := by positivity
  have hreal : (a : ℝ) ^ p ≤ (b : ℝ) ^ q := by
    rw [← Real.log_le_log_iff hap hbq, Real.log_pow, Real.log_pow]
    exact h
  exact_mod_cast hreal

/-- **The functional-equation core of entropy uniqueness.**

The only monotone function `f : ℕ → ℝ` satisfying `f (m * n) = f m + f n` for `m, n ≥ 1` is the
constant multiple `(f 2 / log 2) · log` of the logarithm. -/
theorem additive_mono_eq_log (f : ℕ → ℝ)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m + f n)
    (hmono : Monotone f) :
    ∀ n, 1 ≤ n → f n = (f 2 / Real.log 2) * Real.log n := by
  -- `f 1 = 0`, since `f 1 = f (1 * 1) = f 1 + f 1`.
  have hf1 : f 1 = 0 := by
    have h := hmul 1 1 le_rfl le_rfl
    rw [mul_one] at h; linarith
  -- `f (a ^ j) = j • f a` by induction on `j` (here for `a ≥ 1`).
  have f_pow : ∀ a : ℕ, 1 ≤ a → ∀ j : ℕ, f (a ^ j) = (j : ℝ) * f a := by
    intro a ha j
    induction j with
    | zero => simp [hf1]
    | succ j ih =>
        have h1 : 1 ≤ a ^ j := Nat.one_le_pow j a ha
        rw [pow_succ, hmul (a ^ j) a h1 ha, ih]; push_cast; ring
  -- `0 ≤ f 2`, from monotonicity and `f 1 = 0`.
  have hf2nn : 0 ≤ f 2 := by
    have h := hmono (show (1 : ℕ) ≤ 2 by norm_num)
    rwa [hf1] at h
  intro n hn
  rcases lt_or_ge n 2 with hn1 | hn2
  · -- Edge case `n = 1`: both sides vanish.
    interval_cases n
    simp [hf1]
  · -- Main case `n ≥ 2`.
    have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    -- Squeeze bound: for every `k ≥ 1`, `k · |f n − log₂ n · f 2| ≤ f 2`.
    have hbound : ∀ k : ℕ, 1 ≤ k →
        (k : ℝ) * |f n - (Real.log n / Real.log 2) * f 2| ≤ f 2 := by
      intro k hk1
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hkΛnn : (0 : ℝ) ≤ (k : ℝ) * (Real.log n / Real.log 2) := by positivity
      -- `m = ⌊k · log₂ n⌋` straddles `k · log₂ n`.
      obtain ⟨m, hm_le, hm_lt⟩ :
          ∃ m : ℕ, (m : ℝ) ≤ (k : ℝ) * (Real.log n / Real.log 2) ∧
            (k : ℝ) * (Real.log n / Real.log 2) < (m : ℝ) + 1 :=
        ⟨⌊(k : ℝ) * (Real.log n / Real.log 2)⌋₊, Nat.floor_le hkΛnn, Nat.lt_floor_add_one _⟩
      -- Turn the floor bounds into real power inequalities `2 ^ m ≤ n ^ k ≤ 2 ^ (m+1)`.
      have hlogA : (m : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log n := by
        have h := hm_le
        rw [← mul_div_assoc, le_div_iff₀ hc] at h
        exact h
      have hlogB : (k : ℝ) * Real.log n ≤ ((m : ℝ) + 1) * Real.log 2 := by
        have h := le_of_lt hm_lt
        rw [← mul_div_assoc, div_le_iff₀ hc] at h
        exact h
      have hA : (2 : ℕ) ^ m ≤ n ^ k := by
        apply pow_le_pow_of_mul_log_le
        · norm_num
        · omega
        · push_cast; exact hlogA
      have hB : n ^ k ≤ (2 : ℕ) ^ (m + 1) := by
        apply pow_le_pow_of_mul_log_le
        · omega
        · norm_num
        · push_cast; exact hlogB
      -- Evaluate `f` on the powers.
      have fA : f (2 ^ m) = (m : ℝ) * f 2 := f_pow 2 (by norm_num) m
      have fB : f (n ^ k) = (k : ℝ) * f n := f_pow n (by omega) k
      have fC : f (2 ^ (m + 1)) = (m : ℝ) * f 2 + f 2 := by
        rw [f_pow 2 (by norm_num) (m + 1)]; push_cast; ring
      -- Monotonicity of `f` sandwiches `k · f n`.
      have I_lo : (m : ℝ) * f 2 ≤ (k : ℝ) * f n := by
        have := hmono hA; rwa [fA, fB] at this
      have I_hi : (k : ℝ) * f n ≤ (m : ℝ) * f 2 + f 2 := by
        have := hmono hB; rwa [fB, fC] at this
      -- The floor bounds, scaled by `f 2 ≥ 0`, sandwich `k · log₂ n · f 2` in the same interval.
      have II_lo : (m : ℝ) * f 2 ≤ (k : ℝ) * (Real.log n / Real.log 2) * f 2 :=
        mul_le_mul_of_nonneg_right hm_le hf2nn
      have II_hi : (k : ℝ) * (Real.log n / Real.log 2) * f 2 ≤ (m : ℝ) * f 2 + f 2 := by
        have r := mul_le_mul_of_nonneg_right (le_of_lt hm_lt) hf2nn
        have e : ((m : ℝ) + 1) * f 2 = (m : ℝ) * f 2 + f 2 := by ring
        linarith
      -- Both quantities lie within `f 2` of each other.
      have h1 : (k : ℝ) * f n - (k : ℝ) * (Real.log n / Real.log 2) * f 2 ≤ f 2 := by linarith
      have h2 : -(f 2) ≤ (k : ℝ) * f n - (k : ℝ) * (Real.log n / Real.log 2) * f 2 := by linarith
      have hcomb : |(k : ℝ) * f n - (k : ℝ) * (Real.log n / Real.log 2) * f 2| ≤ f 2 :=
        abs_le.mpr ⟨h2, h1⟩
      have hfac : (k : ℝ) * f n - (k : ℝ) * (Real.log n / Real.log 2) * f 2
          = (k : ℝ) * (f n - (Real.log n / Real.log 2) * f 2) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (le_of_lt hkpos)] at hcomb
      exact hcomb
    -- A nonnegative number `≤ f 2 / k` for all `k` (i.e. `k · · ≤ f 2`) must be zero.
    have hDzero : |f n - (Real.log n / Real.log 2) * f 2| = 0 := by
      by_contra hDne
      have hDpos : 0 < |f n - (Real.log n / Real.log 2) * f 2| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hDne)
      obtain ⟨N, hN⟩ := Archimedean.arch (f 2) hDpos
      rw [nsmul_eq_mul] at hN
      have hb := hbound (N + 1) (by omega)
      push_cast at hb
      have e : ((N : ℝ) + 1) * |f n - (Real.log n / Real.log 2) * f 2|
          = (N : ℝ) * |f n - (Real.log n / Real.log 2) * f 2|
            + |f n - (Real.log n / Real.log 2) * f 2| := by ring
      rw [e] at hb
      linarith
    -- Unwind the absolute value and rearrange to the stated form.
    have hfn : f n = (Real.log n / Real.log 2) * f 2 := sub_eq_zero.mp (abs_eq_zero.mp hDzero)
    rw [hfn]; ring

/-- The uniform probability distribution on `Fin n`, assigning mass `1 / n` to each point. -/
noncomputable def uniformDist (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- The fiber of `Prod.fst : α × β → α` over a point `j` is canonically the second factor `β`. -/
def fiberFstEquiv {α β : Type*} [DecidableEq α] (j : α) : {x : α × β // x.1 = j} ≃ β where
  toFun x := x.1.2
  invFun b := ⟨(j, b), rfl⟩
  left_inv := by rintro ⟨⟨a, b⟩, rfl⟩; rfl
  right_inv := by intro b; rfl

/-- **Entropy of the uniform distribution is forced to be the logarithm.**

If an entropy functional `H` (taken here as a hypothesis, together with the Shannon–Khinchin axioms)
is invariant under relabelling, obeys the grouping/chain rule, and is monotone along the uniform
distributions, then `H (uniformDist n) = (H (uniformDist 2) / log 2) * log n`.

The proof uses the product trick: applying the grouping axiom to the uniform distribution on
`Fin m × Fin n` and the projection `Prod.fst` shows
`H (uniformDist (m * n)) = H (uniformDist m) + H (uniformDist n)`, so `n ↦ H (uniformDist n)`
satisfies the hypotheses of `additive_mono_eq_log`. -/
theorem uniform_entropy_eq_log
    (H : {ι : Type} → [Fintype ι] → (ι → ℝ) → ℝ)
    (hrelabel : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (p : κ → ℝ),
      H (p ∘ e) = H p)
    (hgroup : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ι → ℝ) (φ : ι → κ),
      (∀ i, 0 < p i) → (∑ i, p i = 1) →
      H p = H (fun j => ∑ i, if φ i = j then p i else 0)
            + ∑ j, (∑ i, if φ i = j then p i else 0)
                   * H (fun i : {x // φ x = j} => p i.1 / ∑ i', if φ i' = j then p i' else 0))
    (hmonoU : Monotone (fun n => H (uniformDist n))) :
    ∀ n, 1 ≤ n → H (uniformDist n) = (H (uniformDist 2) / Real.log 2) * Real.log n := by
  -- The key multiplicativity, obtained from the grouping axiom on a product.
  have hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      H (uniformDist (m * n)) = H (uniformDist m) + H (uniformDist n) := by
    intro m n hm hn
    have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hmnpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 0 < m * n := Nat.mul_pos hm hn
      exact_mod_cast this
    set c : ℝ := 1 / ((m * n : ℕ) : ℝ) with hc_def
    have hc_pos : 0 < c := by rw [hc_def]; exact one_div_pos.mpr hmnpos
    -- Uniform distribution on the product is a genuine distribution.
    have hppos : ∀ i : Fin m × Fin n, 0 < (fun _ : Fin m × Fin n => c) i := fun _ => hc_pos
    have hpsum : (∑ _i : Fin m × Fin n, c) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, hc_def, mul_one_div, div_self hmnpos.ne']
    -- Pushforward along `Prod.fst` is the uniform distribution on `Fin m`.
    have hpush : (fun j : Fin m => ∑ i : Fin m × Fin n, if i.1 = j then c else 0)
        = uniformDist m := by
      funext j
      rw [Fintype.sum_prod_type]
      dsimp only
      have inner : ∀ x : Fin m, (∑ _y : Fin n, if x = j then c else 0)
          = (n : ℝ) * (if x = j then c else 0) := fun x => by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show (∑ x : Fin m, ∑ _y : Fin n, if x = j then c else 0)
          = ∑ x : Fin m, (n : ℝ) * (if x = j then c else 0) from
        Finset.sum_congr rfl (fun x _ => inner x)]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [uniformDist]
      rw [hc_def, mul_one_div, show ((m * n : ℕ) : ℝ) = (n : ℝ) * (m : ℝ) by push_cast; ring,
        ← div_div, div_self hnne]
    -- Each fiber has total mass `1 / m`.
    have hw : ∀ j : Fin m, (∑ i : Fin m × Fin n, if i.1 = j then c else 0) = 1 / (m : ℝ) := by
      intro j
      have h := congrFun hpush j
      simpa [uniformDist] using h
    -- The conditional distribution on each fiber is uniform on `Fin n`.
    have hcond : ∀ j : Fin m,
        H (fun i : {x : Fin m × Fin n // x.1 = j} =>
            c / ∑ i' : Fin m × Fin n, if i'.1 = j then c else 0) = H (uniformDist n) := by
      intro j
      have hfun : (fun i : {x : Fin m × Fin n // x.1 = j} =>
          c / ∑ i' : Fin m × Fin n, if i'.1 = j then c else 0)
          = uniformDist n ∘ (fiberFstEquiv j) := by
        funext i
        rw [hw j]
        simp only [Function.comp_apply, uniformDist]
        rw [hc_def, one_div (m : ℝ), div_inv_eq_mul, mul_comm, mul_one_div,
          show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) by push_cast; ring, ← div_div, div_self hmne]
      rw [hfun]
      exact hrelabel (fiberFstEquiv j) (uniformDist n)
    -- The product distribution relabels to `uniformDist (m * n)`.
    have hLHS : H (fun _ : Fin m × Fin n => c) = H (uniformDist (m * n)) := by
      have he : (fun _ : Fin m × Fin n => c) = uniformDist (m * n) ∘ finProdFinEquiv := by
        funext x
        simp only [Function.comp_apply, uniformDist, hc_def]
      rw [he]
      exact hrelabel finProdFinEquiv (uniformDist (m * n))
    -- The grouping sum collapses to `H (uniformDist n)`.
    have hfibersum : (∑ j : Fin m, (∑ i : Fin m × Fin n, if i.1 = j then c else 0)
        * H (fun i : {x : Fin m × Fin n // x.1 = j} =>
            c / ∑ i' : Fin m × Fin n, if i'.1 = j then c else 0)) = H (uniformDist n) := by
      have step : (∑ j : Fin m, (∑ i : Fin m × Fin n, if i.1 = j then c else 0)
          * H (fun i : {x : Fin m × Fin n // x.1 = j} =>
              c / ∑ i' : Fin m × Fin n, if i'.1 = j then c else 0))
          = ∑ _j : Fin m, (1 / (m : ℝ)) * H (uniformDist n) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcond j, hw j]
      rw [step, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
        mul_one_div, div_self hmne, one_mul]
    -- Assemble.
    have hgrp := hgroup (fun _ : Fin m × Fin n => c) Prod.fst hppos hpsum
    simp only [] at hgrp
    rw [hLHS, hpush, hfibersum] at hgrp
    exact hgrp
  -- `n ↦ H (uniformDist n)` is monotone and multiplicative, so equals `C · log`.
  exact additive_mono_eq_log (fun n => H (uniformDist n)) hmul hmonoU

/-- The fiber of `Sigma.fst` over a point `j`, for a sigma of `Fin`s, is canonically `Fin (a j)`.
The dependent element `⟨⟨i, k⟩, (h : i = j)⟩` maps to `k : Fin (a i)` transported along `h`. -/
def fiberSigmaFstEquiv {n : ℕ} (a : Fin n → ℕ) (j : Fin n) :
    {x : Σ i : Fin n, Fin (a i) // x.fst = j} ≃ Fin (a j) where
  toFun x := x.2 ▸ x.1.2
  invFun m := ⟨⟨j, m⟩, rfl⟩
  left_inv := by rintro ⟨⟨i, k⟩, rfl⟩; rfl
  right_inv := by intro m; rfl

/-- **Entropy is forced on rational distributions.**

For the same axioms as `uniform_entropy_eq_log`, the value of `H` on any rational distribution
`p i = a i / ∑ a` (with `a i ≥ 1`) is `C · entropy p`, where `C = H (uniformDist 2) / log 2` and
`entropy` is the Shannon entropy. The argument mirrors `uniform_entropy_eq_log`, applying the
grouping axiom to the uniform distribution on `Σ i, Fin (a i)` (the variable-block-size analogue of
`Fin m × Fin n`) along `Sigma.fst`. -/
theorem rational_entropy_eq
    (H : {ι : Type} → [Fintype ι] → (ι → ℝ) → ℝ)
    (hrelabel : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (p : κ → ℝ), H (p ∘ e) = H p)
    (hgroup : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ι → ℝ) (φ : ι → κ),
      (∀ i, 0 < p i) → (∑ i, p i = 1) →
      H p = H (fun j => ∑ i, if φ i = j then p i else 0)
            + ∑ j, (∑ i, if φ i = j then p i else 0)
                   * H (fun i : {x // φ x = j} => p i.1 / ∑ i', if φ i' = j then p i' else 0))
    (hmonoU : Monotone (fun n => H (uniformDist n)))
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) :
    H (fun i => (a i : ℝ) / (∑ j, (a j : ℝ)))
      = (H (uniformDist 2) / Real.log 2) * entropy (fun i => (a i : ℝ) / (∑ j, (a j : ℝ))) := by
  set N : ℕ := ∑ j, a j with hN_def
  have hNpos : 0 < N := by
    rw [hN_def]
    exact Finset.sum_pos (fun i _ => ha i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hNrpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := hNrpos.ne'
  have haine : ∀ i, (a i : ℝ) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (show 0 < a i from ha i).ne'
  have hND : (N : ℝ) = ∑ j, (a j : ℝ) := by rw [hN_def, Nat.cast_sum]
  rw [← hND]
  set c : ℝ := 1 / (N : ℝ) with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; exact one_div_pos.mpr hNrpos
  -- The uniform distribution on the sigma type is a genuine distribution.
  have hppos : ∀ x : (Σ i : Fin n, Fin (a i)), 0 < (fun _ : (Σ i : Fin n, Fin (a i)) => c) x :=
    fun _ => hc_pos
  have hpsum : (∑ _x : (Σ i : Fin n, Fin (a i)), c) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← hN_def, nsmul_eq_mul, hc_def, mul_one_div, div_self hNne]
  -- Pushforward along `Sigma.fst` is `p`.
  have hpush : (fun j : Fin n => ∑ x : (Σ i : Fin n, Fin (a i)), if x.fst = j then c else 0)
      = fun i => (a i : ℝ) / (N : ℝ) := by
    funext j
    rw [Fintype.sum_sigma]
    dsimp only
    have inner : ∀ i : Fin n, (∑ _k : Fin (a i), if i = j then c else 0)
        = (a i : ℝ) * (if i = j then c else 0) := fun i => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (∑ i : Fin n, ∑ _k : Fin (a i), if i = j then c else 0)
        = ∑ i : Fin n, (a i : ℝ) * (if i = j then c else 0) from
      Finset.sum_congr rfl (fun i _ => inner i)]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hc_def, mul_one_div]
  have hw : ∀ j : Fin n, (∑ x : (Σ i : Fin n, Fin (a i)), if x.fst = j then c else 0)
      = (a j : ℝ) / (N : ℝ) := fun j => congrFun hpush j
  -- The conditional on each fiber is uniform on `Fin (a j)`.
  have hcond : ∀ j : Fin n,
      H (fun i : {x : Σ i : Fin n, Fin (a i) // x.fst = j} =>
          c / ∑ x' : (Σ i : Fin n, Fin (a i)), if x'.fst = j then c else 0)
        = H (uniformDist (a j)) := by
    intro j
    have hfun : (fun i : {x : Σ i : Fin n, Fin (a i) // x.fst = j} =>
        c / ∑ x' : (Σ i : Fin n, Fin (a i)), if x'.fst = j then c else 0)
        = uniformDist (a j) ∘ (fiberSigmaFstEquiv a j) := by
      funext i
      rw [hw j]
      simp only [Function.comp_apply, uniformDist]
      rw [hc_def, div_div_eq_mul_div, one_div_mul_cancel hNne]
    rw [hfun]
    exact hrelabel (fiberSigmaFstEquiv a j) (uniformDist (a j))
  -- The product distribution relabels to `uniformDist N`.
  have hLHS : H (fun _ : (Σ i : Fin n, Fin (a i)) => c) = H (uniformDist N) := by
    have hcard : Fintype.card (Σ i : Fin n, Fin (a i)) = N := by
      simp [Fintype.card_sigma, Fintype.card_fin, hN_def]
    have he : (fun _ : (Σ i : Fin n, Fin (a i)) => c)
        = uniformDist N ∘ (Fintype.equivFinOfCardEq hcard) := by
      funext x
      simp only [Function.comp_apply, uniformDist, hc_def]
    rw [he]
    exact hrelabel (Fintype.equivFinOfCardEq hcard) (uniformDist N)
  -- The grouping sum.
  have hfibersum : (∑ j : Fin n, (∑ x : (Σ i : Fin n, Fin (a i)), if x.fst = j then c else 0)
      * H (fun i : {x : Σ i : Fin n, Fin (a i) // x.fst = j} =>
          c / ∑ x' : (Σ i : Fin n, Fin (a i)), if x'.fst = j then c else 0))
      = ∑ j : Fin n, ((a j : ℝ) / (N : ℝ)) * H (uniformDist (a j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcond j, hw j]
  -- Assemble via the grouping axiom.
  have hgrp := hgroup (fun _ : (Σ i : Fin n, Fin (a i)) => c)
    (Sigma.fst : (Σ i : Fin n, Fin (a i)) → Fin n) hppos hpsum
  simp only [] at hgrp
  rw [hLHS, hpush, hfibersum] at hgrp
  -- Plug in the uniform-distribution values from `uniform_entropy_eq_log`.
  have hUa : ∀ j : Fin n, H (uniformDist (a j))
      = (H (uniformDist 2) / Real.log 2) * Real.log (a j) :=
    fun j => uniform_entropy_eq_log H hrelabel hgroup hmonoU (a j) (ha j)
  rw [uniform_entropy_eq_log H hrelabel hgroup hmonoU N hNpos] at hgrp
  simp only [hUa] at hgrp
  -- Compute the Shannon entropy of `p` in closed form.
  have hsum_p : (∑ i, (a i : ℝ) / (N : ℝ)) = 1 := by
    rw [← Finset.sum_div, ← hND, div_self hNne]
  have hentropy : entropy (fun i => (a i : ℝ) / (N : ℝ))
      = Real.log (N : ℝ) - ∑ j, ((a j : ℝ) / (N : ℝ)) * Real.log (a j) := by
    have hlog : ∀ i : Fin n, ((a i : ℝ) / (N : ℝ)) * Real.log ((a i : ℝ) / (N : ℝ))
        = ((a i : ℝ) / (N : ℝ)) * Real.log (a i) - ((a i : ℝ) / (N : ℝ)) * Real.log (N : ℝ) :=
      fun i => by rw [Real.log_div (haine i) hNne]; ring
    simp only [entropy]
    rw [show (∑ i, ((a i : ℝ) / (N : ℝ)) * Real.log ((a i : ℝ) / (N : ℝ)))
        = ∑ i, (((a i : ℝ) / (N : ℝ)) * Real.log (a i)
              - ((a i : ℝ) / (N : ℝ)) * Real.log (N : ℝ)) from
      Finset.sum_congr rfl (fun i _ => hlog i)]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_p, one_mul]
    ring
  -- Finish: solve `hgrp` for `H p` and match against `C · entropy p`.
  rw [hentropy, mul_sub, Finset.mul_sum]
  rw [show (∑ j, (H (uniformDist 2) / Real.log 2) * (((a j : ℝ) / (N : ℝ)) * Real.log (a j)))
      = ∑ j, ((a j : ℝ) / (N : ℝ)) * ((H (uniformDist 2) / Real.log 2) * Real.log (a j)) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  linarith [hgrp]

/-- **Shannon entropy is continuous.** As a function of the distribution `p`, the entropy
`entropy p = ∑ i, Real.negMulLog (p i)` is a finite sum of continuous functions (`Real.negMulLog`
is continuous everywhere, including at `0`). -/
theorem continuous_entropy {ι : Type} [Fintype ι] :
    Continuous (fun p : ι → ℝ => entropy p) := by
  have heq : (fun p : ι → ℝ => entropy p) = fun p => ∑ i, Real.negMulLog (p i) := by
    funext p
    unfold entropy
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib]
  rw [heq]
  exact continuous_finsetSum Finset.univ
    (fun i _ => Real.continuous_negMulLog.comp (continuous_apply i))

/-- The floor approximation `(⌊N·x⌋ + 1)/N` converges to `x` from above as `N → ∞`.
This is the engine that lets a real distribution be approached by rational ones. -/
theorem tendsto_floorApprox (x : ℝ) (hx : 0 ≤ x) :
    Filter.Tendsto (fun N : ℕ => ((⌊(N : ℝ) * x⌋₊ : ℝ) + 1) / (N : ℝ)) Filter.atTop (nhds x) := by
  have hupper : Filter.Tendsto (fun N : ℕ => x + 1 / (N : ℝ)) Filter.atTop (nhds x) := by
    have hc : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) := tendsto_const_nhds
    have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using hc.add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [le_div_iff₀ hNpos]
    have h := Nat.lt_floor_add_one ((N : ℝ) * x)
    linarith [h, mul_comm x (N : ℝ)]
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos, add_mul, one_div_mul_cancel hNpos.ne']
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) * x by positivity)
    linarith [hfloor, mul_comm x (N : ℝ)]

/-- **Entropy uniqueness (capstone).**

Under the Shannon–Khinchin axioms (`hrelabel`, `hgroup`, `hmonoU`) together with continuity of `H`,
the functional `H` equals `(H (uniformDist 2) / log 2) · entropy` on *every* finite distribution.
The rational case `rational_entropy_eq` is extended to all real distributions by approximating `p`
with the rational distributions built from `⌊N · p i⌋ + 1` and passing to the limit, using
continuity of both `H` and `entropy` and uniqueness of limits. -/
theorem entropy_uniqueness
    (H : {ι : Type} → [Fintype ι] → (ι → ℝ) → ℝ)
    (hrelabel : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (p : κ → ℝ), H (p ∘ e) = H p)
    (hgroup : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ι → ℝ) (φ : ι → κ),
      (∀ i, 0 < p i) → (∑ i, p i = 1) →
      H p = H (fun j => ∑ i, if φ i = j then p i else 0)
            + ∑ j, (∑ i, if φ i = j then p i else 0)
                   * H (fun i : {x // φ x = j} => p i.1 / ∑ i', if φ i' = j then p i' else 0))
    (hmonoU : Monotone (fun n => H (uniformDist n)))
    (hcont : ∀ {ι : Type} [Fintype ι], Continuous (fun p : ι → ℝ => H p))
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    H p = (H (uniformDist 2) / Real.log 2) * entropy p := by
  set C : ℝ := H (uniformDist 2) / Real.log 2 with hC
  -- The approximating rational distributions, built from `⌊N · p i⌋ + 1`.
  set aN : ℕ → Fin n → ℕ := fun N i => ⌊(N : ℝ) * p i⌋₊ + 1 with haN
  set q : ℕ → Fin n → ℝ := fun N i => (aN N i : ℝ) / (∑ j, (aN N j : ℝ)) with hq
  have ha1 : ∀ N i, 1 ≤ aN N i := by intro N i; simp only [haN]; omega
  -- Each `q N` is rational, so `rational_entropy_eq` applies.
  have hidentity : ∀ N, H (q N) = C * entropy (q N) := fun N =>
    rational_entropy_eq H hrelabel hgroup hmonoU hn (aN N) (fun i => ha1 N i)
  -- Coordinatewise: `aN N i / N → p i`.
  have hnum : ∀ i, Filter.Tendsto (fun N => (aN N i : ℝ) / (N : ℝ)) Filter.atTop (nhds (p i)) := by
    intro i
    refine (tendsto_floorApprox (p i) (hp i)).congr (fun N => ?_)
    simp only [haN]; push_cast; ring
  -- The denominators, scaled by `1/N`, tend to `∑ p = 1`.
  have hden : Filter.Tendsto (fun N => (∑ j, (aN N j : ℝ)) / (N : ℝ)) Filter.atTop (nhds 1) := by
    have hsum : Filter.Tendsto (fun N => ∑ j, (aN N j : ℝ) / (N : ℝ)) Filter.atTop
        (nhds (∑ j, p j)) := tendsto_finsetSum Finset.univ (fun j _ => hnum j)
    rw [hp1] at hsum
    refine hsum.congr (fun N => ?_)
    rw [Finset.sum_div]
  -- Coordinatewise `q N i → p i` by cancelling `N`.
  have hqi : ∀ i, Filter.Tendsto (fun N => q N i) Filter.atTop (nhds (p i)) := by
    intro i
    have hdiv := (hnum i).div hden one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Pi.div_apply, hq]
    rw [div_div_div_cancel_right₀ hNne]
  -- Hence `q → p` in the product topology.
  have hq_tendsto : Filter.Tendsto q Filter.atTop (nhds p) := tendsto_pi_nhds.mpr hqi
  -- Continuity transports the limit to `H` and to `C · entropy`.
  have hHq : Filter.Tendsto (fun N => H (q N)) Filter.atTop (nhds (H p)) :=
    (hcont.tendsto p).comp hq_tendsto
  have hEnt : Filter.Tendsto (fun N => C * entropy (q N)) Filter.atTop (nhds (C * entropy p)) :=
    ((continuous_entropy.const_mul C).tendsto p).comp hq_tendsto
  -- The two sequences agree termwise, so their limits coincide.
  have hfun_eq : (fun N => H (q N)) = fun N => C * entropy (q N) := funext hidentity
  rw [hfun_eq] at hHq
  exact tendsto_nhds_unique hHq hEnt

/-- **Entropy uniqueness, normalized form.** If, in addition to the Shannon–Khinchin axioms and
continuity, `H` is normalized so that `H (uniformDist 2) = log 2` (one bit on a fair coin), then `H`
*is* the Shannon entropy on every finite distribution. -/
theorem entropy_uniqueness_normalized
    (H : {ι : Type} → [Fintype ι] → (ι → ℝ) → ℝ)
    (hrelabel : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (p : κ → ℝ), H (p ∘ e) = H p)
    (hgroup : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ι → ℝ) (φ : ι → κ),
      (∀ i, 0 < p i) → (∑ i, p i = 1) →
      H p = H (fun j => ∑ i, if φ i = j then p i else 0)
            + ∑ j, (∑ i, if φ i = j then p i else 0)
                   * H (fun i : {x // φ x = j} => p i.1 / ∑ i', if φ i' = j then p i' else 0))
    (hmonoU : Monotone (fun n => H (uniformDist n)))
    (hcont : ∀ {ι : Type} [Fintype ι], Continuous (fun p : ι → ℝ => H p))
    (hnorm : H (uniformDist 2) = Real.log 2)
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    H p = entropy p := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [entropy_uniqueness H hrelabel hgroup hmonoU hcont hn p hp hp1, hnorm, div_self hlog2,
    one_mul]
