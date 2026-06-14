/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.FDivergence

/-! # The variational (Fenchel–Young) lower bound for `f`-divergences.

The convex-duality summit. Every `f`-divergence admits a variational representation: it is the
supremum, over test functions `g`, of `(∑ i, P i · g i) - (∑ i, Q i · f* (g i))`, where `f*` is the
convex conjugate of `f`. Here we prove the **lower-bound direction** (weak duality), which is the
master inequality from which the Donsker–Varadhan / Gibbs variational principle for KL and the
information-theoretic generalisation bound descend as special cases.

Rather than define `f*` as a supremum (awkward in Lean), we parametrise by a **Fenchel–Young pair**
`(f, fStar)` supplied through the hypothesis
`hYoung : ∀ t ≥ 0, ∀ s, t · s ≤ f t + fStar s`.
This is exactly the Fenchel–Young inequality, and it holds with equality when `fStar` is the exact
conjugate of `f`. Concrete instances discharge `hYoung` directly. The proof is a pointwise
application of `hYoung` at `t = P i / Q i`, weighted by `Q i` and summed — structurally like
`fDiv_nonneg` but simpler, requiring no Jensen step. -/

/-- **Variational lower bound for `f`-divergences** (Fenchel–Young / weak duality). For any
Fenchel–Young pair `(f, fStar)` — i.e. `t · s ≤ f t + fStar s` for all `t ≥ 0` and all `s` — and any
test function `g`,
`(∑ i, P i · g i) - (∑ i, Q i · fStar (g i)) ≤ D_f(P ‖ Q)`.
Taking the supremum over `g` recovers the variational representation of the `f`-divergence; the KL /
Gibbs variational principle and the downstream generalisation bound are members of this family. -/
theorem fDiv_variational {ι : Type*} [Fintype ι] (f fStar : ℝ → ℝ) (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hYoung : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, t * s ≤ f t + fStar s) :
    (∑ i, P i * g i) - (∑ i, Q i * fStar (g i)) ≤ fDiv f P Q := by
  -- Pointwise Fenchel–Young at `t = P i / Q i ≥ 0`, weighted by the positive `Q i`. The weighted
  -- left-hand side collapses via `Q i · (P i / Q i) = P i`.
  have hpt : ∀ i, P i * g i ≤ Q i * f (P i / Q i) + Q i * fStar (g i) := by
    intro i
    have hy := hYoung (P i / Q i) (div_nonneg (hP i) (hQ i).le) (g i)
    have h2 := mul_le_mul_of_nonneg_left hy (hQ i).le
    rw [mul_add] at h2
    rwa [show Q i * (P i / Q i * g i) = P i * g i from by
      rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (hQ i).ne']] at h2
  -- Sum the pointwise bounds and split the right-hand side.
  have hsum : (∑ i, P i * g i)
      ≤ (∑ i, Q i * f (P i / Q i)) + (∑ i, Q i * fStar (g i)) := by
    calc (∑ i, P i * g i)
        ≤ ∑ i, (Q i * f (P i / Q i) + Q i * fStar (g i)) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = (∑ i, Q i * f (P i / Q i)) + (∑ i, Q i * fStar (g i)) := Finset.sum_add_distrib
  -- Rearrange: `(∑ P·g) - (∑ Q·fStar) ≤ ∑ Q·f = D_f(P ‖ Q)`.
  simp only [fDiv]
  rwa [sub_le_iff_le_add]

#print axioms fDiv_variational

/-!
## The Kullback–Leibler instance: the Gibbs variational principle

Specialising the master inequality to the KL generating function `f t = t · log t`, paired with its
convex conjugate `f* s = e^{s-1}`, yields the **Gibbs variational principle** — the Fenchel–Young
(weak-duality) form of the Donsker–Varadhan variational representation of relative entropy. The
whole content beyond the master inequality is the pointwise Fenchel–Young inequality for this
conjugate pair, which collapses to a single application of `x + 1 ≤ eˣ`. -/

/-- **Fenchel–Young inequality for the KL conjugate pair** `(t · log t, e^{s-1})`: for `t ≥ 0` and
any `s`, `t · s ≤ t · log t + e^{s-1}`. The core is one application of `Real.add_one_le_exp`
(`x + 1 ≤ eˣ`) at `x = s - 1 - log t`. -/
theorem young_kl (t : ℝ) (ht : 0 ≤ t) (s : ℝ) :
    t * s ≤ t * Real.log t + Real.exp (s - 1) := by
  rcases eq_or_lt_of_le ht with h | h
  · -- `t = 0`: the bound reduces to `0 ≤ e^{s-1}`.
    subst h
    simp [(Real.exp_pos (s - 1)).le]
  · -- `0 < t`: `x + 1 ≤ eˣ` at `x = s - 1 - log t`, with `e^{s-1-log t} = e^{s-1}/t`.
    have hexp := Real.add_one_le_exp (s - 1 - Real.log t)
    rw [Real.exp_sub, Real.exp_log h] at hexp
    -- `hexp : (s - 1 - log t) + 1 ≤ e^{s-1}/t`, i.e. `s - log t ≤ e^{s-1}/t`.
    have h2 : s - Real.log t ≤ Real.exp (s - 1) / t := by linarith
    -- Multiply by `t > 0`: `(s - log t)·t ≤ e^{s-1}`, then rearrange via `ring`/`linarith`.
    have h3 := (le_div_iff₀ h).mp h2
    have heq : (s - Real.log t) * t = t * s - t * Real.log t := by ring
    linarith [h3, heq]

#print axioms young_kl

/-- **Gibbs variational principle** (KL member of the master-inequality family): for any test
function `g`, `(∑ i, P i · g i) - (∑ i, Q i · e^{g i - 1}) ≤ D(P ‖ Q)`. This is the Fenchel–Young
(weak-duality) form of the Donsker–Varadhan variational representation of relative entropy; strong
duality at the optimiser `g* = log (Q/P)` is the next rung. Obtained by instantiating
`fDiv_variational` at the KL conjugate pair `(t · log t, e^{s-1})` via `young_kl`, then identifying
`fDiv (t ↦ t · log t)` with the relative entropy through `fDiv_mul_log_eq_relEntropy`. -/
theorem relEntropy_variational {ι : Type*} [Fintype ι] (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    (∑ i, P i * g i) - (∑ i, Q i * Real.exp (g i - 1)) ≤ ∑ i, P i * Real.log (P i / Q i) := by
  have h := fDiv_variational (fun t => t * Real.log t) (fun s => Real.exp (s - 1)) P Q g hP hQ
    (fun t ht s => young_kl t ht s)
  rwa [fDiv_mul_log_eq_relEntropy P Q hQ] at h

#print axioms relEntropy_variational

/-!
## Donsker–Varadhan strong duality: the summit

The Donsker–Varadhan variational representation states that relative entropy is the *supremum* over
test functions `g` of the Donsker–Varadhan functional `g ↦ E_Q[g] - log E_P[e^g]`. We prove both
halves and package them as `IsGreatest`:

* **`≤` (weak duality).** Crucially, this direction is *derived from the master inequality*
  `relEntropy_variational`, not re-proved from scratch — exhibiting Donsker–Varadhan, and hence the
  whole generalisation-bound tower built on it, as a member of the `fDiv_variational` family. The
  step is a constant-optimisation substitution: feed the tilted test function `g + 1 - log Z`
  (with `Z = E_P[e^g]` the partition function) into the master inequality; the additive constant is
  chosen so the conjugate term `E_P[e^{·-1}]` collapses to `1`.
* **`=` (achievability).** At the optimiser `g* = log (Q/P)` the partition function `E_P[e^{g*}]`
  collapses to `∑ Q = 1`, so `log` of it vanishes and the functional attains exactly `D(Q ‖ P)`.

Together: `D(Q ‖ P)` is the greatest value of the Donsker–Varadhan functional. -/

/-- **Donsker–Varadhan, `≤` direction, derived from the master inequality.** For any test function
`g`, the Donsker–Varadhan functional `E_Q[g] - log E_P[e^g]` is at most `D(Q ‖ P)`. The proof feeds
the tilted test function `g + 1 - log Z` (`Z = E_P[e^g]`) into `relEntropy_variational`; the
conjugate term collapses to `1`, leaving exactly this bound. This exhibits the Donsker–Varadhan
inequality as a child of `fDiv_variational`. -/
theorem donsker_varadhan_le_of_variational {ι : Type*} [Fintype ι] (P Q g : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i)) ≤ ∑ i, Q i * Real.log (Q i / P i) := by
  -- `Finset.univ` is nonempty: otherwise `∑ Q i = 0 ≠ 1`.
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hQ1
    exact one_ne_zero hQ1.symm
  -- The partition function `Z = ∑ P · e^g` is strictly positive.
  set Z : ℝ := ∑ i, P i * Real.exp (g i) with hZ_def
  have hZ : 0 < Z := by
    rw [hZ_def]
    exact Finset.sum_pos (fun i _ => mul_pos (hP i) (Real.exp_pos _)) hne
  have hZne : Z ≠ 0 := hZ.ne'
  -- Term A: the tilted `Q`-mean, with the constant `1 - log Z` factored out via `∑ Q = 1`.
  have hA : (∑ i, Q i * (g i + 1 - Real.log Z)) = (∑ i, Q i * g i) + (1 - Real.log Z) := by
    have hcongr : ∀ i, Q i * (g i + 1 - Real.log Z) = Q i * g i + Q i * (1 - Real.log Z) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => hcongr i), Finset.sum_add_distrib, ← Finset.sum_mul,
        hQ1, one_mul]
  -- Term B: the conjugate term collapses to `Z / Z = 1` (the point of the `+1` tilt).
  have hB : (∑ i, P i * Real.exp ((g i + 1 - Real.log Z) - 1)) = 1 := by
    have hcongr : ∀ i, P i * Real.exp ((g i + 1 - Real.log Z) - 1) = P i * Real.exp (g i) / Z := by
      intro i
      have hexp : (g i + 1 - Real.log Z) - 1 = g i - Real.log Z := by ring
      rw [hexp, Real.exp_sub, Real.exp_log hZ, ← mul_div_assoc]
    rw [Finset.sum_congr rfl (fun i _ => hcongr i), ← Finset.sum_div, ← hZ_def, div_self hZne]
  -- The master inequality at the tilted test function `g + 1 - log Z`, then simplify both sums.
  have hmaster := relEntropy_variational Q P (fun i => g i + 1 - Real.log Z) (fun i => (hQ i).le) hP
  calc (∑ i, Q i * g i) - Real.log Z
      = (∑ i, Q i * (g i + 1 - Real.log Z))
          - (∑ i, P i * Real.exp ((g i + 1 - Real.log Z) - 1)) := by rw [hA, hB]; ring
    _ ≤ ∑ i, Q i * Real.log (Q i / P i) := hmaster

#print axioms donsker_varadhan_le_of_variational

/-- **Donsker–Varadhan achievability** at the optimiser `g* = log (Q/P)`. There the partition
function `∑ i, P i · e^{log (Q i / P i)} = ∑ i, Q i = 1`, so its log vanishes and the
Donsker–Varadhan functional attains exactly `D(Q ‖ P)`. -/
theorem donsker_varadhan_eq {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * Real.log (Q i / P i))
      - Real.log (∑ i, P i * Real.exp (Real.log (Q i / P i)))
    = ∑ i, Q i * Real.log (Q i / P i) := by
  -- The partition function at `g* = log (Q/P)` collapses to `∑ Q = 1`.
  have hsum : (∑ i, P i * Real.exp (Real.log (Q i / P i))) = 1 := by
    have hcongr : ∀ i, P i * Real.exp (Real.log (Q i / P i)) = Q i := by
      intro i
      rw [Real.exp_log (div_pos (hQ i) (hP i)), ← mul_div_assoc, mul_div_cancel_left₀ _ (hP i).ne']
    rw [Finset.sum_congr rfl (fun i _ => hcongr i), hQ1]
  -- `log 1 = 0`, so the subtracted term vanishes.
  rw [hsum, Real.log_one, sub_zero]

#print axioms donsker_varadhan_eq

/-- **Donsker–Varadhan strong duality** (the summit): relative entropy `D(Q ‖ P)` is the *greatest*
value of the Donsker–Varadhan functional `g ↦ E_Q[g] - log E_P[e^g]`. Membership is achievability at
`g* = log (Q/P)` (`donsker_varadhan_eq`); the upper bound is the variational `≤` direction derived
from the master inequality (`donsker_varadhan_le_of_variational`). -/
theorem donsker_varadhan {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i))}
               (∑ i, Q i * Real.log (Q i / P i)) := by
  refine ⟨⟨fun i => Real.log (Q i / P i), (donsker_varadhan_eq P Q hP hQ hQ1).symm⟩, ?_⟩
  rintro x ⟨g, rfl⟩
  exact donsker_varadhan_le_of_variational P Q g hP hQ hQ1

#print axioms donsker_varadhan

/-!
## The general-`f` variational representation: strong duality for every `f`-divergence

The Donsker–Varadhan summit is the KL face of a general phenomenon: *every* `f`-divergence is the
supremum of its variational functional `g ↦ E_P[g] - E_Q[f*(g)]`. The master inequality
`fDiv_variational` already gives the `≤` direction; the missing piece is achievability. Both facts
that made KL work are kept abstract and supplied as hypotheses, exactly as `hYoung` was:

* `hYoung` — the Fenchel–Young inequality `t · s ≤ f t + f* s` (gives `≤`), and
* `hconj` — the conjugate evaluated at the derivative, `f*(f' t) = t · f' t - f t`. This is the
  Fenchel–Young *equality* at the optimiser `s = f' t`; supplying it as a hypothesis means no
  differentiation is needed inside Lean.

At the optimiser `g* = f'(P/Q)` the variational functional attains exactly `D_f(P ‖ Q)`, so the
`f`-divergence is the *greatest* value of the functional (`IsGreatest`). Specialising to the KL pair
recovers the variational representation of relative entropy, closing the loop with `young_kl` and
`fDiv_mul_log_eq_relEntropy`. -/

/-- **Achievability of the general-`f` variational representation** at the optimiser `g* = f'(P/Q)`.
Using the conjugate-at-the-derivative identity `f*(f' t) = t · f' t - f t`, the variational
functional evaluated at `f'(P/Q)` collapses, term by term, to `Q i · f (P i / Q i)`, i.e. to
`D_f(P ‖ Q)`. -/
theorem fDiv_variational_eq {ι : Type*} [Fintype ι] (f fStar f' : ℝ → ℝ) (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t) :
    (∑ i, P i * f' (P i / Q i)) - (∑ i, Q i * fStar (f' (P i / Q i))) = fDiv f P Q := by
  simp only [fDiv]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Per term, `t = P i / Q i > 0`: substitute the conjugate identity and cancel `Q i·(P/Q) = P`.
  have ht : 0 < P i / Q i := div_pos (hP i) (hQ i)
  have hPi : Q i * (P i / Q i) = P i := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hQ i).ne']
  rw [hconj (P i / Q i) ht, mul_sub, ← mul_assoc, hPi]
  ring

#print axioms fDiv_variational_eq

/-- **Strong duality for every `f`-divergence**: `D_f(P ‖ Q)` is the *greatest* value of the
variational functional `g ↦ E_P[g] - E_Q[f*(g)]`. Membership is achievability at `g* = f'(P/Q)`
(`fDiv_variational_eq`); the upper bound is the master inequality `fDiv_variational`. The
Donsker–Varadhan theorem is the KL face of this statement. -/
theorem fDiv_variational_isGreatest {ι : Type*} [Fintype ι] (f fStar f' : ℝ → ℝ) (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hYoung : ∀ t, 0 ≤ t → ∀ s, t * s ≤ f t + fStar s)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, P i * g i) - (∑ i, Q i * fStar (g i))}
      (fDiv f P Q) := by
  refine ⟨⟨fun i => f' (P i / Q i), (fDiv_variational_eq f fStar f' P Q hP hQ hconj).symm⟩, ?_⟩
  rintro x ⟨g, rfl⟩
  exact fDiv_variational f fStar P Q g (fun i => (hP i).le) hQ hYoung

#print axioms fDiv_variational_isGreatest

/-- **KL strong duality as the `f = t · log t` instance** (loop closure): relative entropy
`D(P ‖ Q)` is the greatest value of `g ↦ E_P[g] - E_Q[e^{g-1}]`. Obtained from
`fDiv_variational_isGreatest` at the KL conjugate pair `(t · log t, e^{s-1})` with derivative
`f' t = log t + 1`; `hYoung` is `young_kl`, and `hconj` holds since both sides equal `t`. -/
theorem relEntropy_variational_isGreatest {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, P i * g i) - (∑ i, Q i * Real.exp (g i - 1))}
               (∑ i, P i * Real.log (P i / Q i)) := by
  -- The conjugate-at-the-derivative identity for the KL pair: both sides equal `t`.
  have hconj : ∀ t : ℝ, 0 < t →
      Real.exp ((Real.log t + 1) - 1) = t * (Real.log t + 1) - t * Real.log t := by
    intro t ht
    rw [show (Real.log t + 1) - 1 = Real.log t from by ring, Real.exp_log ht]
    ring
  have h := fDiv_variational_isGreatest (fun t => t * Real.log t) (fun s => Real.exp (s - 1))
    (fun t => Real.log t + 1) P Q hP hQ (fun t ht s => young_kl t ht s) hconj
  rwa [fDiv_mul_log_eq_relEntropy P Q hQ] at h

#print axioms relEntropy_variational_isGreatest

/-!
## The frontier summit: the data-processing inequality from convex duality

The data-processing inequality (DPI) — pushing `P, Q` through a Markov kernel `K` cannot increase
`D_f` — is usually proved by the `f`-log-sum inequality (`fDiv_kernel_le`). Here we derive it
instead *from the variational representation*, exhibiting DPI as a corollary of strong duality. The
argument
is the cleanest possible: the variational functional is built from a linear part and an `f*` part,
and a Markov kernel interacts perfectly with both —

* the **linear part** transforms by the kernel *adjoint* (a discrete Fubini swap `hadj`), turning an
  output test function `g*` into the pulled-back input test function `g x = ∑_y K x y · g* y`, and
* the **`f*` part** only *improves* under the kernel, by **Jensen** applied row-by-row (each kernel
  row is a probability vector, `f*` is convex).

So: pick the *optimal* output test function `g*` (achievability, `fDiv_variational_isGreatest`); its
value is `D_f` of the outputs. Pull it back through the kernel; the linear part is preserved exactly
(adjoint) while the conjugate part can only shrink (Jensen), and the resulting value is bounded by
`D_f(P ‖ Q)` via the master inequality `fDiv_variational`. Chaining gives DPI. `fStar` convexity is
supplied as `hfStar_cvx` (it is the convex conjugate of `f`). -/

/-- **Data-processing inequality for `f`-divergences, derived from the variational representation.**
For a Markov kernel `K` (strictly positive, row-stochastic), pushing `P, Q` through `K` cannot
increase `D_f`. The proof is the deepest unification in the development: achievability picks the
optimal output test function, the kernel *adjoint* (Fubini, `hadj`) pulls it back to the inputs
preserving the linear term, row-wise **Jensen** shows the conjugate term only shrinks, and the
master inequality `fDiv_variational` closes the chain — exhibiting DPI as a corollary of convex
duality. -/
theorem fDiv_kernel_le_of_variational {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳]
    (f fStar f' : ℝ → ℝ) (P Q : 𝒳 → ℝ) (K : 𝒳 → 𝒴 → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x)
    (hK : ∀ x y, 0 < K x y) (hKrow : ∀ x, ∑ y, K x y = 1)
    (hYoung : ∀ t, 0 ≤ t → ∀ s, t * s ≤ f t + fStar s)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t)
    (hfStar_cvx : ConvexOn ℝ Set.univ fStar) :
    fDiv f (fun y => ∑ x, P x * K x y) (fun y => ∑ x, Q x * K x y) ≤ fDiv f P Q := by
  -- Name the kernel pushforwards (matching `fDiv_kernel_le`'s inline convention).
  set Pf : 𝒴 → ℝ := fun y => ∑ x, P x * K x y with hPf_def
  set Qf : 𝒴 → ℝ := fun y => ∑ x, Q x * K x y with hQf_def
  -- The adjoint / pull-back identity (discrete Fubini), generic in the measure `R`.
  have hadj : ∀ (R : 𝒳 → ℝ) (h : 𝒴 → ℝ),
      (∑ y, (∑ x, R x * K x y) * h y) = ∑ x, R x * (∑ y, K x y * h y) := by
    intro R h
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  -- Output distributions are strictly positive (each fiber sum is positive, `𝒳` nonempty).
  have hP' : ∀ y, 0 < Pf y := by
    intro y
    simp only [hPf_def]
    exact Finset.sum_pos (fun x _ => mul_pos (hP x) (hK x y)) Finset.univ_nonempty
  have hQ' : ∀ y, 0 < Qf y := by
    intro y
    simp only [hQf_def]
    exact Finset.sum_pos (fun x _ => mul_pos (hQ x) (hK x y)) Finset.univ_nonempty
  -- Achievability at the output: extract the optimiser `gstar` from strong duality.
  obtain ⟨gstar, hgstar⟩ :=
    (fDiv_variational_isGreatest f fStar f' Pf Qf hP' hQ' hYoung hconj).1
  -- Pull the optimiser back through the kernel: `g x = ∑_y K x y · gstar y`.
  set g : 𝒳 → ℝ := fun x => ∑ y, K x y * gstar y with hg_def
  -- Linear term: the adjoint moves `gstar` from the outputs to the inputs, exactly.
  have hlin : (∑ y, Pf y * gstar y) = ∑ x, P x * g x := by
    simp only [hPf_def, hg_def]
    exact hadj P gstar
  -- Conjugate term: the `Q`-side adjoint.
  have hlinQ : (∑ y, Qf y * fStar (gstar y))
      = ∑ x, Q x * (∑ y, K x y * fStar (gstar y)) := by
    simp only [hQf_def]
    exact hadj Q (fun y => fStar (gstar y))
  -- Kernel-row Jensen (the crux): `fStar` convex, each kernel row a probability vector.
  have hjen : ∀ x, fStar (g x) ≤ ∑ y, K x y * fStar (gstar y) := by
    intro x
    have hj := hfStar_cvx.map_sum_le (w := fun y => K x y) (p := gstar)
      (fun y _ => (hK x y).le) (hKrow x) (fun y _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hj
    simp only [hg_def]
    exact hj
  -- Sum the Jensen bound against the nonnegative weights `Q x`.
  have hsumjen : (∑ x, Q x * fStar (g x)) ≤ ∑ x, Q x * (∑ y, K x y * fStar (gstar y)) :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hjen x) (hQ x).le)
  -- The master inequality at the pulled-back test function `g`.
  have hvar := fDiv_variational f fStar P Q g (fun x => (hP x).le) hQ hYoung
  -- Assemble: output value = input linear form minus a Jensen-dominated conjugate term ≤ D_f(P‖Q).
  linarith

#print axioms fDiv_kernel_le_of_variational
