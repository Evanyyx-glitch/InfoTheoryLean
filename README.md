# InfoTheoryLean

A Lean 4 formalization of the core inequalities of discrete information theory, built on [mathlib](https://github.com/leanprover-community/mathlib4). Every result is machine-checked and `sorry`-free.

Starting from Gibbs' inequality, the library develops the fundamental inequalities governing the **Kullback–Leibler divergence** (relative entropy) of finite distributions — up through **Pinsker's inequality**, the **data-processing inequality**, **joint convexity**, and the **non-negativity of mutual information**.

Author: Yuyang Xiao.

## Setting

For finite distributions `p, q : ι → ℝ` (with `ι` a `Fintype`), the relative entropy is written directly as the sum

```
∑ i, p i * Real.log (p i / q i).
```

All results live in [`InfoTheoryLean/Basic.lean`](InfoTheoryLean/Basic.lean).

## Results

### Foundations

**Gibbs' inequality** — relative entropy is non-negative.

```lean
theorem relEntropy_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i)
```

**Equality case** — the divergence vanishes exactly when the distributions agree.

```lean
theorem relEntropy_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, p i * Real.log (p i / q i) = 0 ↔ p = q
```

### Pinsker's inequality

A quadratic lower bound on `x·log x − x + 1` (the analytic core; established via a second-derivative bound that reduces to `1 − x⁻¹ ≤ log x`), then Pinsker via Cauchy–Schwarz.

```lean
lemma klFun_quad_lower (x : ℝ) (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * x + 4) ≤ x * Real.log x + 1 - x

theorem pinsker {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (1 / 2) * (∑ i, |p i - q i|) ^ 2 ≤ ∑ i, p i * Real.log (p i / q i)
```

### The log-sum inequality and its consequences

The log-sum inequality (arbitrary finite sums, no normalization required) is the keystone for the data-processing and convexity results.

```lean
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i)
```

**Data-processing inequality (deterministic map).** Relative entropy does not increase under a map `f : ι → κ`, where `pushforward f p` is the image distribution `j ↦ ∑_{i : f i = j} p i`.

```lean
theorem relEntropy_pushforward_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    ∑ j, pushforward f p j * Real.log (pushforward f p j / pushforward f q j)
      ≤ ∑ i, p i * Real.log (p i / q i)
```

**Data-processing inequality (Markov kernel).** The general form, for a stochastic kernel `K` (the deterministic case above is the special case `K i j = if f i = j then 1 else 0`). No normalization of `p, q` is required.

```lean
theorem relEntropy_kernel_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℝ) (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    ∑ j, (∑ i, p i * K i j) * Real.log ((∑ i, p i * K i j) / (∑ i, q i * K i j))
      ≤ ∑ i, p i * Real.log (p i / q i)
```

**Joint convexity.** Relative entropy is jointly convex in the pair `(p, q)`.

```lean
theorem relEntropy_jointly_convex {ι : Type*} [Fintype ι]
    (p₁ q₁ p₂ q₂ : ι → ℝ)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hq₁ : ∀ i, 0 < q₁ i)
    (hp₂ : ∀ i, 0 ≤ p₂ i) (hq₂ : ∀ i, 0 < q₂ i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (∑ i, (lam * p₁ i + (1 - lam) * p₂ i) *
          Real.log ((lam * p₁ i + (1 - lam) * p₂ i) / (lam * q₁ i + (1 - lam) * q₂ i)))
      ≤ lam * (∑ i, p₁ i * Real.log (p₁ i / q₁ i))
        + (1 - lam) * (∑ i, p₂ i * Real.log (p₂ i / q₂ i))
```

### Mutual information

**Non-negativity of mutual information** — `I(X; Y) = D(P_XY ‖ P_X ⊗ P_Y) ≥ 0`, obtained directly from Gibbs' inequality applied to the joint distribution against the product of its marginals.

```lean
theorem mutualInfo_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    0 ≤ ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))
```

## How the results fit together

```
Gibbs (relEntropy_nonneg)
  ├─ equality case          (relEntropy_eq_zero_iff)
  └─ mutual information ≥ 0  (mutualInfo_nonneg)

klFun_quad_lower ──► Pinsker  (pinsker)

log-sum inequality (log_sum_inequality)
  ├─ deterministic DPI  (relEntropy_pushforward_le)
  ├─ Markov-kernel DPI  (relEntropy_kernel_le)   ⊇  deterministic DPI
  └─ joint convexity    (relEntropy_jointly_convex)
```

## Relation to mathlib

mathlib provides the measure-theoretic Kullback–Leibler divergence (`klDiv`, `klFun`) with a substantial API, but at the time of writing it does not contain Pinsker's inequality (in any form), the log-sum inequality, a total-variation distance between distributions, a quadratic lower bound on `klFun`, or the data-processing inequality for relative entropy (only chain-rule equalities). This library establishes these results in the finite discrete setting.

## Building

```
lake exe cache get   # fetch the prebuilt mathlib cache
lake build
```

The Lean toolchain version is pinned in `lean-toolchain` and managed by [`elan`](https://github.com/leanprover/elan).

## Verification

Each theorem has been checked with `#print axioms` to depend only on Lean's three standard axioms — `propext`, `Classical.choice`, and `Quot.sound` — with no `sorryAx`. There are no incomplete proofs and no assumptions beyond those stated.

## License

Apache 2.0. See [LICENSE](LICENSE).