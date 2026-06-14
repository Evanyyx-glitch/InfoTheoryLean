# InfoTheoryLean

A Lean 4 formalization of the core inequalities of discrete information theory, built on [mathlib](https://github.com/leanprover-community/mathlib4). Every result is machine-checked and `sorry`-free.

Starting from Gibbs' inequality, the library develops the fundamental inequalities governing the **Kullback–Leibler divergence** (relative entropy) of finite distributions — up through **Pinsker's inequality**, the **data-processing inequality**, **joint convexity**, and the **non-negativity of mutual information**. Companion modules develop:

- **Shannon entropy** — entropy bounds, the identities linking entropy, joint and conditional entropy, and mutual information, subadditivity, and **Fano's inequality**;
- **f-divergences** — the abstract divergence `D_f`, its non-negativity, data-processing inequality, and joint convexity, with the **χ²**, **total-variation**, and **squared-Hellinger** divergences as instances of the same machinery;
- **information-theoretic generalization bounds** — Donsker–Varadhan, a **sub-Gaussian decoupling lemma**, **Hoeffding's lemma**, and the **Xu–Raginsky mutual-information bound** on the expected generalization gap;
- **convex duality** — the **variational (Fenchel–Young) representation** of f-divergences as a single master inequality, **strong duality** (the **Donsker–Varadhan formula**), and a derivation of the **data-processing inequality as a corollary of convex duality**.

Author: Yuyang Xiao.

## Setting

For finite distributions `p, q : ι → ℝ` (with `ι` a `Fintype`), the relative entropy is written directly as the sum

```
∑ i, p i * Real.log (p i / q i).
```

The five modules are:

| Module | Contents |
| --- | --- |
| [`InfoTheoryLean/Basic.lean`](InfoTheoryLean/Basic.lean) | relative entropy: Gibbs, Pinsker, the log-sum inequality, DPI, joint convexity, `I ≥ 0` |
| [`InfoTheoryLean/Shannon.lean`](InfoTheoryLean/Shannon.lean) | Shannon entropy `H(p) = − ∑ i, p i * Real.log (p i)` (in nats), and Fano's inequality |
| [`InfoTheoryLean/FDivergence.lean`](InfoTheoryLean/FDivergence.lean) | the abstract f-divergence `D_f` and the χ² / TV / squared-Hellinger instances |
| [`InfoTheoryLean/Generalization.lean`](InfoTheoryLean/Generalization.lean) | sub-Gaussian decoupling, Hoeffding, the Xu–Raginsky generalization bound |
| [`InfoTheoryLean/Duality.lean`](InfoTheoryLean/Duality.lean) | the variational representation, Donsker–Varadhan strong duality, DPI from duality |

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

## Shannon entropy and Fano's inequality

The Shannon module (`InfoTheoryLean/Shannon.lean`) builds on the divergence results above. Entropy, joint and conditional entropy, mutual information, and the binary entropy function are defined as

```lean
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  - ∑ i, p i * Real.log (p i)

noncomputable def jointEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
  - ∑ x, ∑ y, r x y * Real.log (r x y)

noncomputable def mutualInfo {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))

noncomputable def condEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
  jointEntropy r - entropy (fun y => ∑ x, r x y)

noncomputable def binEntropy (p : ℝ) : ℝ :=
  - p * Real.log p - (1 - p) * Real.log (1 - p)
```

### Entropy bounds

Shannon entropy is non-negative, and maximised by the uniform distribution.

```lean
theorem entropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    0 ≤ entropy p

theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card ι)
```

### Entropy, joint entropy, and mutual information

The mutual information decomposes through the joint and conditional entropies, giving the standard chain-rule identities and the two basic monotonicity facts — *conditioning reduces entropy* and *subadditivity*.

```lean
theorem mutualInfo_eq_entropy_add_sub_jointEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r = entropy (fun x => ∑ y, r x y)
                   + entropy (fun y => ∑ x, r x y) - jointEntropy r

theorem mutualInfo_eq_entropy_sub_condEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r = entropy (fun x => ∑ y, r x y) - condEntropy r

theorem condEntropy_le_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    condEntropy r ≤ entropy (fun x => ∑ y, r x y)

theorem jointEntropy_le_entropy_add_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    jointEntropy r ≤ entropy (fun x => ∑ y, r x y) + entropy (fun y => ∑ x, r x y)
```

### Binary entropy and Fano's inequality

The binary entropy function is concave on `[0, 1]`, and conditional entropy is the marginal-weighted average of the entropies of the conditional distributions.

```lean
theorem concaveOn_binEntropy : ConcaveOn ℝ (Set.Icc 0 1) binEntropy

theorem condEntropy_eq_sum_smul_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hs : ∀ y, 0 < ∑ x, r x y) :
    condEntropy r = ∑ y, (∑ x, r x y) * entropy (fun x => r x y / (∑ x', r x' y))
```

The analytic core of Fano's inequality is a single-distribution bound: the entropy of any distribution `q` is controlled by the binary entropy of `1 − q i₀` for a distinguished outcome `i₀`. It drops out of Gibbs' inequality against a maximally-spread reference distribution.

```lean
theorem entropy_le_binEntropy_add {ι : Type*} [Fintype ι] (q : ι → ℝ) (i₀ : ι)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hi₀ : 0 < q i₀)
    (hcard : 2 ≤ Fintype.card ι) :
    entropy q ≤ binEntropy (1 - q i₀)
                + (1 - q i₀) * Real.log ((Fintype.card ι : ℝ) - 1)
```

**Fano's inequality.** For a joint distribution `r` of a value `X` and an estimate `X̂` over a common alphabet `𝒳`, the conditional entropy `H(X ∣ X̂)` is bounded by the binary entropy of the error probability plus an error-weighted log term. Here `1 − ∑ x, r x x` is the error probability `P_e = P(X ≠ X̂)`, and the diagonal `r x x` is the *correct* event. Combining the decomposition, the single-distribution bound applied per outcome, and Jensen's inequality for the concave `binEntropy` yields

```lean
theorem condEntropy_le_binEntropy_add {X : Type*} [Fintype X]
    (r : X → X → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hdiag : ∀ y, 0 < r y y) (hcard : 2 ≤ Fintype.card X) :
    condEntropy r ≤ binEntropy (1 - ∑ x, r x x)
                    + (1 - ∑ x, r x x) * Real.log ((Fintype.card X : ℝ) - 1)
```

## f-divergences

The f-divergence module (`InfoTheoryLean/FDivergence.lean`) abstracts the divergence inequalities. For a generator `f` and finite distributions `P, Q`,

```lean
noncomputable def fDiv {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (P Q : ι → ℝ) : ℝ :=
  ∑ i, Q i * f (P i / Q i)
```

Each KL theorem reappears here as the instance `f(t) = t·log t`, with the abstract `f : ConvexOn ℝ (Set.Ici 0)` playing the role of `Real.log`'s convexity.

**Non-negativity (Jensen).** `D_f(P ‖ Q) ≥ f(1)`; for a divergence generator (`f(1) = 0`) this is `D_f ≥ 0`. Generalizes Gibbs' inequality.

```lean
theorem fDiv_nonneg {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    f 1 ≤ fDiv f P Q
```

**Generalized log-sum inequality** and the **f-divergence data-processing inequality** (DPI for an arbitrary convex generator; the relative-entropy DPI is the `t·log t` instance):

```lean
theorem fDiv_log_sum_ineq {ι : Type*} (s : Finset ι) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, b i) * f ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, b i * f (a i / b i)

theorem fDiv_kernel_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (K : ι → κ → ℝ) (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv f (fun j => ∑ i, P i * K i j) (fun j => ∑ i, Q i * K i j) ≤ fDiv f P Q
```

**Joint convexity** of `D_f` in `(P, Q)`, and the **bridge** identifying the `t·log t` divergence with relative entropy:

```lean
theorem fDiv_jointly_convex {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (P₁ Q₁ P₂ Q₂ : ι → ℝ)
    (hP₁ : ∀ i, 0 ≤ P₁ i) (hQ₁ : ∀ i, 0 < Q₁ i)
    (hP₂ : ∀ i, 0 ≤ P₂ i) (hQ₂ : ∀ i, 0 < Q₂ i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fDiv f (fun i => lam * P₁ i + (1 - lam) * P₂ i) (fun i => lam * Q₁ i + (1 - lam) * Q₂ i)
      ≤ lam * fDiv f P₁ Q₁ + (1 - lam) * fDiv f P₂ Q₂

theorem fDiv_mul_log_eq_relEntropy {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => t * Real.log t) P Q = ∑ i, P i * Real.log (P i / Q i)
```

### The classical trio

The **χ²**, **total-variation**, and **squared-Hellinger** divergences each reduce to their closed forms and inherit non-negativity from `fDiv_nonneg`.

```lean
-- Pearson χ²,  f(t) = (t − 1)²
theorem chiSq_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (t - 1) ^ 2) P Q = ∑ i, (P i - Q i) ^ 2 / Q i

-- Total variation,  f(t) = |t − 1|
theorem convexOn_tvFun : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => |t - 1|)

theorem tv_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => |t - 1|) P Q = ∑ i, |P i - Q i|

theorem tv_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, |P i - Q i|

-- Squared Hellinger,  f(t) = (√t − 1)²
theorem convexOn_hellingerFun : ConvexOn ℝ (Set.Ici 0) (fun t => (Real.sqrt t - 1) ^ 2)

theorem hellinger_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (Real.sqrt t - 1) ^ 2) P Q = ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2

theorem hellinger_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2
```

## Information-theoretic generalization bounds

The generalization module (`InfoTheoryLean/Generalization.lean`) builds the **Xu–Raginsky** bound on the expected generalization gap in terms of the mutual information between a training sample and the learned hypothesis.

**Donsker–Varadhan (easy direction).** Change of measure against an exponentially tilted reference:

```lean
theorem donsker_varadhan_le {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (g : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i)) ≤ ∑ i, Q i * Real.log (Q i / P i)
```

**Sub-Gaussian decoupling.** For a `σ`-sub-Gaussian `X` (under `P`), the change in mean from `P` to `Q` is controlled by the KL divergence — the heart of the chapter:

```lean
theorem subgaussian_decouple {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (X : ι → ℝ) (σ : ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1)
    (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ, Real.log (∑ i, P i * Real.exp (lam * X i))
              ≤ lam * (∑ i, P i * X i) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ i, Q i * X i) - (∑ i, P i * X i)
      ≤ Real.sqrt (2 * σ ^ 2 * (∑ i, Q i * Real.log (Q i / P i)))
```

**Hoeffding's lemma** (bounded ⟹ sub-Gaussian), via the scalar inequality at its core:

```lean
theorem hoeffding_scalar (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    Real.log (1 - p + p * Real.exp h) - p * h ≤ h ^ 2 / 8

theorem hoeffding_mgf {ι : Type*} [Fintype ι] (P : ι → ℝ) (X : ι → ℝ) (a b : ℝ)
    (hP : ∀ i, 0 < P i) (hP1 : ∑ i, P i = 1)
    (hab : a < b) (hXa : ∀ i, a ≤ X i) (hXb : ∀ i, X i ≤ b) (lam : ℝ) :
    Real.log (∑ i, P i * Real.exp (lam * X i))
      ≤ lam * (∑ i, P i * X i) + lam ^ 2 * (b - a) ^ 2 / 8
```

**The Xu–Raginsky generalization bound.** For a joint distribution `J` of sample `Z` and hypothesis `W`, the gap between the loss under the true coupling and under the product of marginals is bounded by the mutual information `I(Z; W)`:

```lean
theorem mutualInfo_generalization_bound {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (σ : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1) (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ,
        Real.log (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * Real.exp (lam * X z w))
          ≤ lam * (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt (2 * σ ^ 2 * mutualInfo J)
```

For a bounded loss `X ∈ [c, d]` the sub-Gaussian hypothesis is discharged by Hoeffding (`σ = (d − c)/2`), giving the named bound with an explicit constant and *no analytic hypotheses*:

```lean
theorem mutualInfo_generalization_bound_bounded {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (c d : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1)
    (hcd : c < d) (hXc : ∀ z w, c ≤ X z w) (hXd : ∀ z w, X z w ≤ d) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt ((d - c) ^ 2 / 2 * mutualInfo J)
```

## Convex duality

The duality module (`InfoTheoryLean/Duality.lean`) develops the **variational (Fenchel–Young) representation** of f-divergences as a single *master inequality*, from which Donsker–Varadhan, the generalization-bound tower, and the data-processing inequality all descend.

To avoid the convex conjugate as a supremum, a generator and its conjugate are supplied as a **Fenchel–Young pair** `(f, fStar)` via the hypothesis `t·s ≤ f t + fStar s` — exactly the property the proof uses (an equality when `fStar` is the exact conjugate).

**The master inequality** — the variational lower bound (weak duality):

```lean
theorem fDiv_variational {ι : Type*} [Fintype ι] (f fStar : ℝ → ℝ) (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hYoung : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, t * s ≤ f t + fStar s) :
    (∑ i, P i * g i) - (∑ i, Q i * fStar (g i)) ≤ fDiv f P Q
```

**The Gibbs variational principle** — its `KL` member, via the conjugate pair `(t·log t, e^{s−1})`:

```lean
theorem young_kl (t : ℝ) (ht : 0 ≤ t) (s : ℝ) :
    t * s ≤ t * Real.log t + Real.exp (s - 1)

theorem relEntropy_variational {ι : Type*} [Fintype ι] (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    (∑ i, P i * g i) - (∑ i, Q i * Real.exp (g i - 1)) ≤ ∑ i, P i * Real.log (P i / Q i)
```

**Donsker–Varadhan strong duality.** Donsker–Varadhan's `≤` direction is *derived from the master inequality* (so the whole generalization tower descends from it); it is then shown tight at the optimiser `g* = log(Q/P)`; and the two are packaged as: `D(Q ‖ P)` is the **greatest value** of the Donsker–Varadhan functional.

```lean
theorem donsker_varadhan_le_of_variational {ι : Type*} [Fintype ι] (P Q g : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i)) ≤ ∑ i, Q i * Real.log (Q i / P i)

theorem donsker_varadhan_eq {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * Real.log (Q i / P i))
      - Real.log (∑ i, P i * Real.exp (Real.log (Q i / P i)))
    = ∑ i, Q i * Real.log (Q i / P i)

theorem donsker_varadhan {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hQ1 : ∑ i, Q i = 1) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i))}
               (∑ i, Q i * Real.log (Q i / P i))
```

**Strong duality for all f-divergences.** With the conjugate-at-the-derivative identity `fStar (f' t) = t · f' t − f t` (the Fenchel–Young equality at the optimiser, supplied abstractly), the variational representation is tight at `g* = f'(P/Q)`, and `D_f(P ‖ Q)` is the greatest value of the general functional. Donsker–Varadhan is the `f = t·log t` instance.

```lean
theorem fDiv_variational_eq {ι : Type*} [Fintype ι] (f fStar f' : ℝ → ℝ) (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t) :
    (∑ i, P i * f' (P i / Q i)) - (∑ i, Q i * fStar (f' (P i / Q i))) = fDiv f P Q

theorem fDiv_variational_isGreatest {ι : Type*} [Fintype ι] (f fStar f' : ℝ → ℝ) (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hYoung : ∀ t, 0 ≤ t → ∀ s, t * s ≤ f t + fStar s)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, P i * g i) - (∑ i, Q i * fStar (g i))}
      (fDiv f P Q)
```

**The data-processing inequality as a corollary of duality.** Pulling an output test function back through the kernel and applying Jensen to `fStar`, the f-divergence DPI follows from the variational representation — the deepest unification in the development.

```lean
theorem fDiv_kernel_le_of_variational {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳]
    (f fStar f' : ℝ → ℝ) (P Q : 𝒳 → ℝ) (K : 𝒳 → 𝒴 → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x)
    (hK : ∀ x y, 0 < K x y) (hKrow : ∀ x, ∑ y, K x y = 1)
    (hYoung : ∀ t, 0 ≤ t → ∀ s, t * s ≤ f t + fStar s)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t)
    (hfStar_cvx : ConvexOn ℝ Set.univ fStar) :
    fDiv f (fun y => ∑ x, P x * K x y) (fun y => ∑ x, Q x * K x y) ≤ fDiv f P Q
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

Shannon entropy
  ├─ H ≥ 0,  H ≤ log card        (entropy_nonneg, entropy_le_log_card)
  ├─ I = H(X) + H(Y) − H(X,Y)    (mutualInfo_eq_entropy_add_sub_jointEntropy)
  └─ I = H(X) − H(X|Y)           (mutualInfo_eq_entropy_sub_condEntropy)
        ├─ H(X|Y) ≤ H(X)         (condEntropy_le_entropy)
        └─ H(X,Y) ≤ H(X) + H(Y)  (jointEntropy_le_entropy_add_entropy)

Fano's inequality (condEntropy_le_binEntropy_add)
  ├─ relEntropy_nonneg ──► single-distribution bound (entropy_le_binEntropy_add)
  ├─ conditional-entropy decomposition (condEntropy_eq_sum_smul_entropy)
  └─ binEntropy concave (concaveOn_binEntropy) ──► Jensen

f-divergence  D_f (fDiv)
  ├─ D_f ≥ f(1)             (fDiv_nonneg)        ⊇  Gibbs
  ├─ generalized log-sum    (fDiv_log_sum_ineq)
  ├─ f-divergence DPI       (fDiv_kernel_le)     ⊇  relEntropy_kernel_le
  ├─ joint convexity        (fDiv_jointly_convex)
  ├─ KL bridge              (fDiv_mul_log_eq_relEntropy)
  └─ χ² / TV / Hellinger    (chiSq_*, tv_*, hellinger_*)

Generalization
  donsker_varadhan_le ──► subgaussian_decouple ──► mutualInfo_generalization_bound  (Xu–Raginsky)
        ▲                         ▲                         └─ bounded-loss corollary
        │                  amgm_opt_le                          (…_bounded)
  hoeffding_scalar ──► hoeffding_mgf ──────────────────────────┘  (discharges sub-Gaussianity)

Convex duality
  fDiv_variational  (master inequality / weak duality)
  ├─ relEntropy_variational         (Gibbs variational principle, KL member)
  ├─ donsker_varadhan_le_of_variational ──► donsker_varadhan  (strong duality, IsGreatest)
  ├─ fDiv_variational_eq ──► fDiv_variational_isGreatest      (strong duality, all f)
  └─ fDiv_kernel_le_of_variational  (DPI as a corollary of duality)
```

## Relation to mathlib

mathlib provides the measure-theoretic Kullback–Leibler divergence (`klDiv`, `klFun`) with a substantial API, and a binary entropy function, but at the time of writing it does not contain Pinsker's inequality (in any form), the log-sum inequality, a total-variation distance between distributions, a quadratic lower bound on `klFun`, the data-processing inequality for relative entropy (only chain-rule equalities), **Fano's inequality**, the general **f-divergence** with its DPI and joint convexity, the **Xu–Raginsky** generalization bound, or the **variational / Donsker–Varadhan** representation of f-divergences. This library establishes these results — together with a self-contained discrete Shannon-entropy development — in the finite discrete setting.

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