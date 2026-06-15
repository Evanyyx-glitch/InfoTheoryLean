# InfoTheoryLean

A machine-checked development of discrete (finite-alphabet) information theory in
[Lean 4](https://leanprover.github.io/) on top of [Mathlib](https://github.com/leanprover-community/mathlib4).

The library has two parts:

1. **A tower of core inequalities** for discrete relative entropy (Kullback–Leibler divergence),
   Shannon entropy, `f`-divergences, and convex duality — Gibbs' inequality, Pinsker's inequality,
   the data-processing inequality, joint convexity, Fano's inequality, the variational
   (Donsker–Varadhan / Fenchel–Young) representations, and an information-theoretic generalization
   bound.

2. **Two classical characterization theorems, each proved from its axioms:**
   * the **Shannon–Khinchin uniqueness of entropy** — the only functional satisfying relabelling
     invariance, the grouping/chain rule, monotonicity along the uniform distributions, and
     continuity is (a constant multiple of) Shannon entropy; and
   * the **Csiszár characterization of `f`-divergences** — the decomposable divergences that are
     monotone under stochastic kernels (data processing) are exactly the `f`-divergences of a convex
     generator.

These are formalizations of **known classical results**, not new mathematics. The contribution is
the formalization itself: as far as we are aware, the entropy-uniqueness theorem and the Csiszár
characterization are not currently in Mathlib, and are formalized here from scratch.

## Axiom cleanliness

Every theorem in the library is checked with `#print axioms` (the `#print axioms ...` lines are kept
inline in the sources). Each depends only on the three standard Lean/Mathlib foundational axioms

```
[propext, Classical.choice, Quot.sound]
```

with **no `sorryAx`** — i.e. there are no `sorry`s, no unproved lemmas, and no extra axioms anywhere
in the development.

## Building and verifying

```sh
lake exe cache get      # fetch the prebuilt Mathlib cache
lake build              # build and check the whole library
```

A successful `lake build` is a complete proof check. To re-confirm the axiom guarantee for any
result, inspect the `#print axioms` output emitted during the build, or add e.g.

```lean
#print axioms csiszar_characterization
```

## Module layout and dependencies

```
Mathlib
  └─ Basic
       ├─ Shannon
       │    ├─ Generalization
       │    └─ EntropyUniqueness
       └─ FDivergence
            ├─ Duality
            └─ CsiszarCharacterization
```

* **Basic** — relative entropy: Gibbs, Pinsker, log-sum, data processing, joint convexity, mutual
  information.
* **Shannon** — Shannon entropy, mutual information / chain rule, conditional entropy, Fano.
* **FDivergence** — `f`-divergences: non-negativity, data processing, joint convexity, and the KL /
  χ² / total-variation / Hellinger instances.
* **Duality** — variational (Fenchel–Young) representations; Donsker–Varadhan; DPI from duality.
* **Generalization** — Donsker–Varadhan (easy direction), Hoeffding, and the mutual-information
  generalization bound.
* **EntropyUniqueness** — the Shannon–Khinchin uniqueness theorem for entropy.
* **CsiszarCharacterization** — the Csiszár characterization of `f`-divergences.

The root module `InfoTheoryLean.lean` imports all of the above.

---

## `InfoTheoryLean/Basic.lean`

The foundation: discrete relative entropy `D(p ‖ q) = ∑ p i · log (p i / q i)` and its core
inequalities. Establishes Gibbs' inequality and its equality case, an analytically sharp finite
Pinsker inequality (via a tuned quadratic lower bound on `x ↦ x log x + 1 − x`), the log-sum
inequality (finite Jensen for `x ↦ x log x`), the data-processing inequality in both deterministic
and stochastic-kernel forms, joint convexity of relative entropy, and non-negativity of mutual
information. Several private lemmas (the Pinsker slack-function machinery, per-coordinate and
per-output bounds) support these but are not part of the public interface.

```lean
theorem relEntropy_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i)

theorem relEntropy_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    ∑ i, p i * Real.log (p i / q i) = 0 ↔ p = q

lemma klFun_quad_lower (x : ℝ) (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * x + 4) ≤ x * Real.log x + 1 - x

theorem pinsker {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (1 / 2) * (∑ i, |p i - q i|) ^ 2 ≤ ∑ i, p i * Real.log (p i / q i)

theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i)

def pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ] (f : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = j), p i

theorem relEntropy_pushforward_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    ∑ j, pushforward f p j * Real.log (pushforward f p j / pushforward f q j)
      ≤ ∑ i, p i * Real.log (p i / q i)

theorem relEntropy_kernel_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → ℝ) (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    ∑ j, (∑ i, p i * K i j) * Real.log ((∑ i, p i * K i j) / (∑ i, q i * K i j))
      ≤ ∑ i, p i * Real.log (p i / q i)

theorem relEntropy_jointly_convex {ι : Type*} [Fintype ι]
    (p₁ q₁ p₂ q₂ : ι → ℝ)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hq₁ : ∀ i, 0 < q₁ i)
    (hp₂ : ∀ i, 0 ≤ p₂ i) (hq₂ : ∀ i, 0 < q₂ i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (∑ i, (lam * p₁ i + (1 - lam) * p₂ i) *
          Real.log ((lam * p₁ i + (1 - lam) * p₂ i) / (lam * q₁ i + (1 - lam) * q₂ i)))
      ≤ lam * (∑ i, p₁ i * Real.log (p₁ i / q₁ i))
        + (1 - lam) * (∑ i, p₂ i * Real.log (p₂ i / q₂ i))

theorem mutualInfo_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hr1 : ∑ x, ∑ y, r x y = 1)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    0 ≤ ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))
```

---

## `InfoTheoryLean/Shannon.lean`

Shannon entropy `H(p) = −∑ p i · log (p i)`, measured in nats, and the basic entropy theory.
Proves non-negativity and the maximum-entropy bound (entropy `≤ log (card)`, attained at the
uniform distribution, via Gibbs); defines joint entropy, mutual information and conditional entropy
and proves the chain rule `I(X;Y) = H(X) + H(Y) − H(X,Y)`, that conditioning reduces entropy, and
subadditivity. The chapter culminates in Fano's inequality: a core per-distribution bound, the
concavity of the binary entropy function, conditional entropy as the expected entropy of the
conditionals, and the assembled conditional Fano inequality.

```lean
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
    - ∑ i, p i * Real.log (p i)

theorem entropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    0 ≤ entropy p

theorem entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    entropy p ≤ Real.log (Fintype.card ι)

noncomputable def jointEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    - ∑ x, ∑ y, r x y * Real.log (r x y)

noncomputable def mutualInfo {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    ∑ x, ∑ y, r x y * Real.log (r x y / ((∑ y', r x y') * (∑ x', r x' y)))

theorem mutualInfo_eq_entropy_add_sub_jointEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r
      = entropy (fun x => ∑ y, r x y) + entropy (fun y => ∑ x, r x y) - jointEntropy r

noncomputable def condEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    jointEntropy r - entropy (fun y => ∑ x, r x y)

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

noncomputable def binEntropy (p : ℝ) : ℝ := - p * Real.log p - (1 - p) * Real.log (1 - p)

theorem entropy_le_binEntropy_add {ι : Type*} [Fintype ι] (q : ι → ℝ) (i₀ : ι)
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (hi₀ : 0 < q i₀)
    (hcard : 2 ≤ Fintype.card ι) :
    entropy q ≤ binEntropy (1 - q i₀) + (1 - q i₀) * Real.log ((Fintype.card ι : ℝ) - 1)

theorem concaveOn_binEntropy : ConcaveOn ℝ (Set.Icc 0 1) binEntropy

theorem condEntropy_eq_sum_smul_entropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hs : ∀ y, 0 < ∑ x, r x y) :
    condEntropy r = ∑ y, (∑ x, r x y) * entropy (fun x => r x y / (∑ x', r x' y))

theorem condEntropy_le_binEntropy_add {X : Type*} [Fintype X]
    (r : X → X → ℝ) (hr : ∀ x y, 0 ≤ r x y) (hr1 : ∑ x, ∑ y, r x y = 1)
    (hdiag : ∀ y, 0 < r y y) (hcard : 2 ≤ Fintype.card X) :
    condEntropy r ≤ binEntropy (1 - ∑ x, r x x)
                    + (1 - ∑ x, r x x) * Real.log ((Fintype.card X : ℝ) - 1)
```

---

## `InfoTheoryLean/FDivergence.lean`

The `f`-divergence `D_f(P ‖ Q) = ∑ i, Q i · f (P i / Q i)` for a convex generator `f`, generalizing
relative entropy. Proves non-negativity (convex Jensen, generalizing Gibbs), the abstract-`f`
log-sum inequality, the stochastic-kernel data-processing inequality, and joint convexity. It then
recovers four concrete divergences as instances — Kullback–Leibler (`f t = t log t`), Pearson χ²
(`f t = (t−1)²`), total variation (`f t = |t−1|`), and squared Hellinger (`f t = (√t−1)²`) — proving
for each a bridge identity to its closed form and non-negativity as a corollary of `fDiv_nonneg`.

```lean
noncomputable def fDiv {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (P Q : ι → ℝ) : ℝ :=
  ∑ i, Q i * f (P i / Q i)

theorem fDiv_nonneg {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f) (hf1 : f 1 = 0)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ fDiv f P Q

theorem fDiv_log_sum_ineq {ι : Type*} (s : Finset ι) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, b i) * f ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s, b i * f (a i / b i)

theorem fDiv_kernel_le {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (K : ι → κ → ℝ) (hK0 : ∀ i j, 0 ≤ K i j) (hK1 : ∀ i, ∑ j, K i j = 1)
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv f (fun j => ∑ i, P i * K i j) (fun j => ∑ i, Q i * K i j) ≤ fDiv f P Q

theorem fDiv_jointly_convex {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Ici 0) f)
    (P₁ Q₁ P₂ Q₂ : ι → ℝ)
    (hP₁ : ∀ i, 0 ≤ P₁ i) (hQ₁ : ∀ i, 0 < Q₁ i)
    (hP₂ : ∀ i, 0 ≤ P₂ i) (hQ₂ : ∀ i, 0 < Q₂ i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fDiv f (fun i => lam * P₁ i + (1 - lam) * P₂ i) (fun i => lam * Q₁ i + (1 - lam) * Q₂ i)
      ≤ lam * fDiv f P₁ Q₁ + (1 - lam) * fDiv f P₂ Q₂

theorem fDiv_mul_log_eq_relEntropy {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun x => x * Real.log x) P Q = ∑ i, P i * Real.log (P i / Q i)

theorem chiSq_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (t - 1) ^ 2) P Q = ∑ i, (P i - Q i) ^ 2 / Q i

theorem chiSq_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, (P i - Q i) ^ 2 / Q i

theorem convexOn_tvFun : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => |t - 1|)

theorem tv_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => |t - 1|) P Q = ∑ i, |P i - Q i|

theorem tv_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, |P i - Q i|

theorem convexOn_hellingerFun : ConvexOn ℝ (Set.Ici 0) (fun t => (Real.sqrt t - 1) ^ 2)

theorem hellinger_eq_fDiv {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    fDiv (fun t => (Real.sqrt t - 1) ^ 2) P Q
      = ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2

theorem hellinger_nonneg {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i)) ^ 2
```

---

## `InfoTheoryLean/Duality.lean`

Convex duality for `f`-divergences. The master inequality is the variational (Fenchel–Young) lower
bound: for any Fenchel–Young pair `(f, f*)` and test function `g`,
`(∑ P · g) − (∑ Q · f*(g)) ≤ D_f(P ‖ Q)`. From it the chapter derives the Gibbs variational
principle for KL, both halves of the Donsker–Varadhan representation packaged as `IsGreatest`,
the general-`f` strong-duality `IsGreatest` statement (with achievability supplied through the
conjugate-at-the-derivative identity), the KL instance of that, and finally the data-processing
inequality re-derived from the variational representation (via the kernel adjoint and row-wise
Jensen). The two abstract inputs `hYoung` (Fenchel–Young inequality) and `hconj`
(conjugate-at-the-derivative equality) keep the conjugate `f*` parametric, avoiding differentiation
inside Lean.

```lean
theorem fDiv_variational {ι : Type*} [Fintype ι] (f fStar : ℝ → ℝ) (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hYoung : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, t * s ≤ f t + fStar s) :
    (∑ i, P i * g i) - (∑ i, Q i * fStar (g i)) ≤ fDiv f P Q

theorem young_kl (t : ℝ) (ht : 0 ≤ t) (s : ℝ) :
    t * s ≤ t * Real.log t + Real.exp (s - 1)

theorem relEntropy_variational {ι : Type*} [Fintype ι] (P Q g : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i) :
    (∑ i, P i * g i) - (∑ i, Q i * Real.exp (g i - 1)) ≤ ∑ i, P i * Real.log (P i / Q i)

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

theorem relEntropy_variational_isGreatest {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) :
    IsGreatest {x : ℝ | ∃ g : ι → ℝ, x = (∑ i, P i * g i) - (∑ i, Q i * Real.exp (g i - 1))}
               (∑ i, P i * Real.log (P i / Q i))

theorem fDiv_kernel_le_of_variational {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] [Nonempty 𝒳]
    (f fStar f' : ℝ → ℝ) (P Q : 𝒳 → ℝ) (K : 𝒳 → 𝒴 → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 < Q x)
    (hK : ∀ x y, 0 < K x y) (hKrow : ∀ x, ∑ y, K x y = 1)
    (hYoung : ∀ t, 0 ≤ t → ∀ s, t * s ≤ f t + fStar s)
    (hconj : ∀ t, 0 < t → fStar (f' t) = t * f' t - f t)
    (hfStar_cvx : ConvexOn ℝ Set.univ fStar) :
    fDiv f (fun y => ∑ x, P x * K x y) (fun y => ∑ x, Q x * K x y) ≤ fDiv f P Q
```

---

## `InfoTheoryLean/Generalization.lean`

Information-theoretic generalization bounds, built on the easy (one-sided) Donsker–Varadhan
inequality. From the variational bound and an AM–GM optimization lemma it derives a sub-Gaussian
decoupling inequality controlling a change of mean from `P` to `Q` by `√(2σ²·D(Q ‖ P))`. The
sub-Gaussian hypothesis is then discharged by Hoeffding's lemma (proved here from a scalar
convexity core). The headline result is the Xu–Raginsky mutual-information generalization bound,
stated abstractly and then as an end-to-end corollary for bounded loss functions.

```lean
theorem donsker_varadhan_le {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (g : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1) :
    (∑ i, Q i * g i) - Real.log (∑ i, P i * Real.exp (g i)) ≤ ∑ i, Q i * Real.log (Q i / P i)

theorem amgm_opt_le {a c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (h : ∀ lam : ℝ, 0 < lam → a ≤ c / lam + lam * d) :
    a ≤ 2 * Real.sqrt (c * d)

theorem subgaussian_decouple {ι : Type*} [Fintype ι] (P Q : ι → ℝ) (X : ι → ℝ) (σ : ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 ≤ Q i) (hP1 : ∑ i, P i = 1) (hQ1 : ∑ i, Q i = 1)
    (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ, Real.log (∑ i, P i * Real.exp (lam * X i))
              ≤ lam * (∑ i, P i * X i) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ i, Q i * X i) - (∑ i, P i * X i)
      ≤ Real.sqrt (2 * σ ^ 2 * (∑ i, Q i * Real.log (Q i / P i)))

theorem hoeffding_scalar (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    Real.log (1 - p + p * Real.exp h) - p * h ≤ h ^ 2 / 8

theorem hoeffding_mgf {ι : Type*} [Fintype ι] (P : ι → ℝ) (X : ι → ℝ) (a b : ℝ)
    (hP : ∀ i, 0 < P i) (hP1 : ∑ i, P i = 1)
    (hab : a < b) (hXa : ∀ i, a ≤ X i) (hXb : ∀ i, X i ≤ b) (lam : ℝ) :
    Real.log (∑ i, P i * Real.exp (lam * X i))
      ≤ lam * (∑ i, P i * X i) + lam ^ 2 * (b - a) ^ 2 / 8

theorem mutualInfo_generalization_bound {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (σ : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1) (hσ : 0 < σ)
    (hsg : ∀ lam : ℝ,
        Real.log (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * Real.exp (lam * X z w))
          ≤ lam * (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w) + lam ^ 2 * σ ^ 2 / 2) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt (2 * σ ^ 2 * mutualInfo J)

theorem mutualInfo_generalization_bound_bounded {ζ ω : Type*} [Fintype ζ] [Fintype ω]
    (J : ζ → ω → ℝ) (X : ζ → ω → ℝ) (c d : ℝ)
    (hJ : ∀ z w, 0 < J z w) (hJ1 : ∑ z, ∑ w, J z w = 1)
    (hcd : c < d) (hXc : ∀ z w, c ≤ X z w) (hXd : ∀ z w, X z w ≤ d) :
    (∑ z, ∑ w, J z w * X z w) - (∑ z, ∑ w, ((∑ w', J z w') * (∑ z', J z' w)) * X z w)
      ≤ Real.sqrt ((d - c) ^ 2 / 2 * mutualInfo J)
```

---

## `InfoTheoryLean/EntropyUniqueness.lean`

The Shannon–Khinchin uniqueness theorem for entropy, proved from scratch. The analytic heart is a
classical squeeze argument showing the only monotone function `f : ℕ → ℝ` with `f(mn) = f m + f n`
is a constant multiple of the logarithm. This is bootstrapped — through the grouping axiom applied
to products of uniform distributions, and then to variable-block-size sigma types — to force the
value of an axiomatic entropy functional `H` on uniform and then on rational distributions. With
continuity of `H` and a density argument (rational distributions approximating an arbitrary one),
the value is pinned on all finite distributions: `H = (H(uniform₂)/log 2) · entropy`, and, under the
one-bit normalization `H(uniform₂) = log 2`, `H` *is* Shannon entropy. The functional `H` is taken
polymorphically over all finite alphabets, and the Shannon–Khinchin axioms (relabelling invariance,
grouping/chain rule, monotonicity along uniforms, continuity) are supplied as hypotheses.

```lean
theorem pow_le_pow_of_mul_log_le {a b p q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : (p : ℝ) * Real.log a ≤ (q : ℝ) * Real.log b) : a ^ p ≤ b ^ q

theorem additive_mono_eq_log (f : ℕ → ℝ)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m + f n)
    (hmono : Monotone f) :
    ∀ n, 1 ≤ n → f n = (f 2 / Real.log 2) * Real.log n

noncomputable def uniformDist (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

def fiberFstEquiv {α β : Type*} [DecidableEq α] (j : α) : {x : α × β // x.1 = j} ≃ β

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
    ∀ n, 1 ≤ n → H (uniformDist n) = (H (uniformDist 2) / Real.log 2) * Real.log n

def fiberSigmaFstEquiv {n : ℕ} (a : Fin n → ℕ) (j : Fin n) :
    {x : Σ i : Fin n, Fin (a i) // x.fst = j} ≃ Fin (a j)

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
      = (H (uniformDist 2) / Real.log 2) * entropy (fun i => (a i : ℝ) / (∑ j, (a j : ℝ)))

theorem continuous_entropy {ι : Type} [Fintype ι] :
    Continuous (fun p : ι → ℝ => entropy p)

theorem tendsto_floorApprox (x : ℝ) (hx : 0 ≤ x) :
    Filter.Tendsto (fun N : ℕ => ((⌊(N : ℝ) * x⌋₊ : ℝ) + 1) / (N : ℝ)) Filter.atTop (nhds x)

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
    H p = (H (uniformDist 2) / Real.log 2) * entropy p

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
    H p = entropy p
```

---

## `InfoTheoryLean/CsiszarCharacterization.lean`

The Csiszár characterization of `f`-divergences, proved from scratch. A divergence functional is
*information-monotone* if pushing `(P, Q)` through any stochastic kernel cannot increase it (the
data-processing inequality, stated as a property of the functional). The easy direction
(`fDiv_infoMonotone`) shows every `f`-divergence with convex generator is information-monotone — a
thin wrapper around `fDiv_kernel_le`. The hard direction works with *decomposable* divergences
`∑ i, d (P i) (Q i)`: information monotonicity alone forces the generator `d` to satisfy an additive
functional equation under equal ratios (`decompDiv_funeq`, from a merge and a lossless-split
kernel); this functional equation plus continuity forces the homogeneity `d p q = q · d (p/q) 1`
(`decompDiv_ratio_form`, by a Cauchy-style integer → rational → real ladder); and the lossy
(superadditive) half of data processing forces the generator `r ↦ d r 1` to be convex
(`generator_convex`). Assembling these, `csiszar_characterization` exhibits any decomposable,
information-monotone, continuous divergence as the `f`-divergence of a convex generator — the
converse to the easy direction. A regularity (continuity) hypothesis on `d` is genuinely necessary.

```lean
def InfoMonotone (D : {ι : Type} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (K : ι → κ → ℝ),
    (∀ i j, 0 ≤ K i j) → (∀ i, ∑ j, K i j = 1) →
    ∀ (P Q : ι → ℝ), (∀ i, 0 ≤ P i) → (∀ i, 0 < Q i) →
      D (fun j => ∑ i, P i * K i j) (fun j => ∑ i, Q i * K i j) ≤ D P Q

theorem fDiv_infoMonotone (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) :
    InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => fDiv f P Q)

def decompDiv (d : ℝ → ℝ → ℝ) {ι : Type} [Fintype ι] (P Q : ι → ℝ) : ℝ :=
  ∑ i, d (P i) (Q i)

theorem decompDiv_funeq (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (p₁ q₁ p₂ q₂ : ℝ) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂)
    (hratio : p₁ * q₂ = p₂ * q₁) :
    d (p₁ + p₂) (q₁ + q₂) = d p₁ q₁ + d p₂ q₂

theorem decompDiv_ratio_form (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    d p q = q * d (p / q) 1

theorem decompDiv_superadditive (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (p₁ q₁ p₂ q₂ : ℝ) (hp₁ : 0 ≤ p₁) (hq₁ : 0 < q₁) (hp₂ : 0 ≤ p₂) (hq₂ : 0 < q₂) :
    d (p₁ + p₂) (q₁ + q₂) ≤ d p₁ q₁ + d p₂ q₂

theorem generator_convex (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2)) :
    ConvexOn ℝ (Set.Ioi 0) (fun r => d r 1)

theorem csiszar_characterization (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2)) :
    ∃ f : ℝ → ℝ, ConvexOn ℝ (Set.Ioi 0) f ∧
      ∀ {ι : Type} [Fintype ι] (P Q : ι → ℝ), (∀ i, 0 < P i) → (∀ i, 0 < Q i) →
        decompDiv d P Q = fDiv f P Q
```

---

*License: Apache 2.0 (see `LICENSE`). Author: Yuyang Xiao.*
