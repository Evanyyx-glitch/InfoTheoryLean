# InfoTheoryLean

Machine-checked **discrete information theory** in Lean 4 / Mathlib.

The library develops finite-alphabet information theory from a single analytic seed — Gibbs'
inequality (non-negativity of relative entropy) — out to Shannon entropy, `f`-divergences,
information-theoretic generalization bounds, and the convex-duality (variational) representation of
divergences. On top of that core it proves three **classical foundational theorems**, each
formalized here from its axioms:

* **Shannon entropy uniqueness** (Faddeev / Shannon–Khinchin) — the entropy functional is forced
  to be `C · (−∑ p log p)`;
* **the `f`-divergence characterization** (Csiszár / Amari), both directions — the
  `f`-divergences are exactly the continuous, decomposable, information-monotone divergences;
* **algorithmic information theory** — a concrete universal machine over `Nat.Partrec.Code`, the
  Kolmogorov-complexity **invariance theorem** (a universal machine is additively optimal), and
  the Berry-paradox **uncomputability** of Kolmogorov complexity.

These are formalizations of *known* classical results, not new mathematics. The contribution is the
machine-checked development itself — to our knowledge the first Lean formalizations of entropy
uniqueness, the Csiszár characterization, and a concrete (non-axiomatic) AIT invariance +
uncomputability theorem. See the per-file sections below for exact statements.

> **On the AIT result.** A *synthetic* development of Kolmogorov complexity exists in Coq
> (Forster, Kunze, Lauermann, *Synthetic Kolmogorov Complexity in Coq*, ITP 2022). The development
> here is the first in Lean and is **concrete** — it builds on Mathlib's actual universal partial
> recursive function `Nat.Partrec.Code.eval` rather than postulating a universal function — at the
> cost of using a **unary** program codec. The unary codec gives a crude (linear, not logarithmic)
> invariance constant; it is prefix-free and computable, which is all the invariance theorem needs.
> The logarithmically-short self-delimiting codec is also formalized (`sdEncode`/`sdDecode`) and
> verified, but its two-bit-stride decoder is not bridged to `Primrec` (see the note in
> `Kolmogorov.lean`), so the universal machine is built on the unary codec.

---

## Dependency overview

```
                 Mathlib
                /        \
            Basic        Kolmogorov   (standalone: Nat.Partrec.Code)
           /     \
      Shannon   FDivergence
       /   \         \
Generalization \      Duality
       EntropyUniqueness   CsiszarCharacterization
```

* **`Basic`** — Gibbs' inequality, the analytic seed everything (except `Kolmogorov`) descends from.
* **`Shannon`** ← `Basic`; **`FDivergence`** ← `Basic`.
* **`Generalization`** ← `Shannon`; **`Duality`** ← `FDivergence`.
* **`EntropyUniqueness`** ← `Shannon`; **`CsiszarCharacterization`** ← `FDivergence`.
* **`Kolmogorov`** ← `Mathlib` only (independent of the analytic core).

The root module [`InfoTheoryLean.lean`](InfoTheoryLean.lean) imports all eight files.

---

## Axiom cleanliness

The library is **`sorry`-free**. Every theorem depends only on the three standard Mathlib axioms

```
[propext, Classical.choice, Quot.sound]
```

with **no `sorryAx`** and no `native_decide`. Several results depend on a strict subset (e.g. the
self-delimiting codec round-trip `sdDecode_sdEncode` uses only `[propext, Quot.sound]`, and the
unary round-trip `uDecode_uEncode` only `[propext]`). The end of `Kolmogorov.lean` carries
`#print axioms` checks on its headline theorems; reproduce them as shown below.

---

## Build / verify

```sh
lake exe cache get      # fetch prebuilt Mathlib oleans
lake build              # build the whole library to zero errors / zero sorry
```

To inspect the axiom footprint of any result:

```lean
#print axioms entropy_uniqueness
#print axioms csiszar_characterization
#print axioms invariance
#print axioms K_uncomputable
```

* Lean toolchain: `leanprover/lean4:v4.30.0`
* Mathlib: `leanprover-community/mathlib` rev `v4.30.0`

---

# Contents by file

## `Basic.lean` — Gibbs' inequality and relative-entropy convexity

The analytic foundation: non-negativity of the discrete relative entropy (Kullback–Leibler
divergence) `∑ p log (p/q)` via the termwise bound `log x ≤ x − 1`, its equality case, and the
quantitative refinements built on it — Pinsker's inequality (KL controls total variation), the
log-sum inequality, the data-processing inequalities for pushforwards and Markov kernels, joint
convexity of relative entropy, and non-negativity of mutual information. Every later analytic result
descends from these.

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

## `Shannon.lean` — Shannon entropy and its inequalities

Defines Shannon entropy `H(p) = −∑ p log p` (in nats), joint/conditional entropy, and mutual
information, then proves the standard bounds: non-negativity, the maximum-entropy bound
`H ≤ log |ι|` (uniform attains it, via Gibbs), the chain-rule identities relating mutual information
to joint and conditional entropy, sub-additivity, concavity of the binary entropy, and a Fano-style
bound (`condEntropy_le_binEntropy_add`).

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

noncomputable def condEntropy {X Y : Type*} [Fintype X] [Fintype Y] (r : X → Y → ℝ) : ℝ :=
    jointEntropy r - entropy (fun y => ∑ x, r x y)

theorem mutualInfo_eq_entropy_add_sub_jointEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (r : X → Y → ℝ) (hr : ∀ x y, 0 ≤ r x y)
    (hX : ∀ x, 0 < ∑ y, r x y) (hY : ∀ y, 0 < ∑ x, r x y) :
    mutualInfo r
      = entropy (fun x => ∑ y, r x y) + entropy (fun y => ∑ x, r x y) - jointEntropy r

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

## `FDivergence.lean` — `f`-divergences

Defines the `f`-divergence `D_f(P ‖ Q) = ∑ Q · f(P/Q)` for a convex generator `f` with `f 1 = 0`,
and proves its non-negativity (convex Jensen — directly generalizing Gibbs, the case `f = x log x`),
the `f`-divergence log-sum inequality, the data-processing inequality through Markov kernels, and
joint convexity. It then identifies the classical divergences as instances: KL relative entropy
(`f = x log x`), the χ² divergence, total variation, and the squared Hellinger distance, each with
its closed form and non-negativity.

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

## `Generalization.lean` — information-theoretic generalization bounds

Develops the chain from the Donsker–Varadhan inequality (easy direction) to mutual-information
generalization bounds. From `relEntropy_nonneg` against an exponentially-tilted reference it proves
the Donsker–Varadhan bound; an AM–GM optimization and a sub-gaussian decoupling lemma then yield the
mutual-information generalization bound, with a fully discharged bounded-loss instance via Hoeffding's
lemma (the scalar `log-mgf` bound and its sum form).

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

## `Duality.lean` — convex (variational) duality for divergences

The convex-duality summit. Proves the variational (Fenchel–Young) lower bound for `f`-divergences —
parametrized by a Fenchel–Young pair `(f, f*)` to avoid defining the conjugate as a supremum — and
derives the Donsker–Varadhan / Gibbs variational principle for KL as a special case, including the
sharp `IsGreatest` (attained-supremum) statements. Closes with a variational-form proof of the
divergence data-processing inequality through a kernel.

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

## ★ `EntropyUniqueness.lean` — Shannon entropy uniqueness (Faddeev / Shannon–Khinchin)

**Foundational result.** Proves that any functional `H`, polymorphic over finite alphabets,
satisfying the Shannon–Khinchin / Faddeev axioms — *relabeling invariance* (`hrelabel`), the
*grouping / recursivity* law (`hgroup`), *monotonicity on uniform distributions* (`hmonoU`), and
*continuity* (`hcont`) — must equal `(H(uniform₂)/log 2) · (−∑ p log p)`; with the normalization
`H(uniform₂) = log 2` it is exactly Shannon entropy. Mathlib (`v4.30.0`) has no such
characterization, so the analytic core is proved from scratch: the centerpiece `additive_mono_eq_log`
shows that a monotone function turning multiplication into addition is forced to be a constant
multiple of `log`, by the classical `⌊k log₂ n⌋` squeeze.

```lean
theorem pow_le_pow_of_mul_log_le {a b p q : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : (p : ℝ) * Real.log a ≤ (q : ℝ) * Real.log b) : a ^ p ≤ b ^ q

theorem additive_mono_eq_log (f : ℕ → ℝ)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m + f n)
    (hmono : Monotone f) :
    ∀ n, 1 ≤ n → f n = (f 2 / Real.log 2) * Real.log n

noncomputable def uniformDist (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

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

## ★ `CsiszarCharacterization.lean` — the `f`-divergence characterization (Csiszár / Amari)

**Foundational result.** Characterizes the `f`-divergences as exactly the divergence functionals
that are *information-monotone* (cannot increase under any stochastic/Markov kernel), continuous, and
*decomposable* (`decompDiv d P Q = ∑ d(P i, Q i)`). Both directions are formalized:

* **Easy direction (`⟸`), `fDiv_infoMonotone`** — every `f`-divergence with convex generator is
  information-monotone (the kernel data-processing inequality, repackaged).
* **Hard direction (`⟹`), `csiszar_characterization`** — every continuous decomposable
  information-monotone divergence *is* an `f`-divergence: there exists a convex generator `f` with
  `decompDiv d P Q = fDiv f P Q`. The proof extracts the generator from the diagonal `r ↦ d(r,1)`,
  showing kernel-monotonicity forces homogeneity `d(p,q) = q·d(p/q,1)`, superadditivity, and
  convexity of the generator.

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

## ★ `Kolmogorov.lean` — algorithmic information theory

**Foundational result.** A concrete development of Kolmogorov complexity over Mathlib's universal
partial recursive function `Nat.Partrec.Code.eval`, culminating in the **invariance theorem** (the
universal machine is additively optimal) and the **uncomputability** of Kolmogorov complexity (via
Berry's paradox). Built bottom-up.

**1. Prefix-free self-delimiting codec.** `sdEncode` writes `n` in binary, doubles each bit, and
appends the terminator `[false, true]`; `sdDecode` recovers `(n, rest)` from any concatenation. The
overhead is logarithmic (`≤ 2·Nat.size n + 2`) — the additive constant the invariance theorem wants.

```lean
def fromBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * fromBits bs

theorem fromBits_bits (n : ℕ) : fromBits (Nat.bits n) = n

def double : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: double bs

def sdEncode (n : ℕ) : List Bool := double (Nat.bits n) ++ [false, true]

def sdDecodeBits : List Bool → Option (List Bool × List Bool)
  | false :: true  :: rest => some ([], rest)
  | false :: false :: rest => (sdDecodeBits rest).map fun p => (false :: p.1, p.2)
  | true  :: true  :: rest => (sdDecodeBits rest).map fun p => (true :: p.1, p.2)
  | _ => none

def sdDecode (l : List Bool) : Option (ℕ × List Bool) :=
  (sdDecodeBits l).map fun p => (fromBits p.1, p.2)

theorem sdDecode_sdEncode (n : ℕ) (rest : List Bool) :
    sdDecode (sdEncode n ++ rest) = some (n, rest)

theorem sdEncode_length_eq (n : ℕ) : (sdEncode n).length = 2 * Nat.size n + 2

theorem sdEncode_length_le (n : ℕ) : (sdEncode n).length ≤ 2 * Nat.size n + 2
```

**2. Computability layer.** `fromBits`, `double`, `Nat.bits`, and `sdEncode` are shown primitive
recursive / computable (`Nat.bits` via a `nat_iterate` fuel recast). The self-delimiting decoder's
two-bit-stride recursion does not fit Mathlib's single-step `Primrec.list_rec`, so it is **not**
bridged to `Primrec` (documented in-file); the universal machine therefore uses the unary codec below.

```lean
theorem computable_fromBits : Computable fromBits
theorem computable_double : Computable double
theorem primrec_natBits : Primrec Nat.bits
theorem computable_natBits : Computable Nat.bits
theorem computable_sdEncode : Computable sdEncode
```

**3. Unary fallback codec** (computable both ways). `uEncode n = trueⁿ ++ [false]`; the decoder
counts the leading `true`s. Crude (linear length) but prefix-free and computable by single-step
structural recursion — sufficient for invariance.

```lean
def uEncode (n : ℕ) : List Bool := List.replicate n true ++ [false]

def uDecode : List Bool → ℕ × List Bool
  | [] => (0, [])
  | true :: l => ((uDecode l).1 + 1, (uDecode l).2)
  | false :: l => (0, l)

theorem uDecode_uEncode (n : ℕ) (p : List Bool) : uDecode (uEncode n ++ p) = (n, p)

theorem computable_uEncode : Computable uEncode
theorem computable_uDecode : Computable uDecode
```

**4. Universal machine.** `phiE e` runs the code decoded from `e` on the encoded input; `U` decodes
its input via the unary codec into an index/program pair and runs `phiE`. `U` is partial recursive
(via Mathlib's universality `Nat.Partrec.Code.eval_part`), and `phiE` enumerates *all* partial
recursive functions on bit strings (`phiE_complete`, from `Nat.Partrec.Code.exists_code`).

```lean
noncomputable def phiE (e : ℕ) : List Bool →. ℕ :=
  fun p => eval (Denumerable.ofNat Code e) (Encodable.encode p)

noncomputable def U : List Bool →. ℕ :=
  fun w => phiE (uDecode w).1 (uDecode w).2

theorem U_partrec : Partrec U

theorem phiE_complete (φ : List Bool →. ℕ) (hφ : Partrec φ) :
    ∃ e, ∀ p, φ p = phiE e p
```

**5. Kolmogorov complexity and the invariance theorem.** `C φ x` is the shortest program length
making `φ` output `x` (in `ℕ∞`, `⊤` if undescribable). The invariance theorem: the universal machine
`U` is optimal up to an additive constant depending on `φ` but not on `x`.

```lean
noncomputable def C (φ : List Bool →. ℕ) (x : ℕ) : ℕ∞ :=
  sInf ((fun p => (p.length : ℕ∞)) '' {p : List Bool | x ∈ φ p})

theorem invariance (φ : List Bool →. ℕ) (hφ : Partrec φ) :
    ∃ c : ℕ, ∀ x, C U x ≤ C φ x + (c : ℕ∞)
```

**6. Unboundedness and uncomputability.** Only finitely many strings have short programs, so
complexity is unbounded (`C_unbounded`, the counting lemma); and if `C U` were computable a
Berry-style selector would name a high-complexity string with a short program — so `C U` is not
computable (`K_uncomputable`).

```lean
theorem C_unbounded (n : ℕ) : ∃ x : ℕ, (n : ℕ∞) ≤ C U x

theorem K_uncomputable :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∀ x, (g x : ℕ∞) = C U x
```

---

*Formalizations of known classical results. Lean 4 / Mathlib `v4.30.0`.*
