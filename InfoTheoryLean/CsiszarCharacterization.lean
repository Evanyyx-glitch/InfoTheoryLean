/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import InfoTheoryLean.FDivergence

/-!
# Csiszár's characterization of `f`-divergences: framework and the easy direction

Csiszár's theorem characterizes the `f`-divergences as exactly the divergence functionals that are
**information-monotone**: pushing a pair of distributions `(P, Q)` through any stochastic (Markov)
kernel cannot increase the divergence. This file lays the framework — the
information-monotonicity predicate `InfoMonotone`, a divergence functional polymorphic over all
finite alphabets (mirroring the polymorphic `H` of `InfoTheoryLean.EntropyUniqueness`) — and proves
the *easy direction* (`⟸`): every `f`-divergence with convex generator is information-monotone.

The easy direction is exactly the stochastic-kernel data-processing inequality
`fDiv_kernel_le` of `InfoTheoryLean.FDivergence`, repackaged so that the bare divergence functional
`fun P Q => fDiv f P Q` is exhibited as a witness of `InfoMonotone`. The hard direction (`⟹`) — that
information monotonicity forces the divergence to be an `f`-divergence — is left to a later rung.
-/

/-- **Information monotonicity** of a divergence functional `D` (polymorphic over finite alphabets):
for every stochastic kernel `K` (`K i j ≥ 0`, rows summing to `1`), pushing `P` and a strictly
positive `Q` through `K` cannot increase `D`. This is the data-processing inequality stated as a
property of the abstract functional `D`, and is the load-bearing center of Csiszár's
characterization. -/
def InfoMonotone (D : {ι : Type} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (K : ι → κ → ℝ),
    (∀ i j, 0 ≤ K i j) → (∀ i, ∑ j, K i j = 1) →
    ∀ (P Q : ι → ℝ), (∀ i, 0 ≤ P i) → (∀ i, 0 < Q i) →
      D (fun j => ∑ i, P i * K i j) (fun j => ∑ i, Q i * K i j) ≤ D P Q

/-- **Easy direction of Csiszár's characterization** (`⟸`): every `f`-divergence with convex
generator `f` is information-monotone. This is a thin wrapper around the stochastic-kernel
data-processing inequality `fDiv_kernel_le`. -/
theorem fDiv_infoMonotone (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) :
    InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => fDiv f P Q) := by
  intro ι κ _ _ K hK0 hK1 P Q hP hQ
  exact fDiv_kernel_le f hf K hK0 hK1 P Q hP hQ

#print axioms fDiv_infoMonotone

/-!
## The functional equation forced by information monotonicity

The heart of the hard direction (`⟹`) of Csiszár's characterization. A divergence is
**decomposable** if it is a coordinatewise sum `∑ i, d (P i) (Q i)` of a two-variable generator `d`.
For such a divergence, information monotonicity alone forces `d` to satisfy the additive functional
equation

  `d (p₁ + p₂) (q₁ + q₂) = d p₁ q₁ + d p₂ q₂`   whenever `p₁ / q₁ = p₂ / q₂`,

the *aggregation* identity that (together with continuity, in later rungs) pins `d p q` down to the
`q · f (p / q)` shape of an `f`-divergence. The proof uses *nothing* but information monotonicity,
applied to two tiny deterministic/stochastic kernels — no continuity, normalization, or
sum-to-one. -/

/-- A **decomposable divergence**: the coordinatewise sum `∑ i, d (P i) (Q i)` of a two-variable
generator `d`, polymorphic over all finite alphabets. The `f`-divergences are the special case
`d p q = q · f (p / q)`. -/
def decompDiv (d : ℝ → ℝ → ℝ) {ι : Type} [Fintype ι] (P Q : ι → ℝ) : ℝ :=
  ∑ i, d (P i) (Q i)

/-- **The functional equation forced by information monotonicity.** If the decomposable divergence
built from `d` is information-monotone, then for positive `p₁, q₁, p₂, q₂` with equal ratios
(`p₁ / q₁ = p₂ / q₂`, expressed as `p₁ · q₂ = p₂ · q₁`) the generator obeys the additive
aggregation law `d (p₁ + p₂) (q₁ + q₂) = d p₁ q₁ + d p₂ q₂`.

The two bounds come from two instances of `hmono`:
* **`≤` (merge):** the all-ones kernel `Fin 2 → Fin 1` collapses `(p₁,q₁), (p₂,q₂)` into their sum;
  data processing gives `d (p₁+p₂) (q₁+q₂) ≤ d p₁ q₁ + d p₂ q₂`.
* **`≥` (split):** the kernel `Fin 1 → Fin 2` with row `(p₁/(p₁+p₂), p₂/(p₁+p₂))` splits the merged
  pair back apart; the equal-ratio hypothesis is exactly what makes this split send `(p₁+p₂, q₁+q₂)`
  *losslessly* to `(p₁, q₁)` and `(p₂, q₂)`, so data processing gives the reverse inequality. -/
theorem decompDiv_funeq (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (p₁ q₁ p₂ q₂ : ℝ) (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₂ : 0 < p₂) (hq₂ : 0 < q₂)
    (hratio : p₁ * q₂ = p₂ * q₁) :
    d (p₁ + p₂) (q₁ + q₂) = d p₁ q₁ + d p₂ q₂ := by
  have hspos : (0 : ℝ) < p₁ + p₂ := by linarith
  have hsne : p₁ + p₂ ≠ 0 := hspos.ne'
  -- Instance 1: the all-ones kernel `Fin 2 → Fin 1` merges the two states. (≤)
  have key1 := hmono (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))
    (by intro i j; norm_num)
    (by intro i; simp)
    ![p₁, p₂] ![q₁, q₂]
    (by
      rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hp₁.le, hp₂.le⟩)
    (by
      rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hq₁, hq₂⟩)
  simp only [decompDiv, Fin.sum_univ_one, Fin.sum_univ_two, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one] at key1
  -- Instance 2: the splitting kernel `Fin 1 → Fin 2` with row `(p₁/(p₁+p₂), p₂/(p₁+p₂))`. (≥)
  have key2 := hmono
    (fun (_ : Fin 1) (j : Fin 2) => (![p₁ / (p₁ + p₂), p₂ / (p₁ + p₂)] : Fin 2 → ℝ) j)
    (by
      intro i
      rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨div_nonneg hp₁.le hspos.le, div_nonneg hp₂.le hspos.le⟩)
    (by
      intro i
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← add_div, div_self hsne])
    ![p₁ + p₂] ![q₁ + q₂]
    (by intro i; simp only [Matrix.cons_val_fin_one]; linarith)
    (by intro i; simp only [Matrix.cons_val_fin_one]; linarith)
  simp only [decompDiv, Fin.sum_univ_one, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at key2
  -- The split is lossless: each pushforward coordinate recovers the original `(pₖ, qₖ)`.
  have e1 : (p₁ + p₂) * (p₁ / (p₁ + p₂)) = p₁ := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hsne]
  have e2 : (p₁ + p₂) * (p₂ / (p₁ + p₂)) = p₂ := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hsne]
  have e3 : (q₁ + q₂) * (p₁ / (p₁ + p₂)) = q₁ := by
    rw [← mul_div_assoc, div_eq_iff hsne]; linear_combination hratio
  have e4 : (q₁ + q₂) * (p₂ / (p₁ + p₂)) = q₂ := by
    rw [← mul_div_assoc, div_eq_iff hsne]; linear_combination -hratio
  rw [e1, e3, e2, e4] at key2
  exact le_antisymm key1 key2

#print axioms decompDiv_funeq

/-!
## From the functional equation to the `f`-divergence ratio form

The functional equation `decompDiv_funeq` is the seed of *homogeneity*: a decomposable,
information-monotone divergence whose generator is (suitably regular) continuous must satisfy
`d (lam · a) (lam · b) = lam · d a b` for every scaling `lam > 0`. Specialising at `lam = q`,
`(a, b) = (p/q, 1)` collapses this to the local `f`-divergence form

  `d p q = q · f (p / q)`,   with `f := fun r => d r 1`.

The route is the classical Cauchy-style ladder — integer → rational → real homogeneity — where the
final real step is the only place continuity enters (rationals are dense, so a continuous function
agreeing with the linear map `lam ↦ lam · d a b` on positive rationals agrees everywhere). A
regularity hypothesis on `d` is genuinely necessary: without it pathological additive solutions
exist. -/

/-- **Decomposable, information-monotone, continuous divergences have the `f`-divergence ratio
form.** With `f := fun r => d r 1` as generator, `d p q = q · f (p / q)` for all `p, q > 0`. -/
theorem decompDiv_ratio_form (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    d p q = q * d (p / q) 1 := by
  -- Step 1: integer homogeneity `d (n·a) (n·b) = n · d a b`, by induction via `decompDiv_funeq`.
  have step1 : ∀ (n : ℕ), 1 ≤ n → ∀ (a b : ℝ), 0 < a → 0 < b →
      d ((n : ℝ) * a) ((n : ℝ) * b) = (n : ℝ) * d a b := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro a b _ _; simp
    | succ k hk ih =>
      intro a b ha hb
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := hk
        exact_mod_cast this
      have hka : 0 < (k : ℝ) * a := mul_pos hkpos ha
      have hkb : 0 < (k : ℝ) * b := mul_pos hkpos hb
      have hr : ((k : ℝ) * a) * b = a * ((k : ℝ) * b) := by ring
      have hfe := decompDiv_funeq d hmono ((k : ℝ) * a) ((k : ℝ) * b) a b hka hkb ha hb hr
      have ihab := ih a b ha hb
      push_cast
      rw [show ((k : ℝ) + 1) * a = (k : ℝ) * a + a from by ring,
          show ((k : ℝ) + 1) * b = (k : ℝ) * b + b from by ring, hfe, ihab]
      ring
  -- Step 2: rational homogeneity `d ((m/n)·a) ((m/n)·b) = (m/n) · d a b`, from Step 1 twice.
  have step2 : ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (a b : ℝ), 0 < a → 0 < b →
      d (((m : ℝ) / (n : ℝ)) * a) (((m : ℝ) / (n : ℝ)) * b)
        = ((m : ℝ) / (n : ℝ)) * d a b := by
    intro m n hm hn a b ha hb
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := hnR.ne'
    set x : ℝ := a / (n : ℝ) with hx
    set y : ℝ := b / (n : ℝ) with hy
    have hxpos : 0 < x := by rw [hx]; exact div_pos ha hnR
    have hypos : 0 < y := by rw [hy]; exact div_pos hb hnR
    have hnx : (n : ℝ) * x = a := by rw [hx, ← mul_div_assoc, mul_div_cancel_left₀ _ hnne]
    have hny : (n : ℝ) * y = b := by rw [hy, ← mul_div_assoc, mul_div_cancel_left₀ _ hnne]
    have hab : d a b = (n : ℝ) * d x y := by
      have h := step1 n hn x y hxpos hypos
      rw [hnx, hny] at h
      exact h
    have hxy : d x y = d a b / (n : ℝ) := by rw [hab, mul_div_cancel_left₀ _ hnne]
    have hmx : (m : ℝ) * x = ((m : ℝ) / (n : ℝ)) * a := by rw [hx]; ring
    have hmy : (m : ℝ) * y = ((m : ℝ) / (n : ℝ)) * b := by rw [hy]; ring
    have hstep := step1 m hm x y hxpos hypos
    rw [hmx, hmy] at hstep
    rw [hstep, hxy]
    ring
  -- Step 2′: package as homogeneity over positive rationals (feeds Step 3's density argument).
  have step2q : ∀ (s : ℚ), 0 < s → ∀ (a b : ℝ), 0 < a → 0 < b →
      d ((s : ℝ) * a) ((s : ℝ) * b) = (s : ℝ) * d a b := by
    intro s hs a b ha hb
    have hnum : 0 < s.num := Rat.num_pos.mpr hs
    have hnumcast : ((s.num.toNat : ℕ) : ℝ) = ((s.num : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    have hsR : (s : ℝ) = ((s.num.toNat : ℕ) : ℝ) / ((s.den : ℕ) : ℝ) := by
      rw [Rat.cast_def, hnumcast]
    rw [hsR]
    exact step2 s.num.toNat s.den (by omega) s.pos a b ha hb
  -- Step 3: real homogeneity, via continuity + density of the positive rationals.
  have step3 : ∀ (a b : ℝ), 0 < a → 0 < b → ∀ (lam : ℝ), 0 < lam →
      d (lam * a) (lam * b) = lam * d a b := by
    intro a b ha hb lam hlam
    have hg : Continuous (fun t : ℝ => d (t * a) (t * b)) := by
      have hpair : Continuous (fun t : ℝ => ((t * a, t * b) : ℝ × ℝ)) := by fun_prop
      exact hcont.comp hpair
    have hh : Continuous (fun t : ℝ => t * d a b) := by fun_prop
    have hEq : Set.EqOn (fun t : ℝ => d (t * a) (t * b)) (fun t : ℝ => t * d a b)
        {x : ℝ | ∃ r : ℚ, 0 < r ∧ (r : ℝ) = x} := by
      intro x hx
      obtain ⟨r, hrpos, rfl⟩ := hx
      exact step2q r hrpos a b ha hb
    have hmem : lam ∈ closure {x : ℝ | ∃ r : ℚ, 0 < r ∧ (r : ℝ) = x} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hc : max (lam / 2) (lam - ε) < lam := max_lt (by linarith) (by linarith)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hc
      refine ⟨(r : ℝ), ⟨r, ?_, rfl⟩, ?_⟩
      · have hhalf : lam / 2 < (r : ℝ) := lt_of_le_of_lt (le_max_left _ _) hr1
        have hpos : (0 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast hpos
      · rw [Real.dist_eq, abs_sub_lt_iff]
        have hge : lam - ε ≤ max (lam / 2) (lam - ε) := le_max_right _ _
        exact ⟨by linarith, by linarith⟩
    exact hEq.closure hg hh hmem
  -- Step 4: specialise Step 3 at `lam = q`, pair `(p/q, 1)`.
  have hpq : 0 < p / q := div_pos hp hq
  have hmain := step3 (p / q) 1 hpq one_pos q hq
  have hqp : q * (p / q) = p := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hq.ne']
  rw [hqp, mul_one] at hmain
  exact hmain

#print axioms decompDiv_ratio_form

/-!
## Convexity of the generator

The last structural fact: the generator `f := fun r => d r 1` of a decomposable,
information-monotone, continuous divergence is convex on `(0, ∞)`. This is the converse content of
`fDiv_nonneg`'s hypothesis — together with `decompDiv_ratio_form` it shows such a `d` is *exactly*
the `f`-divergence of a convex `f`, completing Csiszár's characterization.

Convexity comes from the **lossy (superadditive) half** of data processing: merging two symbols can
only decrease the divergence, i.e. `d (p₁+p₂) (q₁+q₂) ≤ d p₁ q₁ + d p₂ q₂` *unconditionally* (no
equal-ratio hypothesis — that was only needed for the reverse, split direction). Applied to
`(a·x, a)` and `(b·y, b)` with `a + b = 1`, and rewritten through the ratio form, this is precisely
the two-point convexity inequality `f (a·x + b·y) ≤ a·f x + b·f y`. -/

/-- **Superadditivity (lossy half of data processing).** Merging two symbols cannot increase a
decomposable, information-monotone divergence: `d (p₁+p₂) (q₁+q₂) ≤ d p₁ q₁ + d p₂ q₂`. This is the
all-ones merge kernel `Fin 2 → Fin 1` fed to `hmono` — one instance, no equal-ratio hypothesis. -/
theorem decompDiv_superadditive (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (p₁ q₁ p₂ q₂ : ℝ) (hp₁ : 0 ≤ p₁) (hq₁ : 0 < q₁) (hp₂ : 0 ≤ p₂) (hq₂ : 0 < q₂) :
    d (p₁ + p₂) (q₁ + q₂) ≤ d p₁ q₁ + d p₂ q₂ := by
  have key := hmono (fun (_ : Fin 2) (_ : Fin 1) => (1 : ℝ))
    (by intro i j; norm_num)
    (by intro i; simp)
    ![p₁, p₂] ![q₁, q₂]
    (by
      rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hp₁, hp₂⟩)
    (by
      rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hq₁, hq₂⟩)
  simp only [decompDiv, Fin.sum_univ_one, Fin.sum_univ_two, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one] at key
  exact key

#print axioms decompDiv_superadditive

/-- **The generator is convex.** For a decomposable, information-monotone, continuous divergence,
the generator `f := fun r => d r 1` is convex on `(0, ∞)`. -/
theorem generator_convex (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2)) :
    ConvexOn ℝ (Set.Ioi 0) (fun r => d r 1) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxp : (0 : ℝ) < x := hx
  have hyp : (0 : ℝ) < y := hy
  simp only [smul_eq_mul]
  -- Goal: d (a * x + b * y) 1 ≤ a * d x 1 + b * d y 1.
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- a = 0, so b = 1: equality.
    subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · -- b = 0, so a = 1: equality.
      subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    · -- 0 < a, 0 < b: the superadditive inequality, read through the ratio form.
      have hax : 0 < a * x := mul_pos hapos hxp
      have hby : 0 < b * y := mul_pos hbpos hyp
      have hsuper := decompDiv_superadditive d hmono (a * x) a (b * y) b
        hax.le hapos hby.le hbpos
      rw [hab] at hsuper
      have hax_eq : a * x / a = x := by rw [mul_div_cancel_left₀ _ hapos.ne']
      have hby_eq : b * y / b = y := by rw [mul_div_cancel_left₀ _ hbpos.ne']
      have e1 : d (a * x) a = a * d x 1 := by
        rw [decompDiv_ratio_form d hmono hcont (a * x) a hax hapos, hax_eq]
      have e2 : d (b * y) b = b * d y 1 := by
        rw [decompDiv_ratio_form d hmono hcont (b * y) b hby hbpos, hby_eq]
      rw [e1, e2] at hsuper
      exact hsuper

#print axioms generator_convex

/-!
## Csiszár's characterization (capstone)

Assembling the pieces: a decomposable divergence `∑ i, d (P i) (Q i)` that is information-monotone
and (regularly) continuous *is* an `f`-divergence for a convex generator `f`. The generator is
`f := fun r => d r 1`, convex by `generator_convex` (the lossy half of data processing), and the
identification `d p q = q · f (p / q)` of `decompDiv_ratio_form` (the homogeneity forced by the
functional equation) makes the two sums agree term by term. Together with the easy direction
`fDiv_infoMonotone`, this pins down the `f`-divergences as exactly the information-monotone
decomposable divergences. -/

/-- **Csiszár's characterization.** Every decomposable, information-monotone, continuous divergence
is the `f`-divergence of a convex generator `f` (on strictly positive distributions). -/
theorem csiszar_characterization (d : ℝ → ℝ → ℝ)
    (hmono : InfoMonotone (fun {ι : Type} [Fintype ι] (P Q : ι → ℝ) => decompDiv d P Q))
    (hcont : Continuous (fun x : ℝ × ℝ => d x.1 x.2)) :
    ∃ f : ℝ → ℝ, ConvexOn ℝ (Set.Ioi 0) f ∧
      ∀ {ι : Type} [Fintype ι] (P Q : ι → ℝ), (∀ i, 0 < P i) → (∀ i, 0 < Q i) →
        decompDiv d P Q = fDiv f P Q := by
  refine ⟨fun r => d r 1, generator_convex d hmono hcont, ?_⟩
  intro ι _ P Q hP hQ
  simp only [decompDiv, fDiv]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact decompDiv_ratio_form d hmono hcont (P i) (Q i) (hP i) (hQ i)

#print axioms csiszar_characterization
