/-
Copyright (c) 2026 Yuyang Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Xiao
-/
import Mathlib

/-!
# Self-delimiting (prefix-free) codes on bit strings

This file builds the first piece of scaffolding for algorithmic information theory (Kolmogorov
complexity): a *self-delimiting* encoding of natural numbers as bit strings. A universal machine
must be able to read a program `p` that has been concatenated with further data without any
external length marker; this requires the program's encoding to be **prefix-free**, so that the
decoder can tell where the program ends. The price paid for self-delimitation is only a *linear*
blow-up in length, and that linear overhead is exactly what makes the invariance theorem of
Kolmogorov complexity *additive* (the universal machine prepends a program-index of bounded
overhead).

## Construction

We expand `n` in binary, least-significant bit first, via mathlib's `Nat.bits`. Each bit is then
**doubled** (`b ↦ [b, b]`), and the doubled stream is terminated by the pair `[false, true]`:

* a doubled bit is always `[false, false]` or `[true, true]`, **never** `[false, true]`, so the
  terminator is unambiguous;
* the decoder reads two bits at a time, accumulating `b` on `[b, b]` and stopping at
  `[false, true]`.

## Main results

* `sdDecode_sdEncode` — the round-trip / prefix-free property: decoding `sdEncode n ++ rest`
  returns `(n, rest)`, recovering the encoded number *and* the untouched suffix. This is what lets a
  universal machine recover an appended program intact.
* `sdEncode_length_le` — the linear length bound `(sdEncode n).length ≤ 2 * Nat.size n + 2`. In
  fact equality holds (`sdEncode_length_eq`); the linear overhead is the additive invariance
  constant.
-/

namespace Kolmogorov

/-! ### Binary expansion and its inverse -/

/-- Read a bit list (least-significant bit first) back into a natural number. This is a left
inverse of `Nat.bits` (see `fromBits_bits`). -/
def fromBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * fromBits bs

@[simp] theorem fromBits_nil : fromBits [] = 0 := rfl

@[simp] theorem fromBits_cons (b : Bool) (bs : List Bool) :
    fromBits (b :: bs) = b.toNat + 2 * fromBits bs := rfl

/-- `fromBits` inverts mathlib's least-significant-bit-first expansion `Nat.bits`. -/
theorem fromBits_bits (n : ℕ) : fromBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, fromBits_cons, ih, Nat.bit_val]
    omega

/-! ### Doubling each bit -/

/-- Double every bit of a list: `b ↦ [b, b]`. The image avoids the pattern `[false, true]`, which
is therefore free to serve as an end-of-code marker. -/
def double : List Bool → List Bool
  | [] => []
  | b :: bs => b :: b :: double bs

@[simp] theorem double_nil : double [] = [] := rfl

@[simp] theorem double_cons (b : Bool) (bs : List Bool) :
    double (b :: bs) = b :: b :: double bs := rfl

/-- Doubling exactly doubles the length. -/
@[simp] theorem double_length (l : List Bool) : (double l).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons b bs ih => simp [ih]; omega

/-! ### Encoder and decoder -/

/-- Self-delimiting encoding of `n`: double the bits of `n`, then append the terminator
`[false, true]`. -/
def sdEncode (n : ℕ) : List Bool := double (Nat.bits n) ++ [false, true]

/-- Core decoder over doubled bits. Reads two bits at a time:
* `[false, true]` is the terminator — stop and return the bits collected so far together with the
  remaining suffix;
* `[false, false]` / `[true, true]` accumulate the bit `false` / `true`;
* anything else (`[true, false]`, a dangling single bit, or exhaustion) is malformed: `none`. -/
def sdDecodeBits : List Bool → Option (List Bool × List Bool)
  | false :: true  :: rest => some ([], rest)
  | false :: false :: rest => (sdDecodeBits rest).map fun p => (false :: p.1, p.2)
  | true  :: true  :: rest => (sdDecodeBits rest).map fun p => (true :: p.1, p.2)
  | _ => none

/-- Self-delimiting decoding: run `sdDecodeBits` and convert the recovered bits back to a number. -/
def sdDecode (l : List Bool) : Option (ℕ × List Bool) :=
  (sdDecodeBits l).map fun p => (fromBits p.1, p.2)

/-! ### Round-trip (prefix-free) property -/

/-- The decoder consumes exactly one doubled, terminated block and hands back the untouched suffix.
This is the engine of the prefix-free property: it is stated for an *arbitrary* trailing list
`rest`, so an appended program is recovered with its suffix intact. -/
theorem sdDecodeBits_double_append (bs rest : List Bool) :
    sdDecodeBits (double bs ++ [false, true] ++ rest) = some (bs, rest) := by
  induction bs with
  | nil => simp [sdDecodeBits]
  | cons b bs ih =>
    -- `simp only` (no `List.append_assoc`) keeps the append associated as the IH expects.
    cases b <;>
      simp only [double_cons, List.cons_append, sdDecodeBits, ih, Option.map_some]

/-- **Prefix-free round-trip.** Decoding `sdEncode n ++ rest` recovers `n` together with the
untouched suffix `rest`. Hence the code is prefix-free: an appended program `p` (here represented by
its index `n`) can always be split off cleanly. -/
theorem sdDecode_sdEncode (n : ℕ) (rest : List Bool) :
    sdDecode (sdEncode n ++ rest) = some (n, rest) := by
  unfold sdDecode sdEncode
  rw [sdDecodeBits_double_append]
  simp [fromBits_bits]

/-! ### Length bound (the additive invariance constant) -/

/-- The encoding length is exactly `2 * Nat.size n + 2`: two output bits per binary digit of `n`
(there are `Nat.size n` of them) plus the two-bit terminator. -/
theorem sdEncode_length_eq (n : ℕ) : (sdEncode n).length = 2 * Nat.size n + 2 := by
  rw [sdEncode, List.length_append, double_length, Nat.size_eq_bits_len]
  rfl

/-- **Linear length bound.** The self-delimiting encoding adds only linear overhead, which is what
makes the Kolmogorov invariance theorem *additive*: the universal-machine constant is bounded by a
fixed linear function of the program index. -/
theorem sdEncode_length_le (n : ℕ) : (sdEncode n).length ≤ 2 * Nat.size n + 2 :=
  (sdEncode_length_eq n).le

/-! ### Sanity checks (no axioms incurred) -/

example : sdEncode 5 = [true, true, false, false, true, true, false, true] := by decide
example : sdDecode (sdEncode 5) = some (5, []) := by decide
example : sdDecode (sdEncode 5 ++ [true, false]) = some (5, [true, false]) := by decide
example : sdEncode 0 = [false, true] := by decide

/-! ## Rung B — computability of the codec (risk-check)

The Kolmogorov invariance theorem needs the universal machine to *decode* its input, so the codec
must be `Computable`. This section probes whether mathlib's `Primrec`/`Computable` framework handles
our bit codec smoothly.

**Verdict (recorded honestly).** The framework's combinator library is rich for *flat* list and
arithmetic operations — single-step folds (`Primrec.list_foldr`), single-step structural recursion
(`Primrec.list_rec`), `nat_add`/`nat_mul`, and `Primrec.dom_bool` (every `Bool → α` is primitive
recursive). Those cover `fromBits` and `double` with no friction (proved below).

Two pieces of the *concrete* Rung-A codec resist, exactly as anticipated:

* **`Nat.bits` (encoder side).** It is defined by `Nat.binaryRec`, i.e. well-founded recursion on
  `n / 2`. There is no off-the-shelf `Primrec Nat.bits`, and the framework has no native
  division-recursion combinator. It *can* be done by recasting to a fuel-bounded iteration
  (`Primrec.nat_iterate` over `n` steps of `(acc, m) ↦ (acc ++ [bodd m], m / 2)`), but that demands
  a separate correctness induction proving the fuel iteration equals `Nat.bits` — a genuine slog.

* **`sdDecodeBits` (decoder side) — the real wall.** Its recursion consumes **two** bits per step
  and recurses on the tail-of-tail, *and* it returns the untouched suffix. `Primrec.list_rec` is a
  **single-step** structural recursion (it exposes `(head, tail, IH-on-tail)`), so the two-element
  stride does not fit it. Recasting to a one-element state machine that also threads the suffix,
  plus the correctness proof, is harder than the `Nat.bits` slog.

**Resolution.** We take the blessed fallback: a *unary* self-delimiting codec whose decode is
single-step structural recursion — which `Primrec.list_rec` handles directly. It is `Computable` in
both directions with a clean round-trip. Its length overhead is `n + 1` (crude, unary) rather than
`2 * Nat.size n + 2` (logarithmic), but invariance needs the codec to be **prefix-free + computable,
not short**, so the fallback yields a fully valid additive invariance constant.
-/

section Computability
open Primrec

/-! ### Smooth: `fromBits` and `double` are primitive recursive

Both are right folds, so `Primrec.list_foldr` applies directly. -/

/-- `fromBits` is primitive recursive: it is the right fold `b, s ↦ b.toNat + 2 * s`. -/
theorem primrec_fromBits : Primrec fromBits := by
  have hstep : Primrec₂ fun (_ : List Bool) (p : Bool × ℕ) => p.1.toNat + 2 * p.2 :=
    Primrec₂.mk (nat_add.comp ((dom_bool Bool.toNat).comp (fst.comp snd))
      (nat_mul.comp (const 2) (snd.comp snd)))
  have h : fromBits = fun l => l.foldr (fun b s => b.toNat + 2 * s) 0 := by
    funext l; induction l with
    | nil => rfl
    | cons b bs ih => simp only [fromBits, List.foldr_cons, ih]
  rw [h]; exact list_foldr Primrec.id (const 0) hstep

theorem computable_fromBits : Computable fromBits := primrec_fromBits.to_comp

/-- `double` is primitive recursive: it is the right fold `b, s ↦ b :: b :: s`. -/
theorem primrec_double : Primrec double := by
  have hstep : Primrec₂ fun (_ : List Bool) (p : Bool × List Bool) => p.1 :: p.1 :: p.2 :=
    Primrec₂.mk (list_cons.comp (fst.comp snd) (list_cons.comp (fst.comp snd) (snd.comp snd)))
  have h : double = fun l => l.foldr (fun b s => b :: b :: s) [] := by
    funext l; induction l with
    | nil => rfl
    | cons b bs ih => simp only [double, List.foldr_cons, ih]
  rw [h]; exact list_foldr Primrec.id (const []) hstep

theorem computable_double : Computable double := primrec_double.to_comp

/-! ### Encoder gateway: `Nat.bits`, hence `sdEncode`, is computable (via a fuel recast)

`Nat.bits` is defined by `Nat.binaryRec` (well-founded recursion on `n / 2`); the framework has no
native division-recursion combinator. We recast it as a fuel-bounded iteration of one halving step
and prove the iteration equals `Nat.bits` once the fuel reaches `Nat.size n` (and `Nat.size n ≤ n`).
This is the "slog" the risk-check flagged — completed here to confirm the encoder side is reachable;
only the decoder (`sdDecodeBits`) remains a genuine wall. -/

/-- One halving step: emit the low bit and halve; identity once the number is `0`. -/
private def bitsStep (p : List Bool × ℕ) : List Bool × ℕ :=
  Nat.casesOn p.2 p fun _ => (p.1 ++ [Nat.bodd p.2], Nat.div2 p.2)

private theorem bitsStep_zero (acc : List Bool) : bitsStep (acc, 0) = (acc, 0) := rfl

private theorem bitsStep_pos (acc : List Bool) (m : ℕ) (hm : m ≠ 0) :
    bitsStep (acc, m) = (acc ++ [Nat.bodd m], Nat.div2 m) := by
  cases m with
  | zero => exact absurd rfl hm
  | succ k => rfl

/-- For `m ≠ 0`, the size drops by exactly one under halving. -/
private theorem size_div2 (m : ℕ) (hm : m ≠ 0) :
    Nat.size m = Nat.size (Nat.div2 m) + 1 := by
  have h' : Nat.bit (Nat.bodd m) (Nat.div2 m) ≠ 0 := by rwa [Nat.bit_bodd_div2]
  have hb := Nat.size_bit h'
  rwa [Nat.bit_bodd_div2] at hb

/-- For `m ≠ 0`, the binary expansion peels off its low bit. -/
private theorem bits_div2 (m : ℕ) (hm : m ≠ 0) :
    Nat.bodd m :: Nat.bits (Nat.div2 m) = Nat.bits m := by
  have hne : Nat.bits m ≠ [] := by
    have hpos : 0 < (Nat.bits m).length := by
      rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hm)
    exact List.ne_nil_of_length_pos hpos
  rw [Nat.bodd_eq_bits_head, Nat.div2_bits_eq_tail]
  cases hb : Nat.bits m with
  | nil => exact absurd hb hne
  | cons b bs => simp

/-- After `k ≥ Nat.size m` halving steps, the iteration has emitted all of `Nat.bits m`. -/
private theorem bitsStep_iter : ∀ (k : ℕ) (acc : List Bool) (m : ℕ), Nat.size m ≤ k →
    bitsStep^[k] (acc, m) = (acc ++ Nat.bits m, 0)
  | 0, acc, m, h => by
    have hm : m = 0 := Nat.size_eq_zero.mp (Nat.le_zero.mp h)
    subst hm; simp [Nat.zero_bits]
  | k + 1, acc, m, h => by
    rcases eq_or_ne m 0 with hm | hm
    · subst hm
      rw [Function.iterate_succ_apply, bitsStep_zero, bitsStep_iter k acc 0 (by simp)]
    · rw [Function.iterate_succ_apply, bitsStep_pos acc m hm]
      have hk : Nat.size (Nat.div2 m) ≤ k := by have := size_div2 m hm; omega
      rw [bitsStep_iter k (acc ++ [Nat.bodd m]) (Nat.div2 m) hk, List.append_assoc,
        List.singleton_append, bits_div2 m hm]

/-- `Nat.bits` is computable: binary expansion recast as `Nat.size n`-bounded (hence `n`-bounded)
iteration of `bitsStep`, which `Primrec.nat_iterate` handles. -/
theorem primrec_natBits : Primrec Nat.bits := by
  have hstep : Primrec bitsStep := by
    have hh : Primrec₂ fun (p : List Bool × ℕ) (_ : ℕ) =>
        (p.1 ++ [Nat.bodd p.2], Nat.div2 p.2) :=
      Primrec₂.mk (pair
        (list_append.comp (fst.comp fst)
          (list_cons.comp (nat_bodd.comp (snd.comp fst)) (const [])))
        (nat_div2.comp (snd.comp fst)))
    exact (nat_casesOn snd Primrec.id hh).of_eq fun p => by
      cases h : p.2 <;> simp [bitsStep, h]
  have hiter : Primrec fun n : ℕ => bitsStep^[n] ([], n) :=
    nat_iterate Primrec.id (pair (const []) Primrec.id) (Primrec₂.mk (hstep.comp snd))
  have hsize : ∀ n : ℕ, Nat.size n ≤ n := fun n => Nat.size_le.mpr (Nat.lt_two_pow_self)
  have h : Nat.bits = fun n => (bitsStep^[n] ([], n)).1 := by
    funext n; rw [bitsStep_iter n [] n (hsize n)]; simp
  rw [h]; exact fst.comp hiter

theorem computable_natBits : Computable Nat.bits := primrec_natBits.to_comp

/-- The concrete Rung-A encoder is computable (encoder side of the codec). -/
theorem primrec_sdEncode : Primrec sdEncode :=
  (list_append.comp (primrec_double.comp primrec_natBits) (const [false, true])).of_eq fun _ => rfl

theorem computable_sdEncode : Computable sdEncode := primrec_sdEncode.to_comp

/-! ### The wall (recorded, not mechanised): `Computable sdDecode` for the concrete decoder

`Computable sdDecode` is **not** provided here (it was a `sorry` in the Rung-B probe and has been
excised so the library is sorry-free). The obstruction: `sdDecodeBits` recurses with **stride two**
(`b₁ :: b₂ :: rest ↦ … rest`), but the only list structural-recursion combinator,
`Primrec.list_rec`, is **single-step** — in case `b :: tl` it exposes `(b, tl, IH = decode tl)`, and
`decode tl` is the parse *starting one bit too late* (misaligned), so it carries no usable
information about the even-position pairing. A `List.foldl` state-machine recast (state
`Option ((bits × Option Bool) ⊕ (bits × suffix))`) *is* primitive recursive, but its equivalence to
`sdDecodeBits` is a multi-case induction over every reachable state — deferred.

This rung sidesteps the wall by building the universal machine over the **unary** codec
(`uEncode`/`uDecode`), whose decode is single-step and fully `Computable` (`computable_uDecode`). -/

/-! ### Fallback codec — unary length prefix (computable both ways)

`uEncode n = trueⁿ ++ [false]`, the unary representation of `n` terminated by a single `false`.
A program `p` is appended: `uEncode n ++ p`. Decoding counts the leading `true`s and drops the
`false` separator — a **single-step** structural recursion, which `Primrec.list_rec` handles. -/

/-- Unary self-delimiting encoding of `n`. Prefix-free: the first `false` marks the boundary. -/
def uEncode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Unary decode: count leading `true`s, then return the count and the tail after the `false`
separator. This is a one-element-at-a-time recursion (contrast `sdDecodeBits`'s two-bit stride). -/
def uDecode : List Bool → ℕ × List Bool
  | [] => (0, [])
  | true :: l => ((uDecode l).1 + 1, (uDecode l).2)
  | false :: l => (0, l)

/-- **Prefix-free round-trip for the fallback codec** (Rung A, redone for `uEncode`/`uDecode`):
decoding `uEncode n ++ p` recovers `n` and the untouched program `p`. -/
theorem uDecode_uEncode (n : ℕ) (p : List Bool) : uDecode (uEncode n ++ p) = (n, p) := by
  induction n with
  | zero => simp [uEncode, uDecode]
  | succ n ih =>
    have hstep : uEncode (n + 1) ++ p = true :: (uEncode n ++ p) := by
      simp [uEncode, List.replicate_succ]
    rw [hstep, uDecode, ih]

/-- `n ↦ List.replicate n true` is primitive recursive (iterate `cons true` `n` times). -/
theorem primrec_replicate_true : Primrec fun n : ℕ => List.replicate n true := by
  have hstep : Primrec₂ fun (_ : ℕ) (l : List Bool) => true :: l :=
    Primrec₂.mk (list_cons.comp (const true) snd)
  have h : (fun n : ℕ => List.replicate n true) = fun n => (fun l => true :: l)^[n] [] := by
    funext n; induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, Function.iterate_succ_apply', ← ih]
  rw [h]; exact nat_iterate Primrec.id (const []) hstep

theorem primrec_uEncode : Primrec uEncode :=
  (list_append.comp primrec_replicate_true (const [false])).of_eq fun _ => rfl

theorem computable_uEncode : Computable uEncode := primrec_uEncode.to_comp

/-- `uDecode` is primitive recursive via single-step structural recursion on the list. -/
theorem primrec_uDecode : Primrec uDecode := by
  have hstep : Primrec₂ fun (_ : List Bool) (p : Bool × List Bool × (ℕ × List Bool)) =>
      (bif p.1 then (p.2.2.1 + 1, p.2.2.2) else (0, p.2.1) : ℕ × List Bool) := by
    refine Primrec₂.mk (cond (fst.comp snd) ?_ ?_)
    · exact pair (succ.comp (fst.comp (snd.comp (snd.comp snd))))
        (snd.comp (snd.comp (snd.comp snd)))
    · exact pair (const 0) (fst.comp (snd.comp snd))
  have h : uDecode = fun l => l.recOn (0, [])
      (fun b l IH => (bif b then (IH.1 + 1, IH.2) else (0, l) : ℕ × List Bool)) := by
    funext l; induction l with
    | nil => rfl
    | cons b l ih => cases b <;> simp [uDecode, ih]
  rw [h]; exact list_rec Primrec.id (const (0, [])) hstep

theorem computable_uDecode : Computable uDecode := primrec_uDecode.to_comp

end Computability

/-! ## Rung C1 — the universal machine and its computability

Using the unary codec of Rung B, we build a universal partial-recursive function over bit strings.
A natural number `e` indexes a partial-recursive program via mathlib's universal interpreter
`Nat.Partrec.Code.eval`: `e` decodes to a `Code` (`Denumerable.ofNat Code e`), which `eval` runs on
the natural-number encoding of the input bit string.

* `U_partrec` — `U` is partial recursive. This transports mathlib's universality lemma
  `Nat.Partrec.Code.eval_part : Partrec₂ eval` through the computable decoders
  (`computable_uDecode`, `Computable.ofNat`, `Computable.encode`).
* `phiE_complete` — every partial-recursive `φ : List Bool →. ℕ` is `phiE e` for some index `e`.
  This is `Nat.Partrec.Code.exists_code` (every partrec function is some code's `eval`) transported
  back along `Encodable`/`Denumerable`. Together with `U_partrec` this makes `phiE` a universal
  enumeration of the partial-recursive functions on bit strings — the substrate for invariance. -/

section Universal
open Computable
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval eval_part exists_code)

/-- The `e`-th partial-recursive function on bit strings: decode `e` to a `Code`, run mathlib's
universal interpreter `eval` on the encoded input. -/
noncomputable def phiE (e : ℕ) : List Bool →. ℕ :=
  fun p => eval (Denumerable.ofNat Code e) (Encodable.encode p)

/-- The universal machine on bit strings: decode the input via the unary codec to an index/program
pair `(e, p)`, then run `phiE e p`. (The unary `uDecode` is total, so the only divergence is the
interpreter's.) -/
noncomputable def U : List Bool →. ℕ :=
  fun w => phiE (uDecode w).1 (uDecode w).2

/-- **The universal machine is partial recursive.** Mathlib's `eval` is a universal partial
recursive function (`eval_part : Partrec₂ eval`); composing it with the computable decoders makes
`U` partrec. -/
theorem U_partrec : Partrec U := by
  have hcode : Computable fun w : List Bool => Denumerable.ofNat Code (uDecode w).1 :=
    (Computable.ofNat Code).comp (fst.comp computable_uDecode)
  have harg : Computable fun w : List Bool => Encodable.encode (uDecode w).2 :=
    Computable.encode.comp (snd.comp computable_uDecode)
  exact (eval_part.comp hcode harg).of_eq fun w => rfl

/-- **Completeness of the enumeration.** Every partial-recursive `φ : List Bool →. ℕ` equals
`phiE e` for some index `e`. Proof: `φ` transports to a `Nat.Partrec` function, which by
`exists_code` is `eval c` for some code `c`; take `e = Encodable.encode c`. -/
theorem phiE_complete (φ : List Bool →. ℕ) (hφ : Partrec φ) :
    ∃ e, ∀ p, φ p = phiE e p := by
  -- `Partrec φ` is by definition `Nat.Partrec` of the encode/decode-transported function.
  obtain ⟨c, hc⟩ := exists_code.mp hφ
  refine ⟨Encodable.encode c, fun p => ?_⟩
  have key : eval c (Encodable.encode p) = φ p := by
    rw [hc]; simp [Encodable.encodek, Part.map_id' Encodable.encode_nat]
  calc φ p = eval c (Encodable.encode p) := key.symm
    _ = phiE (Encodable.encode c) p := by simp only [phiE, Denumerable.ofNat_encode]

end Universal

/-! ## Rung C2 — Kolmogorov complexity and the invariance theorem

`C φ x` is the length of the shortest program making machine `φ` output `x` (an extended natural,
`⊤` when `x` is not describable). The **invariance theorem** says the universal machine `U` of
Rung C1 is *optimal*: for any partial-recursive `φ` there is an additive constant `c` (here `e + 1`,
the length `uEncode e` of the program index) with `C U x ≤ C φ x + c` for all `x`. The constant
depends on `φ` but not on `x` — this is exactly what makes Kolmogorov complexity well-defined up to
`O(1)`, and it is the additive constant that Rung A's linear length bound was designed to keep
finite. -/

section Invariance

/-- **Kolmogorov complexity** of `x` relative to machine `φ`: the infimum program length over all
programs `p` with `x ∈ φ p`, valued in `ℕ∞` (`⊤` if no program describes `x`, as `sInf ∅ = ⊤`). -/
noncomputable def C (φ : List Bool →. ℕ) (x : ℕ) : ℕ∞ :=
  sInf ((fun p => (p.length : ℕ∞)) '' {p : List Bool | x ∈ φ p})

/-- **Invariance / optimality of the universal machine.** For every partial-recursive `φ` there is
a constant `c` with `C U x ≤ C φ x + c` for all `x`: the universal machine is optimal up to an
additive constant. The constant is `e + 1`, where `e` is the `phiE`-index of `φ` and `e + 1` is the
length of its unary self-delimiting prefix `uEncode e`. -/
theorem invariance (φ : List Bool →. ℕ) (hφ : Partrec φ) :
    ∃ c : ℕ, ∀ x, C U x ≤ C φ x + (c : ℕ∞) := by
  obtain ⟨e, he⟩ := phiE_complete φ hφ
  refine ⟨e + 1, fun x => ?_⟩
  -- KEY LEMMA: any program `p` for `x` under `φ` yields a program `uEncode e ++ p` for `x` under
  -- `U` of length `p.length + (e + 1)`, bounding `C U x`.
  have KEY : ∀ p, x ∈ φ p → C U x ≤ ((p.length + (e + 1) : ℕ) : ℕ∞) := by
    intro p hp
    have hx : x ∈ phiE e p := by rw [← he p]; exact hp
    have hU : x ∈ U (uEncode e ++ p) := by
      change x ∈ phiE (uDecode (uEncode e ++ p)).1 (uDecode (uEncode e ++ p)).2
      rw [uDecode_uEncode]; exact hx
    have hmem : (uEncode e ++ p) ∈ {q : List Bool | x ∈ U q} := hU
    have hle : C U x ≤ ((uEncode e ++ p).length : ℕ∞) :=
      sInf_le (Set.mem_image_of_mem (fun q => (q.length : ℕ∞)) hmem)
    have hlen : (uEncode e ++ p).length = p.length + (e + 1) := by
      simp only [uEncode, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      omega
    rwa [hlen] at hle
  -- FINISH: pure `ℕ∞` inf-plumbing. `tsub_le_iff_right` strips the `+ c`, `le_sInf` reduces to the
  -- per-program KEY bound, and the undescribable case (`C φ x = sInf ∅ = ⊤`) is handled for free.
  rw [← tsub_le_iff_right]
  unfold C
  apply le_sInf
  rintro b ⟨p, hp, rfl⟩
  rw [tsub_le_iff_right, ← Nat.cast_add]
  exact KEY p hp

end Invariance

/-! ## Rung D1 — Kolmogorov complexity is unbounded (the counting lemma)

There are only finitely many programs shorter than `n`, and a deterministic machine assigns each at
most one output, so only finitely many `x` have `C U x < n`. Since `ℕ` is infinite, some `x` escapes
that finite set, giving `n ≤ C U x`. This counting lemma is what Berry-style incompressibility
arguments rest on: complexity cannot be bounded by any constant. -/

theorem C_unbounded (n : ℕ) : ∃ x : ℕ, (n : ℕ∞) ≤ C U x := by
  -- Finitely many programs of length `< n` (`Bool` is a `Fintype`).
  have hP : {p : List Bool | p.length < n}.Finite := List.finite_length_lt Bool n
  -- Their outputs form a finite union of subsingletons (each `U p : Part ℕ` is single-valued).
  have hTfin : (⋃ p ∈ {p : List Bool | p.length < n}, {x | x ∈ U p}).Finite :=
    hP.biUnion fun p _ => (Part.subsingleton (U p)).finite
  -- Every `x` with `C U x < n` is such an output.
  have hsub : {x : ℕ | C U x < (n : ℕ∞)} ⊆
      ⋃ p ∈ {p : List Bool | p.length < n}, {x | x ∈ U p} := by
    intro x hx
    simp only [Set.mem_setOf_eq, C] at hx
    obtain ⟨b, hb, hbn⟩ := sInf_lt_iff.mp hx
    obtain ⟨q, hq, rfl⟩ := hb
    exact Set.mem_biUnion (Nat.cast_lt.mp hbn) hq
  have hSfin : {x : ℕ | C U x < (n : ℕ∞)}.Finite := hTfin.subset hsub
  -- A finite subset of the infinite `ℕ` omits some `x`; there `¬ (C U x < n)`, i.e. `n ≤ C U x`.
  obtain ⟨x, hx⟩ := hSfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx
  exact ⟨x, not_lt.mp hx⟩

/-! ## Rung D2 — Kolmogorov complexity is uncomputable (Berry's paradox)

If `C U` were computable (via some `g : ℕ → ℕ`), we could *name a high-complexity string with a
short program*, contradicting unboundedness. Concretely: a computable selector `h n` picks some `x`
with `C U x ≥ n` (STEP 1–2); but `h` itself is a `U`-program, so `h n` has a `U`-program of length
only `(e+1) + Nat.size n` (STEP 3); combined, `n ≤ (e+1) + Nat.size n` for all `n`, which fails at
`n = 2^(c+2)` since `Nat.size` is logarithmic while the left side is exponential (STEP 4). This is
the second pillar of AIT: complexity is well-defined but not effectively computable. -/

section Berry
open Computable

theorem K_uncomputable :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∀ x, (g x : ℕ∞) = C U x := by
  rintro ⟨g, hg_comp, hg⟩
  -- STEP 1: by `C_unbounded`, every `n` has some `x` with `n ≤ g x`; the least such is computable.
  have hex : ∀ n : ℕ, ∃ x, n ≤ g x := by
    intro n
    obtain ⟨x, hx⟩ := C_unbounded n
    rw [← hg x] at hx
    exact ⟨x, Nat.cast_le.mp hx⟩
  have hP_comp : ComputablePred (fun p : ℕ × ℕ => p.1 ≤ g p.2) :=
    ((Primrec.nat_le.decide.to_comp).comp Computable.fst
      (hg_comp.comp Computable.snd)).computablePred
  let h : ℕ → ℕ := fun n => Nat.find (hex n)
  have h_comp : Computable h := Computable.find hP_comp hex
  -- STEP 2: by construction `n ≤ g (h n)`, hence `n ≤ C U (h n)`.
  have h_spec : ∀ n, n ≤ g (h n) := fun n => Nat.find_spec (hex n)
  -- STEP 3: `h ∘ fromBits` is a computable program; let `e` be its universal index.
  let ψ : List Bool → ℕ := fun p => h (fromBits p)
  have hψ_comp : Computable ψ := h_comp.comp computable_fromBits
  obtain ⟨e, he⟩ := phiE_complete (ψ : List Bool →. ℕ) hψ_comp.partrec
  -- STEP 2+3 combined: `h n` is output by the short program `uEncode e ++ Nat.bits n`.
  have bound : ∀ n, n ≤ (e + 1) + Nat.size n := by
    intro n
    have hUeq : U (uEncode e ++ Nat.bits n) = phiE e (Nat.bits n) := by
      change phiE (uDecode (uEncode e ++ Nat.bits n)).1 (uDecode (uEncode e ++ Nat.bits n)).2
        = phiE e (Nat.bits n)
      rw [uDecode_uEncode]
    have hmemU : h n ∈ U (uEncode e ++ Nat.bits n) := by
      rw [hUeq, ← he (Nat.bits n), PFun.coe_val, Part.mem_some_iff]
      change h n = h (fromBits (Nat.bits n))
      rw [fromBits_bits]
    have hmem : (uEncode e ++ Nat.bits n) ∈ {q : List Bool | h n ∈ U q} := hmemU
    have hle : C U (h n) ≤ ((uEncode e ++ Nat.bits n).length : ℕ∞) :=
      sInf_le (Set.mem_image_of_mem (fun q => (q.length : ℕ∞)) hmem)
    have hlen : (uEncode e ++ Nat.bits n).length = (e + 1) + Nat.size n := by
      simp only [uEncode, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, Nat.size_eq_bits_len]
    rw [hlen, ← hg (h n)] at hle
    exact le_trans (h_spec n) (Nat.cast_le.mp hle)
  -- STEP 4: exponential beats logarithmic. At `n = 2^(c+2)` the bound is impossible.
  set c := e + 1 with hc
  have hb := bound (2 ^ (c + 2))
  rw [Nat.size_pow] at hb
  have h2c : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hpow : 2 ^ (c + 2) = 4 * 2 ^ c := by rw [pow_add]; ring
  omega

end Berry

end Kolmogorov

-- Rung A
#print axioms Kolmogorov.sdDecode_sdEncode
#print axioms Kolmogorov.sdEncode_length_le

-- Rung B: smooth pieces and the encoder gateway (axiom-clean)
#print axioms Kolmogorov.computable_fromBits
#print axioms Kolmogorov.computable_double
#print axioms Kolmogorov.computable_natBits
#print axioms Kolmogorov.computable_sdEncode

-- Rung B: fallback unary codec (axiom-clean, the working computable prefix-free codec)
#print axioms Kolmogorov.uDecode_uEncode
#print axioms Kolmogorov.computable_uEncode
#print axioms Kolmogorov.computable_uDecode

-- Rung C1: universal machine
#print axioms Kolmogorov.U_partrec
#print axioms Kolmogorov.phiE_complete

-- Rung C2: the invariance theorem
#print axioms Kolmogorov.invariance

-- Rung D1: complexity is unbounded
#print axioms Kolmogorov.C_unbounded

-- Rung D2: complexity is uncomputable (Berry)
#print axioms Kolmogorov.K_uncomputable
