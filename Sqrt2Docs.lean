/-
  Sqrt2Docs.lean - Verso documentation for the convoluted sqrt(2) proof
-/

import VersoManual
import Sqrt2Irrational

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Convoluted Proof: sqrt(2) is Irrational" =>

%%%
authors := ["Based on Asaf Karagila's ultrafilter proof"]
%%%

A sophisticated proof using **Dirichlet's theorem**, **quadratic reciprocity**,
and **ultrafilters** in Lean 4 with Mathlib.

This is a formalization of an "awfully sophisticated proof for a simple fact."

# The Key Idea

Instead of the usual proof by contradiction using parity, we use heavy machinery:

1. **Dirichlet's Theorem:** There are infinitely many primes p ≡ 3 (mod 8)
2. **Quadratic Reciprocity:** For such primes, 2 is NOT a quadratic residue mod p
3. **Ultraproducts:** Construct an ultraproduct of fields Z/pZ over these primes
4. **Los's Theorem:** x² = 2 has no solution in the ultraproduct

If sqrt(2) = a/b were rational, then for any sufficiently large prime p (not dividing b),
we'd have (a/b)² ≡ 2 (mod p), contradicting that 2 is not a square mod p!

# Proof Comparison

How does this proof compare to the standard one taught in schools?

## Standard Proof (Parity)

```
Assume sqrt(2) = a/b in lowest terms
-> a² = 2b²
-> a² is even
-> a is even (a = 2k)
-> 4k² = 2b², so b² = 2k²
-> b is even
-> Both even contradicts "lowest terms"
-> Contradiction!
```

**Core fact:** If n² is even, then n is even

## This Proof (Dirichlet + QR)

```
Assume sqrt(2) = a/b
-> a² = 2b²
-> Pick prime p ≡ 3 (mod 8), p > max(a,b)
-> p does not divide b, so b invertible mod p
-> (a/b)² ≡ 2 (mod p)
-> 2 is a square mod p
-> But QR says 2 is NOT a square mod p
-> Contradiction!
```

**Core fact:** Legendre symbol (2|p) = -1 for p ≡ 3 (mod 8)

# Core Components

## Primes ≡ 3 (mod 8) are Infinite

Using Dirichlet's theorem on primes in arithmetic progressions, we prove
{name}`primes_three_mod_eight_infinite`:

The set {name}`primes_three_mod_eight` is infinite by {name}`Nat.infinite_setOf_prime_and_eq_mod`.

## 2 is Not a Square mod p

For primes p ≡ 3 (mod 8), the Legendre symbol (2|p) = -1. This is proved in
{name}`two_not_square_mod_prime_three_mod_eight` using {name}`ZMod.exists_sq_eq_two_iff`.

## The Main Theorem

{name}`irrational_sqrt_2` proves sqrt(2) is irrational using the direct approach.

{name}`irrational_sqrt_2_ultraproduct` proves the same using the full ultraproduct machinery.

# Ultraproduct Machinery

The ultraproduct version adds ~130 more lines to package "for almost all p" into a single algebraic object.

## The Index Set

{name}`PrimesMod3_8` is the subtype of primes ≡ 3 (mod 8).

## The Ultrafilter

{name}`ultrafilterOnPrimes` is a non-principal ultrafilter extending the cofinite filter.
This requires the Axiom of Choice via {name}`hyperfilter`.

## The Ultraproduct

{name}`Ultraproduct` is the filter product ∏_U (ZMod p) over primes p ≡ 3 (mod 8).

## Key Lemma

{name}`ultraproduct_no_sqrt_two` shows that no element of the ultraproduct squares to 2.

# Axioms Used

All proofs use standard mathematical axioms (verified by Lean):

- `propext` — Propositional extensionality
- `Classical.choice` — Axiom of choice
- `Quot.sound` — Quotient soundness

No custom axioms were introduced.

# Source Code

Full source: [github.com/alok/Sqrt2Irrational](https://github.com/alok/Sqrt2Irrational)
