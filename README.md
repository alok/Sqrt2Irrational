# Convoluted Proofs

A collection of absurdly sophisticated proofs of simple mathematical facts in Lean 4.

**[View the interactive documentation](https://alok.github.io/Sqrt2Irrational/)**

## Overview

This project demonstrates how simple mathematical facts can be proven using unnecessarily complex mathematical machinery. It's inspired by the MathOverflow question ["Awfully sophisticated proof for simple facts"](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts) and Asaf Karagila's proof of the irrationality of √2 using ultrafilters.

## Theorems Proved

### Irrationality of √2

Two proofs are provided:

#### 1. Direct Proof (`irrational_sqrt_2`)

Uses Dirichlet's theorem and quadratic reciprocity without explicit ultraproduct machinery.

**Approach**:
- Uses Dirichlet's theorem on primes in arithmetic progressions to get infinitely many primes ≡ 3 (mod 8)
- Applies quadratic reciprocity to show 2 is not a square mod p for these primes
- For any rational √2 = a/b, picks a prime p > max(a,b) with p ≡ 3 (mod 8)
- Shows a² = 2b² implies 2 is a square mod p — contradiction!

#### 2. Ultraproduct Proof (`irrational_sqrt_2_ultraproduct`)

The full model-theoretic proof using first-order language structures.

**Approach**:

- Constructs the index set `PrimesMod3_8` of primes ≡ 3 (mod 8)
- Builds a non-principal ultrafilter using `hyperfilter`
- Defines the ultraproduct ∏_U (ZMod p) over these primes
- Shows x² = 2 has no solution in the ultraproduct (by Łoś's theorem)
- If √2 = a/b, then (a · b⁻¹)² = 2 in ZMod p for large p — contradiction!

**Reference**: Based on [Asaf Karagila's proof](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational) (see comments)

## Building the Project

1. Install Lean 4 following the [official instructions](https://leanprover.github.io/lean4/doc/setup.html)
2. Clone this repository
3. Run `lake exe cache get` to fetch Mathlib cache
4. Run `lake build` in the project directory

## Mathematical Background

The project showcases how advanced mathematical concepts can be (mis)used to prove elementary results:

- **Model Theory**: Ultraproducts, Łoś's theorem, first-order ring structures
- **Number Theory**: Dirichlet's theorem, quadratic reciprocity
- **Filter Theory**: Ultrafilters, hyperfilter, cofinite filter

## Axioms

The proofs use only standard mathematical axioms:

- `propext` — Propositional extensionality
- `Classical.choice` — Axiom of choice (required for ultrafilters)
- `Quot.sound` — Quotient soundness

No custom axioms are introduced.

## ✅ Verified Independence

The proofs are **genuinely independent** of Mathlib's existing `irrational_sqrt_two` theorem. This was verified by commenting out Mathlib's proof and rebuilding successfully.

### How to Reproduce

```bash
# 1. Comment out these theorems in .lake/packages/mathlib/Mathlib/NumberTheory/Real/Irrational.lean:
#    - Line 132: Nat.Prime.irrational_sqrt
#    - Line 136: irrational_sqrt_two  
#    - Line 511: exists_irrational_btwn

# 2. Wrap each theorem in block comments: /- ... -/

# 3. Rebuild
lake build Sqrt2Irrational

# 4. Build succeeds → proof is independent!
```

**Result:** Build completed successfully (3326 jobs). Both `irrational_sqrt_2` and `irrational_sqrt_2_ultraproduct` compile without any dependency on Mathlib's standard proof.

### Key Difference

| Mathlib's Proof | Our Proof |
|-----------------|-----------|
| `Nat.Prime.not_isSquare` (parity) | `ZMod.exists_sq_eq_two_iff` (quadratic reciprocity) |
| Ancient Greece (~500 BCE) | 19th century (Dirichlet 1837) |

## Contributing

Feel free to add your own convoluted proofs! The more sophisticated the machinery for proving simple facts, the better.

## License

Apache 2.0
