# Convoluted Proofs

A collection of absurdly sophisticated proofs of simple mathematical facts in Lean 4.

## Overview

This project demonstrates how simple mathematical facts can be proven using unnecessarily complex mathematical machinery. It's inspired by the MathOverflow question ["Awfully sophisticated proof for simple facts"](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts) and Asaf Karagila's proof of the irrationality of √2 using ultrafilters.

## Theorems Proved

### 1. Irrationality of √2 (`irrational_sqrt_2`)
**Statement**: √2 is irrational.

**Convoluted approach**: 
- Uses Dirichlet's theorem on primes in arithmetic progressions to get infinitely many primes ≡ 3 (mod 8)
- Constructs a non-principal ultrafilter on this infinite set using the hyperfilter
- Applies quadratic reciprocity to show 2 is not a square mod p for these primes
- Derives a contradiction by showing if √2 = a/b, then 2 would be a square mod p

**Reference**: Based on [Asaf Karagila's proof](https://math.stackexchange.com/questions/1311228/what-is-the-most-unusual-proof-you-know-that-sqrt2-is-irrational) (see comments)

### 2. Existence of Discontinuous Functions (`discontinuous_function_exists`)
**Statement**: There exists a function from ℝ to ℝ that is not continuous.

**Convoluted approach**:
- Proof by contradiction assuming all functions are continuous
- Uses cardinal arithmetic: if all functions were continuous, then #(ℝ → ℝ) ≤ #(ℚ → ℝ)
- Applies density of ℚ in ℝ and that continuous functions are determined by values on dense subsets
- Shows this implies 𝔠^𝔠 ≤ 𝔠^ℵ₀ = 𝔠
- Derives contradiction using Cantor's theorem: 𝔠 < 𝔠^𝔠

**Reference**: [MathOverflow discussion](https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts)

## Building the Project

1. Install Lean 4 following the [official instructions](https://leanprover.github.io/lean4/doc/setup.html)
2. Clone this repository
3. Run `lake build` in the project directory

## Mathematical Background

The project showcases how advanced mathematical concepts can be (mis)used to prove elementary results:

- **Model Theory**: Ultraproducts
- **Number Theory**: Dirichlet's theorem, quadratic reciprocity
- **Set Theory**: Cardinal arithmetic, Cantor's theorem

## Contributing

Feel free to add your own convoluted proofs! The more sophisticated the machinery for proving simple facts, the better.

## License

Apache 2.0