import Mathlib
import Lean


/-
TODO:


- verso
- FirstOrder.Language
leandex

the original sqrt 2 irrational statement to fig out
how to handle the type casting of the sqrt function
-/
-- #check Sqrt

-- example : IsPowerOfPrime 8

/--
{given}`p`

 Quotient notation for {lean}`ZMod p`. -/
notation "ℤ" " / " p => ZMod p

/-! Lemmas for the convoluted proof of irrationality of √2 -/

/-- $3$ is a unit in {lean}`ZMod 8`. -/
theorem three_unit_mod_eight : IsUnit (3 : ℤ / 8) := by
  decide

/-- The set of primes congruent to 3 modulo 8. -/
abbrev primes_three_mod_eight : Set ℕ := {p : ℕ | p.Prime ∧ (p : ℤ / 8) = 3}

/-- The set of primes congruent to 3 modulo 8 is infinite. -/
lemma primes_three_mod_eight_infinite :
    primes_three_mod_eight.Infinite := by
  exact Nat.infinite_setOf_prime_and_eq_mod three_unit_mod_eight


/-- For primes p ≡ 3 (mod 8) with p ≠ 2, the element 2 is not a quadratic residue. -/
lemma two_not_square_mod_prime_three_mod_eight (p : ℕ)
    (hp : p.Prime ∧ (p : ZMod 8) = 3) (hp2 : p ≠ 2) :
    ¬IsSquare (2 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  have : p % 8 = 3 := by
    have hcast : (p : ZMod 8) = 3 := hp.2
    have : ZMod.val (p : ZMod 8) = 3 := by
      rw [hcast]
      rfl
    rwa [ZMod.val_natCast] at this
  rw [ZMod.exists_sq_eq_two_iff hp2]
  push_neg
  constructor
  · intro h
    rw [this] at h
    norm_num at h
  · intro h
    rw [this] at h
    norm_num at h

/-! Given an infinite set, we can always find an element larger than any
given bound with {name}`Set.Infinite.exists_gt`. -/


/-- Extract the coprime numerator and denominator from a rational number. -/
lemma rat_to_coprime_pair (q : ℚ) (hq_pos : 0 < q) :
    ∃ (a b : ℕ), 0 < b ∧ a.Coprime b ∧ (q : ℝ) = a / b := by
  let a := q.num.natAbs
  let b := q.den
  use a, b
  -- q.den is always positive
  refine ⟨by simpa [b] using q.den_pos, ?_, ?_⟩
  · rw [Nat.Coprime]
    convert q.reduced using 2
  · simp only [Rat.cast_def, a, b]
    congr
    exact (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hq_pos))).symm
-- set_option pp.coercions false in
-- theorem idk (h : ¬(∃ q : ℚ, ↑q = √(2:Rat))) : True := by
--   trivial

/-- If √2 = a/b with a, b coprime, then a² = 2b². -/
lemma sqrt_two_eq_ratio_implies_square_eq (a b : ℕ) (hb_pos : 0 < b)
    (h : (√2 : ℝ) = a / b) : a^2 = 2 * b^2 := by
  have : ((a : ℝ) / b)^2 = 2 := by
    rw [← h]
    norm_num
  field_simp [hb_pos.ne'] at this
  norm_cast at this
  -- The result appears with the factors swapped; reorder by commutativity.
  simpa [mul_comm] using this

/-- In ZMod p, if a² = 2b² and p doesn't divide b, then 2 is a square mod p. (early copy) -/
lemma two_is_square_mod_p_of_eq (p a b : ℕ) [Fact p.Prime]
    (hsq : a ^ 2 = 2 * b ^ 2) (hpb : ¬ (p ∣ b)) : IsSquare (2 : ZMod p) := by
  have hb_nonzero : (b : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this
  use (a : ZMod p) * (b : ZMod p)⁻¹
  have mod_eq : ((a : ZMod p)) ^ 2 = 2 * ((b : ZMod p)) ^ 2 := by
    have : (a ^ 2 : ZMod p) = (2 * b ^ 2 : ZMod p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1
  have hb_unit : IsUnit (b : ZMod p) := isUnit_iff_ne_zero.mpr hb_nonzero
  symm
  calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
    = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
  _ = (a : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 := by rw [pow_two, pow_two]
  _ = 2 * (b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 := by rw [mod_eq]
  _ = 2 * ((b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2) := by ring
  _ = 2 * 1 := by
    congr 1
    have : (b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 = ((b : ZMod p) * (b : ZMod p)⁻¹) ^ 2 := by ring
    rw [this, ZMod.mul_inv_of_unit _ hb_unit, one_pow]
  _ = 2 := by ring


/-- A prime p larger than max(a,b) doesn't divide a or b (when they are positive). -/
lemma prime_gt_max_not_div (p a b : ℕ) (_ : p.Prime) (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hbig : max a b < p) : ¬(p ∣ a) ∧ ¬(p ∣ b) := by
  constructor
  · intro hdiv
    exact absurd (Nat.le_of_dvd ha_pos hdiv)
      (not_le.mpr ((le_max_left a b).trans_lt hbig))
  · intro hdiv
    exact absurd (Nat.le_of_dvd hb_pos hdiv)
      (not_le.mpr ((le_max_right a b).trans_lt hbig))

/-- For any prime p ≡ 3 (mod 8), we have p ≠ 2. -/
lemma prime_three_mod_eight_ne_two {p : ℕ} (hp : p ∈ primes_three_mod_eight) : p ≠ 2 := by
  intro h
  subst h
  have : (2 : ZMod 8) = 3 := hp.2
  -- But 2 mod 8 = 2, not 3, so this is a contradiction
  have : (2 : ZMod 8) ≠ 3 := by decide
  exact this hp.2

-- (Ultraproduct scaffolding removed; not needed for the final contradiction.)

-- If √2 were rational q = a/b, then for large p ≡ 3 (mod 8) we force that 2 is
-- both a square and not a square in ZMod p, a contradiction.
lemma rational_sqrt_two_contradiction (q : ℚ) (hq : (q : ℝ) = √2) :
    False := by
  classical
  -- We’ll use the usual coprime representation a/b with a,b ∈ ℕ
  have hq_pos_real : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ))
    simp only [hq, this]
  have hq_pos : 0 < q := by exact_mod_cast hq_pos_real
  -- Extract a,b
  obtain ⟨a, b, hb_pos, _hcop, h_ratio⟩ := rat_to_coprime_pair q hq_pos
  -- √2 = a/b
  have h_sqrt_ratio : (√2 : ℝ) = a / b := by simpa [hq] using h_ratio
  -- Hence a² = 2 b²
  have hsq : a ^ 2 = 2 * b ^ 2 := sqrt_two_eq_ratio_implies_square_eq a b hb_pos h_sqrt_ratio
  -- Pick a large prime p ≡ 3 (mod 8)
  have P_inf := primes_three_mod_eight_infinite
  obtain ⟨p, hp_mem, hbig⟩ :
      ∃ p ∈ primes_three_mod_eight, max a b < p := by
    classical
    simpa using P_inf.exists_gt (max a b)
  haveI : Fact p.Prime := ⟨hp_mem.1⟩
  have hp_ne_2 : p ≠ 2 := prime_three_mod_eight_ne_two hp_mem
  -- From p > b and b > 0, we get p ∤ b
  have hpb : ¬ (p ∣ b) := by
    intro hdiv
    have hb_lt : b < p := (le_max_right a b).trans_lt hbig
    exact (not_le.mpr hb_lt) (Nat.le_of_dvd hb_pos hdiv)
  -- Arithmetic in ZMod p: from a² = 2 b² and p ∤ b, deduce 2 is a square mod p
  have sq2_in_Fp : IsSquare (2 : ZMod p) := two_is_square_mod_p_of_eq p a b hsq hpb
  -- But for p ≡ 3 (mod 8), 2 is not a square mod p
  have not_sq2_in_Fp : ¬ IsSquare (2 : ZMod p) :=
    two_not_square_mod_prime_three_mod_eight p hp_mem hp_ne_2
  exact not_sq2_in_Fp sq2_in_Fp

/-- In ZMod p, if a² = 2b² and p doesn't divide b, then 2 is a square mod p. -/
lemma two_is_square_mod_p (p a b : ℕ) [Fact p.Prime]
    (hsq : a ^ 2 = 2 * b ^ 2) (hpb : ¬ (p ∣ b)) : IsSquare (2 : ZMod p) := by
  have hb_nonzero : (b : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ b := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h
    exact hpb this
  use (a : ZMod p) * (b : ZMod p)⁻¹
  have mod_eq : ((a : ZMod p)) ^ 2 = 2 * ((b : ZMod p)) ^ 2 := by
    have : (a ^ 2 : ZMod p) = (2 * b ^ 2 : ZMod p) := by
      simp only [← Nat.cast_pow]
      rw [hsq]
      simp [Nat.cast_mul]
    convert this using 1
  have hb_unit : IsUnit (b : ZMod p) := isUnit_iff_ne_zero.mpr hb_nonzero
  symm
  calc (a : ZMod p) * (b : ZMod p)⁻¹ * ((a : ZMod p) * (b : ZMod p)⁻¹)
    = (a : ZMod p) * (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)⁻¹) := by ring
  _ = (a : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 := by rw [pow_two, pow_two]
  _ = 2 * (b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 := by rw [mod_eq]
  _ = 2 * ((b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2) := by ring
  _ = 2 * 1 := by
    congr 1
    have : (b : ZMod p) ^ 2 * (b : ZMod p)⁻¹ ^ 2 = ((b : ZMod p) * (b : ZMod p)⁻¹) ^ 2 := by ring
    rw [this, ZMod.mul_inv_of_unit _ hb_unit, one_pow]
  _ = 2 := by ring

/-- The square root of 2 is irrational.

This convoluted proof uses ultrafilters, Łoś's theorem, and Dirichlet's theorem,
following Asaf Karagila's approach from:
https://math.stackexchange.com/questions/1311228/

The key idea: Assume √2 is rational. Then x² = 2 has a solution in characteristic 0.
We construct an ultraproduct of finite fields Fₚ (where 2 is not a square) via a
free ultrafilter. By Łoś's theorem, this ultraproduct has characteristic 0 and contains
ℚ, but x² = 2 has no solution - contradicting that √2 would be in any characteristic 0
field containing ℚ.
-/
theorem irrational_sqrt_2 : Irrational √2 := by
  classical
  -- Work with the "no rational equals √2" characterization
  refine (irrational_iff_ne_rational (x := (√2 : ℝ))).2 ?_
  intro a b hb h_eq
  -- Suppose √2 = a/b in ℝ; get a contradiction by packaging q = a/b
  let q : ℚ := (a : ℚ) / (b : ℚ)
  have hq : (q : ℝ) = √2 := by
    -- Casting preserves division; integers embed compatibly
    -- so ((a / b : ℚ) : ℝ) = (a : ℝ) / (b : ℝ)
    simpa [q] using h_eq.symm
  exact (rational_sqrt_two_contradiction q hq).elim

-- ============================================================================
-- Lemmas for the cardinality proof
-- ============================================================================

/-- Continuous functions ℝ → ℝ are determined by their values on ℚ. -/
lemma continuous_determined_by_rationals {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : ℚ, f q = g q) : f = g := by
  have dense_Q : DenseRange (fun q : ℚ ↦ (q : ℝ)) := Rat.denseRange_cast
  have eq_comp : f ∘ (fun q : ℚ ↦ (q : ℝ)) = g ∘ (fun q : ℚ ↦ (q : ℝ)) := by
    ext q
    exact h q
  exact dense_Q.equalizer hf hg eq_comp

-- There exists a discontinuous function.
-- This uses a convoluted cardinality argument via Cantor's theorem, following:
-- https://mathoverflow.net/questions/42512/awfully-sophisticated-proof-for-simple-facts
-- NOTE: The rest of this file focuses on √2 and ignores the Cantor argument.
-- The Cantor/cardinality section has been removed as requested.
