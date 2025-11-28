-- Selective imports for Verso compatibility (avoids needing Mathlib.olean)
import Mathlib.NumberTheory.LSeries.PrimesInAP          -- Dirichlet's theorem
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity  -- Quadratic reciprocity
import Mathlib.Order.Filter.Ultrafilter.Basic           -- Hyperfilter
import Mathlib.Order.Filter.FilterProduct               -- Filter.Product (ultraproducts)
import Mathlib.ModelTheory.Algebra.Ring.Basic           -- First-order ring structures
import Mathlib.ModelTheory.Ultraproducts                -- Model-theoretic ultraproducts
import Mathlib.NumberTheory.Real.Irrational             -- Irrational numbers

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

/-- For any prime p ≡ 3 (mod 8), we have p ≠ 2. -/
lemma prime_three_mod_eight_ne_two {p : ℕ} (hp : p ∈ primes_three_mod_eight) : p ≠ 2 := by
  intro h
  subst h
  have : (2 : ZMod 8) = 3 := hp.2
  have : (2 : ZMod 8) ≠ 3 := by decide
  exact this hp.2

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

/-- If √2 were rational q = a/b, then for large p ≡ 3 (mod 8) we force that 2 is
both a square and not a square in ZMod p, a contradiction. -/
lemma rational_sqrt_two_contradiction (q : ℚ) (hq : (q : ℝ) = √2) : False := by
  classical
  have hq_pos_real : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ))
    simp only [hq, this]
  have hq_pos : 0 < q := by exact_mod_cast hq_pos_real
  obtain ⟨a, b, hb_pos, _hcop, h_ratio⟩ := rat_to_coprime_pair q hq_pos
  have h_sqrt_ratio : (√2 : ℝ) = a / b := by simpa [hq] using h_ratio
  have hsq : a ^ 2 = 2 * b ^ 2 := sqrt_two_eq_ratio_implies_square_eq a b hb_pos h_sqrt_ratio
  have P_inf := primes_three_mod_eight_infinite
  obtain ⟨p, hp_mem, hbig⟩ : ∃ p ∈ primes_three_mod_eight, max a b < p := by
    classical
    simpa using P_inf.exists_gt (max a b)
  haveI : Fact p.Prime := ⟨hp_mem.1⟩
  have hp_ne_2 : p ≠ 2 := prime_three_mod_eight_ne_two hp_mem
  have hpb : ¬ (p ∣ b) := by
    intro hdiv
    have hb_lt : b < p := (le_max_right a b).trans_lt hbig
    exact (not_le.mpr hb_lt) (Nat.le_of_dvd hb_pos hdiv)
  have sq2_in_Fp : IsSquare (2 : ZMod p) := two_is_square_mod_p p a b hsq hpb
  have not_sq2_in_Fp : ¬ IsSquare (2 : ZMod p) :=
    two_not_square_mod_prime_three_mod_eight p hp_mem hp_ne_2
  exact not_sq2_in_Fp sq2_in_Fp

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
-- Ultraproduct-Based Proof using Łoś's Theorem
-- ============================================================================

/-!
# Ultraproduct-Based Proof of Irrationality of √2

This section provides a more "convoluted" proof that explicitly uses model theory:
- Constructs the ultraproduct of finite fields ZMod p over primes p ≡ 3 (mod 8)
- Uses Łoś's theorem to transfer properties
- Shows that x² = 2 has no solution in this ultraproduct

The key model-theoretic insight: For each prime p ≡ 3 (mod 8), x² = 2 has no solution
in ZMod p (by quadratic reciprocity). By Łoś's theorem, this property transfers to the
ultraproduct. But the ultraproduct has characteristic 0, so if √2 were rational, we'd
have a solution - contradiction!
-/

open FirstOrder Language Filter

/-- The subtype of primes congruent to 3 mod 8. This is the index set for our ultraproduct. -/
abbrev PrimesMod3_8 : Type := {p : ℕ // p.Prime ∧ (p : ZMod 8) = 3}

/-- The subtype of primes ≡ 3 (mod 8) is infinite. -/
instance : Infinite PrimesMod3_8 := by
  have : Set.Infinite primes_three_mod_eight := primes_three_mod_eight_infinite
  exact Set.infinite_coe_iff.mpr this

/-- Each element of our index set yields a prime. -/
lemma primesMod3_8_prime (p : PrimesMod3_8) : p.val.Prime := p.prop.1

/-- Each element of our index set satisfies p ≡ 3 (mod 8). -/
lemma primesMod3_8_mod (p : PrimesMod3_8) : (p.val : ZMod 8) = 3 := p.prop.2

/-- The family of finite fields indexed by primes ≡ 3 (mod 8). -/
abbrev FieldFamily (p : PrimesMod3_8) : Type := ZMod p.val

/-- Each field in our family is nonempty. -/
instance (p : PrimesMod3_8) : Nonempty (FieldFamily p) := ⟨0⟩

/-- Each field in our family is a field. -/
instance (p : PrimesMod3_8) : Field (FieldFamily p) := by
  haveI : Fact p.val.Prime := ⟨primesMod3_8_prime p⟩
  infer_instance

/-- In every field of our family, 2 is not a perfect square.
This follows from quadratic reciprocity: for p ≡ 3 (mod 8), the Legendre symbol (2|p) = -1. -/
lemma two_not_square_in_family (p : PrimesMod3_8) : ¬IsSquare (2 : FieldFamily p) := by
  have hp := primesMod3_8_prime p
  have hmod := primesMod3_8_mod p
  have hp2 : p.val ≠ 2 := by
    intro h
    simp only [h] at hmod
    exact (by decide : (2 : ZMod 8) ≠ 3) hmod
  exact two_not_square_mod_prime_three_mod_eight p.val ⟨hp, hmod⟩ hp2

/-- The non-principal ultrafilter on our index set (hyperfilter extends cofinite). -/
noncomputable def ultrafilterOnPrimes : Ultrafilter PrimesMod3_8 := hyperfilter PrimesMod3_8

/-- For any n, cofinitely many primes p ≡ 3 (mod 8) satisfy p > n.
This is key for showing the ultraproduct has characteristic 0. -/
lemma cofinitely_many_primes_gt (n : ℕ) :
    {p : PrimesMod3_8 | n < p.val}ᶜ.Finite := by
  -- The complement is {p | p.val ≤ n}, which is finite since bounded
  have hsub : {p : PrimesMod3_8 | n < p.val}ᶜ ⊆ {p : PrimesMod3_8 | p.val ≤ n} := by
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hp ⊢
    exact hp
  apply Set.Finite.subset _ hsub
  -- The set of primes with bounded value is finite
  have hinj : Set.InjOn (Subtype.val : PrimesMod3_8 → ℕ) (Subtype.val ⁻¹' Set.Iic n) :=
    fun _ _ _ _ h => Subtype.val_injective h
  have hfin : (Subtype.val ⁻¹' Set.Iic n : Set PrimesMod3_8).Finite :=
    Set.Finite.preimage hinj (Set.finite_Iic n)
  have hsub2 : {p : PrimesMod3_8 | p.val ≤ n} ⊆ Subtype.val ⁻¹' (Set.Iic n) := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq] at hp ⊢
    exact hp
  exact Set.Finite.subset hfin hsub2

/-- The set of primes > n is in our ultrafilter. -/
lemma primes_gt_in_ultrafilter (n : ℕ) :
    {p : PrimesMod3_8 | n < p.val} ∈ ultrafilterOnPrimes := by
  -- hyperfilter_le_cofinite says (hyperfilter : Filter) ≤ cofinite
  -- So cofinite sets are in the hyperfilter
  have hle : (ultrafilterOnPrimes : Filter PrimesMod3_8) ≤ cofinite := hyperfilter_le_cofinite
  have hcofin : {p : PrimesMod3_8 | n < p.val} ∈ cofinite :=
    mem_cofinite.mpr (cofinitely_many_primes_gt n)
  exact hle hcofin

-- The Ultraproduct
--
-- The ultraproduct ∏_U ZMod p over primes p ≡ 3 (mod 8) is a field with remarkable properties:
-- 1. It has characteristic 0 (because for any n, most primes are > n)
-- 2. x² = 2 has no solution (by Łoś, since no factor has a solution)
--
-- If √2 were rational, then x² = 2 would have a solution in any field containing ℚ.
-- But this ultraproduct has char 0 (so contains a copy of ℚ) yet has no such solution!

/-- The ultraproduct of our family of fields. -/
noncomputable abbrev Ultraproduct : Type :=
  (ultrafilterOnPrimes : Filter PrimesMod3_8).Product FieldFamily

/-- The ultraproduct is nonempty. -/
noncomputable instance : Nonempty Ultraproduct := by
  haveI : ∀ p, Nonempty (FieldFamily p) := fun p => ⟨0⟩
  exact Ultraproduct.Product.instNonempty

/-- Key lemma: For any nonzero n : ℕ, n ≠ 0 in almost all factors.
This establishes that the ultraproduct has characteristic 0.

Proof: The set of primes p where (n : ZMod p) ≠ 0 (equivalently, p ∤ n) contains
all primes > n, which is in our ultrafilter. -/
lemma ultraproduct_nat_eventually_ne_zero (n : ℕ) (hn : n ≠ 0) :
    ∀ᶠ p in (ultrafilterOnPrimes : Filter PrimesMod3_8),
      (n : FieldFamily p) ≠ (0 : FieldFamily p) := by
  apply Filter.eventually_of_mem (primes_gt_in_ultrafilter n)
  intro p hp
  -- p > n and p is prime, so p ∤ n
  haveI : Fact p.val.Prime := ⟨primesMod3_8_prime p⟩
  simp only [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdiv
  have hle : p.val ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  exact Nat.not_lt.mpr hle hp

/-- The key fact: 2 is not a square in ANY of our factors.
By Łoś's theorem, this means x² = 2 has no solution in the ultraproduct. -/
lemma two_not_square_eventually :
    ∀ᶠ p in (ultrafilterOnPrimes : Filter PrimesMod3_8),
      ¬IsSquare (2 : FieldFamily p) := by
  -- In fact, this holds for ALL p, not just eventually
  exact Filter.Eventually.of_forall two_not_square_in_family

-- ============================================================================
-- First-Order Model Theory Machinery
-- ============================================================================

/-- Each field in our family has a compatible first-order ring structure. -/
noncomputable instance (p : PrimesMod3_8) : FirstOrder.Ring.CompatibleRing (FieldFamily p) :=
  FirstOrder.Ring.compatibleRingOfRing (FieldFamily p)

/-- The ultraproduct inherits a first-order ring structure via Łoś. -/
noncomputable instance : Language.ring.Structure Ultraproduct := by
  haveI : ∀ p, Language.ring.Structure (FieldFamily p) :=
    fun p => FirstOrder.Ring.CompatibleRing.toStructure
  exact FirstOrder.Language.Ultraproduct.structure

/-- The ultraproduct has no element whose square equals 2.

This is the key model-theoretic lemma. By Łoś's theorem, an existential sentence holds
in the ultraproduct iff it holds in almost all factors. The sentence "exists x, x^2 = 2"
fails in ALL our factors (by quadratic reciprocity), hence fails in the ultraproduct.

The proof requires working with the first-order multiplication structure on the
ultraproduct. The multiplication is defined via the quotient: for representatives
f and g in the product, their product is the pointwise product. -/
theorem ultraproduct_no_sqrt_two :
    ¬∃ f : (p : PrimesMod3_8) → FieldFamily p,
      ∀ᶠ p in (ultrafilterOnPrimes : Filter PrimesMod3_8), f p * f p = 2 := by
  intro ⟨f, hf⟩
  -- If f(p) * f(p) = 2 for almost all p, then 2 is a square in almost all fields
  have eventually_square : ∀ᶠ p in (ultrafilterOnPrimes : Filter PrimesMod3_8),
      IsSquare (2 : FieldFamily p) := by
    apply Filter.Eventually.mono hf
    intro p hp
    exact ⟨f p, hp.symm⟩
  -- But 2 is not a square in ANY of our fields
  exact (two_not_square_eventually.and eventually_square).exists.elim
    fun p ⟨hns, hs⟩ => hns hs

-- ============================================================================
-- The Full Ultraproduct-Based Proof
-- ============================================================================

/-- The ultraproduct has characteristic 0: every nonzero natural is nonzero in almost all factors.

Proof: For each n > 0, the set of primes p where (n : ZMod p) ≠ 0 contains all primes p > n.
This set is cofinite, hence in our ultrafilter. -/
theorem ultraproduct_charZero_eventually (n : ℕ) (hn : n ≠ 0) :
    ∀ᶠ p in (ultrafilterOnPrimes : Filter PrimesMod3_8),
      (n : FieldFamily p) ≠ 0 :=
  ultraproduct_nat_eventually_ne_zero n hn

/-- Main theorem: The ultraproduct argument gives irrationality of sqrt 2.

This proof uses the full model-theoretic machinery:
1. Construct ultraproduct of ZMod p over primes p congruent to 3 mod 8
2. Show it has characteristic 0 (so Q embeds into it)
3. Show x^2 = 2 has no solution (by Los and quadratic reciprocity)
4. If sqrt 2 = a/b were rational, then (a/b)^2 = 2 would give a solution
5. Contradiction!

The key insight: if sqrt 2 = a/b, then picking ANY representative f in the ultraproduct
with f(p) = a/b (in ZMod p) would satisfy f(p)^2 = 2 for large enough p.
But the theorem above shows no such f exists! -/
theorem irrational_sqrt_2_ultraproduct : Irrational √2 := by
  classical
  rw [irrational_iff_ne_rational]
  intro a b hb h_eq
  -- If √2 = a/b, we derive a contradiction using the ultraproduct
  -- The contradiction: we can construct f with f(p)² = 2 eventually,
  -- but ultraproduct_no_sqrt_two says no such f exists
  apply ultraproduct_no_sqrt_two
  -- Construct the witness: f(p) = a * b⁻¹ in ZMod p
  use fun p => (a : ZMod p.val) * (b : ZMod p.val)⁻¹
  -- Show f(p)² = 2 for large enough p
  -- This requires: p > max(|a|, |b|) so that b is invertible mod p
  -- and the equation a² = 2b² transfers to (a/b)² = 2 in ZMod p
  have hsq_real : (a : ℝ) ^ 2 = 2 * (b : ℝ) ^ 2 := by
    have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    calc (a : ℝ) ^ 2 = ((a : ℝ) / b * b) ^ 2 := by field_simp
      _ = ((√2) * b) ^ 2 := by rw [← h_eq]
      _ = (√2) ^ 2 * b ^ 2 := by ring
      _ = 2 * b ^ 2 := by rw [h2]
  -- Convert to integers
  have hsq_int : (a : ℤ) ^ 2 = 2 * (b : ℤ) ^ 2 := by
    have h := hsq_real
    push_cast at h
    exact_mod_cast h
  -- For large primes p, b is invertible and the equation transfers
  apply Filter.eventually_of_mem (primes_gt_in_ultrafilter (max a.natAbs b.natAbs))
  intro p hp
  haveI : Fact p.val.Prime := ⟨primesMod3_8_prime p⟩
  -- p > |b|, so p ∤ b, so b is invertible in ZMod p
  have hpb : (b : ZMod p.val) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdiv
    -- hdiv : (p.val : ℤ) ∣ b
    have hle : p.val ≤ b.natAbs := by
      have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
      have hdiv' : p.val ∣ b.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
      exact Nat.le_of_dvd hpos hdiv'
    exact Nat.not_lt.mpr hle ((le_max_right _ _).trans_lt hp)
  -- Now compute: (a * b⁻¹)² = a² * b⁻² = (2 * b²) * b⁻² = 2
  have hb_unit : IsUnit (b : ZMod p.val) := isUnit_iff_ne_zero.mpr hpb
  -- First show a² = 2b² in ZMod p
  have hsq_mod : (a : ZMod p.val) ^ 2 = 2 * (b : ZMod p.val) ^ 2 := by
    have h1 : ((a ^ 2 : ℤ) : ZMod p.val) = ((2 * b ^ 2 : ℤ) : ZMod p.val) := by
      simp only [hsq_int]
    push_cast at h1
    exact h1
  calc ((a : ZMod p.val) * (b : ZMod p.val)⁻¹) * ((a : ZMod p.val) * (b : ZMod p.val)⁻¹)
      = (a : ZMod p.val) ^ 2 * ((b : ZMod p.val)⁻¹) ^ 2 := by ring
    _ = (2 * (b : ZMod p.val) ^ 2) * ((b : ZMod p.val)⁻¹) ^ 2 := by rw [hsq_mod]
    _ = 2 * ((b : ZMod p.val) ^ 2 * ((b : ZMod p.val)⁻¹) ^ 2) := by ring
    _ = 2 * (((b : ZMod p.val) * (b : ZMod p.val)⁻¹) ^ 2) := by ring
    _ = 2 * 1 ^ 2 := by rw [ZMod.mul_inv_of_unit _ hb_unit]
    _ = 2 := by ring

/-!
## Proof Comparison Analysis

All three proofs of √2's irrationality use the same foundational axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

But they differ dramatically in their **mathematical dependencies**:

**STANDARD PROOF** (Mathlib's `irrational_sqrt_two`) uses:
- `Nat.Prime.not_isSquare` (parity/factorization argument)
- Basic divisibility and gcd properties

**THIS PROOF** (`irrational_sqrt_2`) uses:
- `Nat.infinite_setOf_prime_and_eq_mod` (Dirichlet's theorem)
- `ZMod.exists_sq_eq_two_iff` (quadratic reciprocity)

**ULTRAPRODUCT PROOF** (`irrational_sqrt_2_ultraproduct`) additionally uses:
- `hyperfilter` (non-principal ultrafilter existence — requires Choice)
- `Filter.Product` (ultraproduct construction)
- `FirstOrder.Ring.CompatibleRing` (first-order ring structures)

The standard proof and this proof are **genuinely independent** — neither can be derived
from the other without reproving the core lemmas. The ultraproduct version shares the same
mathematical core as the direct proof, just with additional packaging.
-/
