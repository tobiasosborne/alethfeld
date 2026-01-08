/-
  Alethfeld Proof: Sum of Divisors of 9! with Units Digit 3
  Graph: graph-div9fac-a1b2c3
  Taint status: clean

  **Theorem**: The sum of all positive divisors of 9! that have units digit 3 equals 66.

  **Note**: The original problem statement claimed the sum was 105, which is incorrect.
  Computational verification shows the only such divisors are {3, 63}, summing to 66.
-/

import Mathlib

-- Computational proofs use native_decide for decidable finite verification
set_option linter.style.nativeDecide false

namespace Alethfeld.NumberTheory

open Nat Finset BigOperators

/-- The units digit of a natural number -/
def unitsDigit (n : ℕ) : ℕ := n % 10

/-- 9! = 362880 -/
theorem factorial_9 : 9! = 362880 := by native_decide

/-- Prime factorization: 9! = 2^7 * 3^4 * 5 * 7 -/
theorem factorial_9_factorization : 9! = 2^7 * 3^4 * 5 * 7 := by native_decide

/-- The divisors of 9! with units digit 3 -/
def divisorsWithUnitsDigit3 : Finset ℕ :=
  (Nat.divisors (9!)).filter (fun d => unitsDigit d = 3)

/-- 3 divides 9! -/
theorem three_divides_factorial_9 : 3 ∣ 9! := by
  simp only [Nat.factorial]
  exact dvd_of_mem_divisors (by native_decide : 3 ∈ Nat.divisors 362880)

/-- 63 divides 9! -/
theorem sixtythree_divides_factorial_9 : 63 ∣ 9! := by
  simp only [Nat.factorial]
  exact dvd_of_mem_divisors (by native_decide : 63 ∈ Nat.divisors 362880)

/-- 3 has units digit 3 -/
theorem three_units_digit : unitsDigit 3 = 3 := by native_decide

/-- 63 has units digit 3 -/
theorem sixtythree_units_digit : unitsDigit 63 = 3 := by native_decide

/-- The set of divisors of 9! with units digit 3 is exactly {3, 63} -/
theorem divisors_units_3_eq : divisorsWithUnitsDigit3 = {3, 63} := by native_decide

/-- **Main Theorem**: Sum of divisors of 9! with units digit 3 equals 66 -/
theorem sum_divisors_units_digit_3 :
    ∑ d ∈ divisorsWithUnitsDigit3, d = 66 := by native_decide

/-- Alternative statement: The sum equals 3 + 63 -/
theorem sum_divisors_explicit : (3 : ℕ) + 63 = 66 := by rfl

/-- Refutation of the original claim: The sum is NOT 105 -/
theorem sum_not_105 : ∑ d ∈ divisorsWithUnitsDigit3, d ≠ 105 := by native_decide

end Alethfeld.NumberTheory
