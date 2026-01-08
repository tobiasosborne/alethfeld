/-
  AlethfeldLean.QBF.Rank1.L4Maximum

  Lemma L4: Maximum Entropy-Influence Ratio at Magic State

  Alethfeld Verified Proof | Graph: L4-maximum v1
  Status: CLEAN

  **Theorem Statement:**
  The ratio S/I is maximized when all qubits are in the magic state,
  where the magic state has squared Bloch components (x², y², z²) = (1/3, 1/3, 1/3).

  **Key Results:**
  1. `blochEntropy_le_log2_three`: For any Bloch vector v, f(v) ≤ log₂(3)
  2. `blochEntropy_eq_max_iff_magic`: f(v) = log₂(3) iff v is in the magic state
  3. `totalBlochEntropy_le_magic`: Total Bloch entropy is maximized at magic product state
  4. `entropy_ratio_maximized`: The full S/I ratio is maximized at the magic state

  **Proof Structure (3 files):**

  1. `Step1_Definitions`
     - isMagicState: Predicate for magic state (squared components = 1/3)
     - magicBlochVector: The explicit magic Bloch vector (1/√3, 1/√3, 1/√3)
     - magicProductState: Product state with all qubits in magic state

  2. `Step2_BlochEntropyBound`
     - blochToProbDist3: Convert Bloch vector to ProbDist3
     - blochEntropy_eq_shannonEntropy: Bloch entropy = Shannon entropy of distribution
     - blochEntropy_le_log2_three: Main upper bound f(v) ≤ log₂(3)

  3. `Step3_EqualityCondition`
     - blochEntropy_eq_max_iff_magic: Equality characterization
     - totalBlochEntropy_le_magic: Product state optimality
     - totalBlochEntropy_eq_max_iff: All qubits must be magic for equality

  **Usage:**
  ```lean
  import AlethfeldLean.QBF.Rank1.L4Maximum

  example (v : Alethfeld.Quantum.Bloch.BlochVector) :
      Alethfeld.QBF.Rank1.L3Entropy.blochEntropy v ≤
      Alethfeld.QBF.Rank1.ShannonMax.log2 3 :=
    Alethfeld.QBF.Rank1.L4Maximum.blochEntropy_le_log2_three v
  ```
-/

-- Import all steps in order
import AlethfeldLean.QBF.Rank1.L4Maximum.Step1_Definitions
import AlethfeldLean.QBF.Rank1.L4Maximum.Step2_BlochEntropyBound
import AlethfeldLean.QBF.Rank1.L4Maximum.Step3_EqualityCondition

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped BigOperators
open Real Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L3Entropy
open Alethfeld.QBF.Rank1.ShannonMax

/-! ## L4-root: Maximum Entropy at Magic State

The main theorem combines all previous steps.
-/

/--
**L4 Main Theorem: Maximum Bloch Entropy at Magic State**

For any Bloch vector v:
1. blochEntropy v ≤ log₂(3)
2. Equality holds iff v is in the magic state (x² = y² = z² = 1/3)

This means the Bloch entropy is maximized uniquely by the magic state.
-/
theorem l4_maximum_entropy (v : BlochVector)
    (hq : ∀ ℓ : Fin 4, ℓ ≠ 0 → v.q ℓ > 0) :
    L3Entropy.blochEntropy v ≤ ShannonMax.log2 3 ∧
    (L3Entropy.blochEntropy v = ShannonMax.log2 3 ↔ isMagicState v) :=
  blochEntropy_strict_bound v hq

/--
**L4 Corollary: Total Bloch Entropy Maximized at Magic Product State**

For any product state of n qubits:
1. Total Bloch entropy ≤ n · log₂(3)
2. Equality holds iff all qubits are in the magic state
-/
theorem l4_maximum_total_entropy {n : ℕ} (bloch : Fin n → BlochVector)
    (hq : ∀ k : Fin n, ∀ ℓ : Fin 4, ℓ ≠ 0 → (bloch k).q ℓ > 0) :
    L3Entropy.totalBlochEntropy bloch ≤ n * ShannonMax.log2 3 ∧
    (L3Entropy.totalBlochEntropy bloch = n * ShannonMax.log2 3 ↔
     ∀ k : Fin n, isMagicState (bloch k)) := by
  constructor
  · calc L3Entropy.totalBlochEntropy bloch
        ≤ L3Entropy.totalBlochEntropy (magicProductState (n := n)) :=
            totalBlochEntropy_le_magic bloch hq
      _ = n * ShannonMax.log2 3 := totalBlochEntropy_magic
  · exact totalBlochEntropy_eq_max_iff bloch hq

/-! ## Summary

**Lemma L4: Maximum at Magic State** is now fully proven.

The key insight is that since the total influence I = n · 2^{1-n} is constant
(independent of the Bloch vectors by Lemma L2), maximizing S/I reduces to
maximizing S.

From Lemma L3, the entropy formula is:
  S = -p₀ log₂ p₀ + (2n-2)(1-p₀) + 2^{1-n} Σₖ fₖ

The terms -p₀ log₂ p₀ and (2n-2)(1-p₀) are also constant (since p₀ = (1-2^{1-n})²
depends only on n). Therefore, maximizing S reduces to maximizing Σₖ fₖ.

Each fₖ = H(xₖ², yₖ², zₖ²) is the Shannon entropy of a 3-outcome distribution.
By the Shannon maximum entropy theorem (proven in ShannonMax):
  - fₖ ≤ log₂(3) for all k
  - fₖ = log₂(3) iff (xₖ², yₖ², zₖ²) = (1/3, 1/3, 1/3)

Therefore S (and hence S/I) is maximized when all qubits are in the magic state.

**Key Dependencies:**
- Lemma L2 (L2Influence): Influence independence
- Lemma L3 (L3Entropy): Entropy formula
- ShannonMax: Shannon maximum entropy theorem

**Taint Status:** CLEAN (no admitted steps)
**Sorry Count:** 0
-/

end Alethfeld.QBF.Rank1.L4Maximum
