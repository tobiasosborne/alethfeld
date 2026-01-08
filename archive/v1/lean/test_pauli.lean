import AlethfeldLean.Quantum.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Finprod

namespace Test

open scoped Matrix ComplexConjugate Kronecker BigOperators
open Complex Matrix Finset Alethfeld.Quantum

-- Pauli matrices
def σI : Mat2 := !![1, 0; 0, 1]
def σX : Mat2 := !![0, 1; 1, 0]
def σY : Mat2 := !![0, -Complex.I; Complex.I, 0]
def σZ : Mat2 := !![1, 0; 0, -1]

def σ : Fin 4 → Mat2
  | 0 => σI
  | 1 => σX
  | 2 => σY
  | 3 => σZ

-- The key equivalence: Fin (2^(n+1)) ≃ Fin (2^n) × Fin 2
def finPow2SuccEquiv (n : ℕ) : Fin (2^(n+1)) ≃ Fin (2^n) × Fin 2 :=
  (finCongr (Nat.pow_succ 2 n)).trans finProdFinEquiv.symm

-- Recursive definition of Pauli string
noncomputable def pauliString : {n : ℕ} → MultiIndex n → QubitMat n
  | 0, _ => !![1]
  | n+1, α =>
    let rest := pauliString (fun k => α k.succ)  -- QubitMat n  
    let first := σ (α 0)                           -- Mat2
    let kron := rest ⊗ₖ first  -- Matrix (Fin (2^n) × Fin 2) (Fin (2^n) × Fin 2) ℂ
    kron.submatrix (finPow2SuccEquiv n) (finPow2SuccEquiv n)

#check pauliString

end Test
