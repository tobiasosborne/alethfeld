/-
  AlethfeldLean.Quantum.PauliDiag

  Pauli diagonal lemmas: properties of diagonal Pauli matrices and strings.

  This module re-exports all submodules for backward compatibility.
  For new code, prefer importing specific submodules.

  Submodules:
  - PauliDiag.Single: Single-qubit diagonal properties (σI, σZ diagonal; σX, σY zero diagonal)
  - PauliDiag.Kronecker: Kronecker product diagonal properties and pauliString diagonal lemmas
  - PauliDiag.Trace: Trace lemmas for products with diagonal matrices
  - PauliDiag.Orthogonality: Pauli product traces and orthogonality relations
  - PauliDiag.General: General Kronecker diagonal lemmas and structural lemmas
-/
import AlethfeldLean.Quantum.PauliDiag.Single
import AlethfeldLean.Quantum.PauliDiag.Kronecker
import AlethfeldLean.Quantum.PauliDiag.Trace
import AlethfeldLean.Quantum.PauliDiag.Orthogonality
import AlethfeldLean.Quantum.PauliDiag.General

namespace Alethfeld.Quantum.PauliDiag

-- Re-export all submodules
open Alethfeld.Quantum.PauliDiag.Single in
export Alethfeld.Quantum.PauliDiag.Single (
  σI_off_diag σZ_off_diag σX_diag_zero σY_diag_zero σ_XY_diag_zero
  σI_diag σZ_diag_0 σZ_diag_1 σZ_diag_entry σI_diag_entry σ_IZ_diag_entry σ_diag_off_diag
)

open Alethfeld.Quantum.PauliDiag.Kronecker in
export Alethfeld.Quantum.PauliDiag.Kronecker (
  kronecker_diag_entry kronecker_diag_off_diag
  pauliString_diag submatrix_diag_entry pauliString_diag_entry pauliString_diag_zero_of_XY
)

open Alethfeld.Quantum.PauliDiag.Trace in
export Alethfeld.Quantum.PauliDiag.Trace (
  trace_mul_diagonal trace_diagonal_mul trace_diagonal_mul_zero_diag
  trace_conjTranspose_mul_diagonal_zero_diag trace_mul_diagonal_zero_diag
  trace_product_zero_of_zero_diag_and_diag
  trace_submatrix_equiv trace_kronecker_prod
  trace_kronecker_zero_of_first trace_kronecker_zero_of_second
  trace_σX_zero trace_σY_zero
)

open Alethfeld.Quantum.PauliDiag.Orthogonality in
export Alethfeld.Quantum.PauliDiag.Orthogonality (
  σI_mul_σI σX_mul_σX σY_mul_σY σZ_mul_σZ
  σX_mul_σZ_diag σZ_mul_σX_diag σY_mul_σZ_diag σZ_mul_σY_diag
  trace_σZ_mul_σX trace_σZ_mul_σY trace_σZ_mul_σI trace_σI_mul_σZ
  trace_σX_mul_σZ trace_σY_mul_σZ trace_σ_mul_σ_ne trace_σ_mul_σ
)

open Alethfeld.Quantum.PauliDiag.General in
export Alethfeld.Quantum.PauliDiag.General (
  kronecker_diag_zero_of_first_diag_zero kronecker_diag_zero_of_second_diag_zero
  kronecker_diag_zero_of_first_zero kronecker_diag_zero_of_second_zero
  submatrix_diag_entry' submatrix_zero_diag_of_kronecker_zero_diag
  trace_pauliString_transformedObs_zero_of_Z spectralDist_zero_of_Z_component
)

end Alethfeld.Quantum.PauliDiag
