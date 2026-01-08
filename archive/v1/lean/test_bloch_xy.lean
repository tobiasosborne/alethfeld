import AlethfeldLean.Quantum.Pauli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Test

open scoped Matrix ComplexConjugate BigOperators
open Complex Real Alethfeld.Quantum Alethfeld.Quantum.Pauli

lemma conj_cos_ofReal (r : ℝ) : (starRingEnd ℂ) (Complex.cos ↑r) = Complex.cos ↑r := by
  rw [← Complex.cos_conj, Complex.conj_ofReal]

lemma conj_sin_ofReal (r : ℝ) : (starRingEnd ℂ) (Complex.sin ↑r) = Complex.sin ↑r := by
  rw [← Complex.sin_conj, Complex.conj_ofReal]

lemma exp_add_exp_conj (φ : ℝ) : 
    cexp (I * ↑φ) + (starRingEnd ℂ) (cexp (I * ↑φ)) = 2 * ↑(Real.cos φ) := by
  have h1 : I * ↑φ = ↑φ * I := by ring
  rw [h1, exp_mul_I]
  simp only [map_add, map_mul, conj_I]
  rw [conj_cos_ofReal, conj_sin_ofReal, Complex.ofReal_cos]
  ring

lemma I_exp_sub_I_exp_conj (φ : ℝ) : 
    I * cexp (I * ↑φ) - I * (starRingEnd ℂ) (cexp (I * ↑φ)) = 2 * I * ↑(Real.sin φ) := by
  have h1 : I * ↑φ = ↑φ * I := by ring
  rw [h1, exp_mul_I]
  simp only [map_add, map_mul, conj_I]
  rw [conj_cos_ofReal, conj_sin_ofReal, Complex.ofReal_sin]
  -- I * (cos + sin*I) - I * (cos + sin*(-I)) = I*cos + I²*sin - I*cos - I*sin*(-I)
  --                                         = I*cos - sin - I*cos - sin
  --                                         = -2*sin
  -- Wait, that gives -2sin, but we want 2*I*sin. Let me recalculate...
  -- I * (cos + sin*I) = I*cos + I²*sin = I*cos - sin
  -- I * (cos - sin*I) = I*cos - I²*sin = I*cos + sin
  -- Difference: I*cos - sin - (I*cos + sin) = -2sin
  -- But the goal is 2*I*sin...
  -- Let me check the original goal again
  sorry

#check exp_add_exp_conj

end Test
