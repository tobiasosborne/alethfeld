# Pickup Prompt: Sorry Elimination for AlethfeldLean L1-Fourier

## Context

You are continuing work on the **AlethfeldLean** Lean 4 formalization project. The previous agent set up the Lake project structure with Mathlib v4.26.0 and created a compilable skeleton for Lemma L1 (Fourier Coefficient Formula for Rank-1 QBFs).

**The project builds successfully** but contains **9 sorries** that need to be replaced with complete proofs.

## Project Location

```
/home/tobiasosborne/Projects/alethfeld/lean/
```

## Build Command

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
lake build
```

Mathlib cache is already downloaded. Builds take ~10 seconds.

## Mathematical Background

This formalizes **Lemma L1** from quantum Boolean function analysis:

**Theorem (Fourier Coefficient Formula):** For a rank-1 QBF $U = I - 2|\psi\rangle\langle\psi|$ where $|\psi\rangle = \bigotimes_{k=1}^n |\phi_k\rangle$ is a product state:

$$\hat{U}(\alpha) = \delta_{\alpha,0} - 2^{1-n} \prod_{k=1}^n r_k^{(\alpha_k)}$$

where $\alpha \in \{0,1,2,3\}^n$ is a multi-index, $\delta_{\alpha,0}$ is the Kronecker delta, and $r_k^{(\ell)}$ are the extended Bloch components:
- $r_k^{(0)} = 1$
- $r_k^{(1)} = x_k$ (Bloch x-component)
- $r_k^{(2)} = y_k$ (Bloch y-component)
- $r_k^{(3)} = z_k$ (Bloch z-component)

---

## Files and Sorry Locations

### 1. `AlethfeldLean/Quantum/Pauli.lean` (3 sorries)

#### Sorry 1: `pauliString` definition (line ~64)
```lean
noncomputable def pauliString {n : ℕ} (α : MultiIndex n) : QubitMat n :=
  sorry -- Requires careful definition using Kronecker product over Fin n
```

**What's needed:** Define the n-fold tensor product $\sigma^\alpha = \sigma^{\alpha_1} \otimes \sigma^{\alpha_2} \otimes \cdots \otimes \sigma^{\alpha_n}$.

**Approach:**
- Use `Matrix.kronecker` (notation `⊗ₖ`) from `Mathlib.LinearAlgebra.Matrix.Kronecker`
- Need to handle the index type change: `Fin 2 × Fin 2 → Fin 4` etc.
- Consider using `Fintype.piFinset` or a recursive definition
- Key insight: The result type `QubitMat n = Matrix (Fin (2^n)) (Fin (2^n)) ℂ` requires index reindexing

**Mathlib references:**
- `Matrix.kronecker_apply`
- `Matrix.trace_kronecker` (may exist in Mathlib)
- `finProdFinEquiv` for index bijections

#### Sorry 2: `trace_kronecker` theorem (line ~68)
```lean
theorem trace_kronecker (A B : Mat2) :
    Matrix.trace (A ⊗ₖ B) = Matrix.trace A * Matrix.trace B := by
  simp only [Matrix.trace, kroneckerMap, Matrix.of_apply]
  sorry -- Standard Kronecker trace property
```

**What's needed:** Prove $\text{Tr}(A \otimes B) = \text{Tr}(A) \cdot \text{Tr}(B)$.

**Approach:**
- Expand trace as sum over diagonal
- Use `kroneckerMap` definition: $(A \otimes B)_{(i,j),(k,l)} = A_{ik} \cdot B_{jl}$
- Diagonal of Kronecker product: $(A \otimes B)_{(i,j),(i,j)} = A_{ii} \cdot B_{jj}$
- Sum factors: $\sum_{i,j} A_{ii} B_{jj} = (\sum_i A_{ii})(\sum_j B_{jj})$

**Mathlib references:**
- Check if `Matrix.trace_kronecker` already exists in Mathlib
- `Finset.sum_product` for factoring sums
- `Fin.sum_univ_two` for 2×2 case

#### Sorry 3: `trace_pauliString` theorem (line ~75)
```lean
theorem trace_pauliString {n : ℕ} (α : MultiIndex n) :
    Matrix.trace (pauliString α) = if isZeroIndex α then (2 : ℂ)^n else 0 := by
  sorry -- Follows from trace_σ and trace_kronecker by induction
```

**What's needed:** Prove by induction on n that the trace of a Pauli string is $2^n$ if all indices are 0, else 0.

**Approach:**
- Induction on `n`
- Base case: `n = 0` is trivial (empty product = identity of dimension 1)
- Inductive step: Use `trace_kronecker` and `trace_σ`
- Key lemma: If any $\alpha_k \neq 0$, then $\text{Tr}(\sigma^{\alpha_k}) = 0$, so the product vanishes

---

### 2. `AlethfeldLean/Quantum/Bloch.lean` (4 sorries)

#### Sorry 4: `expectation_σI` (line ~80)
```lean
theorem expectation_σI (θ φ : ℝ) :
    expectation (blochState θ φ) σI = 1 := by
  sorry -- Direct computation
```

**What's needed:** Show $\langle\phi|I|\phi\rangle = 1$ for normalized state.

**Approach:**
- Expand `expectation`, `innerProduct`, `matVecMul`, `blochState`, `σI`
- Use `Fin.sum_univ_two` to evaluate the sum
- Result: $|\cos(\theta/2)|^2 + |\exp(i\varphi)\sin(\theta/2)|^2 = \cos^2 + \sin^2 = 1$

**Mathlib references:**
- `Complex.abs_exp` for $|e^{i\varphi}| = 1$
- `Real.cos_sq_add_sin_sq`

#### Sorry 5: `expectation_σX` (line ~85)
```lean
theorem expectation_σX (θ φ : ℝ) :
    expectation (blochState θ φ) σX = (blochVectorOfAngles θ φ).x := by
  sorry -- Computation using 2cos(θ/2)sin(θ/2)cos(φ) = sin(θ)cos(φ)
```

**What's needed:** Show $\langle\phi|\sigma_x|\phi\rangle = \sin\theta\cos\varphi$.

**Approach:**
- $\sigma_x|\phi\rangle = \cos(\theta/2)|1\rangle + e^{i\varphi}\sin(\theta/2)|0\rangle$
- Inner product: $e^{-i\varphi}\sin(\theta/2)\cos(\theta/2) + e^{i\varphi}\cos(\theta/2)\sin(\theta/2)$
- Simplify: $2\cos(\theta/2)\sin(\theta/2)\cos\varphi = \sin\theta\cos\varphi$

**Mathlib references:**
- `Real.sin_two_mul`: $\sin(2x) = 2\sin(x)\cos(x)$
- `Complex.add_conj`: $z + \bar{z} = 2\text{Re}(z)$

#### Sorry 6: `expectation_σY` (line ~90)
```lean
theorem expectation_σY (θ φ : ℝ) :
    expectation (blochState θ φ) σY = (blochVectorOfAngles θ φ).y := by
  sorry -- Analogous computation
```

**What's needed:** Show $\langle\phi|\sigma_y|\phi\rangle = \sin\theta\sin\varphi$.

**Approach:** Analogous to σX but with imaginary unit giving $\sin\varphi$ instead of $\cos\varphi$.

#### Sorry 7: `expectation_σZ` (line ~95)
```lean
theorem expectation_σZ (θ φ : ℝ) :
    expectation (blochState θ φ) σZ = (blochVectorOfAngles θ φ).z := by
  sorry -- cos²(θ/2) - sin²(θ/2) = cos(θ)
```

**What's needed:** Show $\langle\phi|\sigma_z|\phi\rangle = \cos\theta$.

**Approach:**
- $\sigma_z|0\rangle = |0\rangle$, $\sigma_z|1\rangle = -|1\rangle$
- Result: $\cos^2(\theta/2) - \sin^2(\theta/2) = \cos\theta$

**Mathlib references:**
- `Real.cos_sq_sub_sin_sq`: $\cos^2(x) - \sin^2(x) = \cos(2x)$

---

### 3. `AlethfeldLean/QBF/Rank1/L1Fourier.lean` (2 sorries)

#### Sorry 8: `fourierCoeff_rank1_expand` (line ~47)
```lean
theorem fourierCoeff_rank1_expand (α : MultiIndex n) (traceOfPauliProj : ℂ) :
    (2 : ℂ)^(-(n : ℤ)) * (Matrix.trace (pauliString α) - 2 * traceOfPauliProj)
    = (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α)
      - (2 : ℂ)^(1 - n : ℤ) * traceOfPauliProj := by
  sorry
```

**What's needed:** Algebraic manipulation showing $2^{-n} \cdot 2 = 2^{1-n}$.

**Approach:**
- Distribute: $2^{-n}(A - 2B) = 2^{-n}A - 2^{-n} \cdot 2 \cdot B$
- Use `zpow_add₀`: $2^{-n} \cdot 2^1 = 2^{-n+1} = 2^{1-n}$

**Mathlib references:**
- `zpow_add₀` for $a^m \cdot a^n = a^{m+n}$
- `zpow_one`
- May need `Int.add_comm` or `omega` for exponent arithmetic

#### Sorry 9: `term1_simplify` (line ~61)
```lean
theorem term1_simplify (α : MultiIndex n) :
    (2 : ℂ)^(-(n : ℤ)) * Matrix.trace (pauliString α) = multiIndexDelta α := by
  rw [trace_pauliString']
  sorry
```

**What's needed:** Show $2^{-n} \cdot 2^n \cdot \delta = \delta$.

**Approach:**
- After rewriting with `trace_pauliString'`: have $2^{-n} \cdot (2^n \cdot \delta)$
- Reassociate: $(2^{-n} \cdot 2^n) \cdot \delta$
- Use `zpow_add₀`: $2^{-n} \cdot 2^n = 2^0 = 1$

**Mathlib references:**
- `zpow_natCast` to convert `(2 : ℂ)^n` to zpow form
- `zpow_add₀`
- `zpow_zero`

---

## General Tips

### Useful Tactics
- `simp only [...]` with explicit lemma lists for controlled simplification
- `norm_num` for numeric computations
- `ring` / `ring_nf` for polynomial identities
- `field_simp` for clearing denominators
- `push_cast` for moving coercions
- `omega` for integer arithmetic in exponents

### Complex Number Lemmas
- `Complex.ofReal_add`, `Complex.ofReal_mul` for real→complex coercions
- `Complex.exp_mul_I` for $e^{i\theta}$
- `Complex.normSq_exp_ofReal_mul_I` for $|e^{i\theta}|^2 = 1$
- `Complex.conj_exp` for $\overline{e^z}$

### Matrix Lemmas
- `Matrix.trace` is defined as `∑ i, M i i`
- `Matrix.of_apply` for `!![a, b; c, d] i j`
- `Fin.sum_univ_two` to expand sums over `Fin 2`
- `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons` for vector access

### Trigonometry
- `Real.sin_sq_add_cos_sq`
- `Real.cos_sq_add_sin_sq`
- `Real.sin_two_mul`
- `Real.cos_two_mul`
- `Real.cos_sq_sub_sin_sq`

---

## Verification

After eliminating all sorries, the build should complete with no warnings about sorry usage:

```bash
lake build 2>&1 | grep -c "sorry"
# Should output: 0
```

## Priority Order

Recommended order for tackling sorries:

1. **`trace_kronecker`** (Sorry 2) - Foundation for everything else
2. **`pauliString`** (Sorry 1) - Needed for trace theorems
3. **`trace_pauliString`** (Sorry 3) - Uses the above two
4. **`expectation_σI/X/Y/Z`** (Sorries 4-7) - Independent, can be done in parallel
5. **`term1_simplify`** (Sorry 9) - Uses trace_pauliString
6. **`fourierCoeff_rank1_expand`** (Sorry 8) - Pure zpow algebra

---

## Files to Edit

1. `/home/tobiasosborne/Projects/alethfeld/lean/AlethfeldLean/Quantum/Pauli.lean`
2. `/home/tobiasosborne/Projects/alethfeld/lean/AlethfeldLean/Quantum/Bloch.lean`
3. `/home/tobiasosborne/Projects/alethfeld/lean/AlethfeldLean/QBF/Rank1/L1Fourier.lean`

## Reference: Original Semantic Proof

The verified semantic proof is in:
```
/home/tobiasosborne/Projects/alethfeld/examples/qbf-rank1/lemmas/L1/L1-fourier.tex
```

This contains the mathematical argument structure that the Lean formalization mirrors.

---

**Good luck! The heavy lifting of project setup and Mathlib integration is done. Focus on the mathematical content.**
